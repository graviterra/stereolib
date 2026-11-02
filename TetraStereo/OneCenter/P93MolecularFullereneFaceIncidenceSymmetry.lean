import TetraStereo.OneCenter.P93MolecularFullereneFlagExtension
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Face-incidence invariance under fullerene orientation reversal

The number of pentagons incident with a cage atom is a purely combinatorial invariant of the
oriented fullerene face map.  This module proves that every orientation-reversing carrier
permutation preserves that number.  The proof constructs the induced permutation of the finite
set of face carriers; it does not enumerate any concrete cage.
-/

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

private abbrev MolecularFullereneFaceCarrier
    (input : MolecularFullereneConfigurationInput) :=
  { face : Finset ℕ // face ∈ (input.faces.map List.toFinset).toFinset }

/-- Number of distinct pentagonal face carriers incident with one atom. -/
def molecularFullerenePentagonIncidence
    (input : MolecularFullereneConfigurationInput) (atom : ℕ) : ℕ :=
  Fintype.card { face : MolecularFullereneFaceCarrier input //
    face.1.card = 5 ∧ atom ∈ face.1 }

private theorem molecularFullereneFaceCarrier_subset
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (face : MolecularFullereneFaceCarrier input) :
    face.1 ⊆ input.carrier := by
  have present : face.1 ∈ input.faces.map List.toFinset := by
    simpa only [List.mem_toFinset] using face.2
  rcases List.mem_map.mp present with ⟨source, sourceMember, sourceCarrier⟩
  rw [← sourceCarrier]
  exact (oriented.1.facesValid source sourceMember).2.1

private theorem mappedMolecularFullereneFaceCarrier_mem
    {input : MolecularFullereneConfigurationInput}
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry)
    (face : MolecularFullereneFaceCarrier input) :
    Finset.image (mapMolecularFullereneCarrierAtom input symmetry) face.1 ∈
      (input.faces.map List.toFinset).toFinset := by
  have present : face.1 ∈ input.faces.map List.toFinset := by
    simpa only [List.mem_toFinset] using face.2
  rcases List.mem_map.mp present with ⟨source, sourceMember, sourceCarrier⟩
  rcases reversing source sourceMember with ⟨target, targetMember, rotated⟩
  simp only [List.mem_toFinset, List.mem_map]
  refine ⟨target, targetMember, ?_⟩
  have carrierEq :
      (mapMolecularFullereneFace input symmetry source).reverse.toFinset =
        target.toFinset := by
    ext atom
    simpa only [List.mem_toFinset] using (rotated.mem_iff (a := atom))
  rw [← sourceCarrier]
  rw [← carrierEq]
  ext atom
  simp only [List.mem_toFinset, List.mem_reverse, mapMolecularFullereneFace,
    List.mem_map, Finset.mem_image]

private noncomputable def mapMolecularFullereneFaceCarrier
    {input : MolecularFullereneConfigurationInput}
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry)
    (face : MolecularFullereneFaceCarrier input) :
    MolecularFullereneFaceCarrier input :=
  ⟨Finset.image (mapMolecularFullereneCarrierAtom input symmetry) face.1,
    mappedMolecularFullereneFaceCarrier_mem symmetry reversing face⟩

private theorem mapMolecularFullereneFaceCarrier_injective
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry) :
    Function.Injective (mapMolecularFullereneFaceCarrier symmetry reversing) := by
  intro left right equal
  apply Subtype.ext
  apply Finset.ext
  intro atom
  constructor
  · intro atomLeft
    have mappedMember :
        mapMolecularFullereneCarrierAtom input symmetry atom ∈
          (mapMolecularFullereneFaceCarrier symmetry reversing left).1 := by
      exact Finset.mem_image.mpr ⟨atom, atomLeft, rfl⟩
    rw [equal] at mappedMember
    rcases Finset.mem_image.mp mappedMember with ⟨other, otherRight, mappedEqual⟩
    have atomCarrier := molecularFullereneFaceCarrier_subset oriented left atomLeft
    have otherCarrier := molecularFullereneFaceCarrier_subset oriented right otherRight
    have atomEq : atom = other :=
      mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
        atomCarrier otherCarrier mappedEqual.symm
    simpa [atomEq] using otherRight
  · intro atomRight
    have mappedMember :
        mapMolecularFullereneCarrierAtom input symmetry atom ∈
          (mapMolecularFullereneFaceCarrier symmetry reversing right).1 := by
      exact Finset.mem_image.mpr ⟨atom, atomRight, rfl⟩
    rw [← equal] at mappedMember
    rcases Finset.mem_image.mp mappedMember with ⟨other, otherLeft, mappedEqual⟩
    have atomCarrier := molecularFullereneFaceCarrier_subset oriented right atomRight
    have otherCarrier := molecularFullereneFaceCarrier_subset oriented left otherLeft
    have atomEq : atom = other :=
      mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
        atomCarrier otherCarrier mappedEqual.symm
    simpa [atomEq] using otherLeft

private theorem mapMolecularFullereneFaceCarrier_card
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry)
    (face : MolecularFullereneFaceCarrier input) :
    (mapMolecularFullereneFaceCarrier symmetry reversing face).1.card = face.1.card := by
  change (Finset.image (mapMolecularFullereneCarrierAtom input symmetry) face.1).card =
    face.1.card
  rw [Finset.card_image_iff.mpr]
  intro left leftMember right rightMember mapped
  exact mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
    (molecularFullereneFaceCarrier_subset oriented face leftMember)
    (molecularFullereneFaceCarrier_subset oriented face rightMember) mapped

private theorem mapMolecularFullereneFaceCarrier_mem_iff
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry)
    (face : MolecularFullereneFaceCarrier input)
    (atom : MolecularFullereneCarrierAtom input) :
    (symmetry atom).1 ∈
        (mapMolecularFullereneFaceCarrier symmetry reversing face).1 ↔
      atom.1 ∈ face.1 := by
  constructor
  · intro member
    rcases Finset.mem_image.mp member with ⟨source, sourceMember, mapped⟩
    have sourceCarrier := molecularFullereneFaceCarrier_subset oriented face sourceMember
    have sourceEq : source = atom.1 := by
      apply mapMolecularFullereneCarrierAtom_injective_on_carrier input symmetry
        sourceCarrier atom.2
      simpa using mapped
    simpa [sourceEq] using sourceMember
  · intro member
    exact Finset.mem_image.mpr ⟨atom.1, member, by
      exact mapMolecularFullereneCarrierAtom_of_mem input symmetry atom.1 atom.2⟩

/-- Every orientation-reversing carrier permutation preserves the number of incident pentagons
at each cage atom. -/
theorem molecularFullerenePentagonIncidence_map_eq
    {molecule : RawMolecule} {input : MolecularFullereneConfigurationInput}
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule input)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (reversing : MolecularFullereneFaceOrientationReversing input symmetry)
    (atom : MolecularFullereneCarrierAtom input) :
    molecularFullerenePentagonIncidence input (symmetry atom).1 =
      molecularFullerenePentagonIncidence input atom.1 := by
  let faceMap := mapMolecularFullereneFaceCarrier symmetry reversing
  have faceMapInjective : Function.Injective faceMap :=
    mapMolecularFullereneFaceCarrier_injective oriented symmetry reversing
  let faceEquiv : MolecularFullereneFaceCarrier input ≃
      MolecularFullereneFaceCarrier input :=
    Equiv.ofBijective faceMap
      ⟨faceMapInjective, Finite.surjective_of_injective faceMapInjective⟩
  have incidencePreserved (face : MolecularFullereneFaceCarrier input) :
      (face.1.card = 5 ∧ atom.1 ∈ face.1) ↔
        ((faceEquiv face).1.card = 5 ∧ (symmetry atom).1 ∈ (faceEquiv face).1) := by
    change (face.1.card = 5 ∧ atom.1 ∈ face.1) ↔
      ((mapMolecularFullereneFaceCarrier symmetry reversing face).1.card = 5 ∧
        (symmetry atom).1 ∈
          (mapMolecularFullereneFaceCarrier symmetry reversing face).1)
    rw [mapMolecularFullereneFaceCarrier_card oriented symmetry reversing face,
      mapMolecularFullereneFaceCarrier_mem_iff oriented symmetry reversing face atom]
  have incidentEquiv :
      { face : MolecularFullereneFaceCarrier input //
        face.1.card = 5 ∧ atom.1 ∈ face.1 } ≃
      { face : MolecularFullereneFaceCarrier input //
        face.1.card = 5 ∧ (symmetry atom).1 ∈ face.1 } :=
    faceEquiv.subtypeEquiv incidencePreserved
  exact (Fintype.card_congr incidentEquiv).symm

end
end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullerenePentagonIncidence_map_eq
