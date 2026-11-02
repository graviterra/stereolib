import TetraStereo.OneCenter.IR9TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness
import TetraStereo.OneCenter.IR9TransBicappedOctahedron8AbsoluteSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TriangularFaceBicappedTrigonalPrism8AbsoluteSymmetry

open FiniteSymmetry
open TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness

/-!
# Proper and mirror classes of the exact ideal TPRT-8 geometry

The two-capped-face/three-corresponding-corner coordinate action is definitionally the same
`S2 × S3` spatial action already proved for OCT-8.  The preceding module independently proves
that this action preserves the chemically different TPRT-8 incidence signature.  This file
transports the already checked orientation character, six-element proper subgroup, and exhaustive
mirror-coset result to TPRT-8.

The resulting two proper-orbit classes are mathematical absolute classes only; no source-specific
TPRT-8 `A`/`C` convention is claimed.
-/

abbrev frameOrientationSign :=
  TransBicappedOctahedron8AbsoluteSymmetry.frameOrientationSign

abbrev properSymmetryGroup : SymmetryGroup Position :=
  TransBicappedOctahedron8AbsoluteSymmetry.properSymmetryGroup

abbrev mirror : Equiv.Perm Position :=
  TransBicappedOctahedron8AbsoluteSymmetry.mirror

theorem frameOrientationSign_mul (first second : CoordinateFrame) :
    frameOrientationSign (first * second) =
      frameOrientationSign first * frameOrientationSign second :=
  TransBicappedOctahedron8AbsoluteSymmetry.frameOrientationSign_mul first second

theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 6 :=
  TransBicappedOctahedron8AbsoluteSymmetry.card_properSymmetryGroup

theorem mirror_mem_fullSymmetryGroup : mirror ∈ fullSymmetryGroup :=
  TransBicappedOctahedron8AbsoluteSymmetry.mirror_mem_fullSymmetryGroup

theorem mirror_not_mem_properSymmetryGroup : mirror ∉ properSymmetryGroup :=
  TransBicappedOctahedron8AbsoluteSymmetry.mirror_not_mem_properSymmetryGroup

theorem fullSymmetryGroup_proper_or_mirror_coset :
    ∀ symmetry : fullSymmetryGroup,
      symmetry.1 ∈ properSymmetryGroup ∨
        ∃ rotation : properSymmetryGroup,
          symmetry.1 = mirror * rotation.1 :=
  TransBicappedOctahedron8AbsoluteSymmetry.fullSymmetryGroup_proper_or_mirror_coset

theorem injectivePlacement_not_properEquivalent_to_mirror
    {Label : Type*} (placement : Position → Label)
    (injective : Function.Injective placement) :
    ¬SymmetryEquivalent properSymmetryGroup placement (relabel mirror placement) :=
  TransBicappedOctahedron8AbsoluteSymmetry.injectivePlacement_not_properEquivalent_to_mirror
    placement injective

theorem injectivePlacement_has_exactlyTwoAbsoluteIndices
    (placement : Position → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices fullSymmetryGroup properSymmetryGroup mirror
      (fun position => priorityDigit (placement position)) :=
  TransBicappedOctahedron8AbsoluteSymmetry.injectivePlacement_has_exactlyTwoAbsoluteIndices
    placement injective

end TetraStereo.OneCenter.RedBookIR9.TriangularFaceBicappedTrigonalPrism8AbsoluteSymmetry
