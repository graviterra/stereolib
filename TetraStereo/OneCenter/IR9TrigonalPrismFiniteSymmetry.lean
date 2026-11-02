import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalPrismFiniteSymmetry

open FiniteSymmetry

/-!
# Complete finite symmetry for the ideal trigonal prism, TPR-6

The six positions are represented by `Fin 6`.  The standard product decomposition
`Fin 6 ≃ Fin 2 × Fin 3` records a triangular face and a corner on that face.  The pairwise
signature distinguishes equality, membership of one triangular face, a corresponding vertical
edge, and a cross-face nonedge.  Its signature automorphism group is therefore the complete full
vertex-symmetry group of the ideal trigonal prism.
-/

/-- The six ligand positions of an ideal trigonal prism. -/
abbrev Position := Fin 6

/-- Face/corner coordinates for a prism position. -/
def coordinates : Position ≃ Fin 2 × Fin 3 :=
  (finProdFinEquiv (m := 2) (n := 3)).symm

/-- The complete pairwise incidence classes of the ideal trigonal prism. -/
inductive PairSignature where
  | identical
  | sameTriangularFace
  | correspondingVerticalEdge
  | crossFaceNonedge
  deriving DecidableEq, Repr

/-- Pairwise signature of the ideal trigonal prism. -/
def pairSignature (left right : Position) : PairSignature :=
  if left = right then
    .identical
  else if (coordinates left).1 = (coordinates right).1 then
    .sameTriangularFace
  else if (coordinates left).2 = (coordinates right).2 then
    .correspondingVerticalEdge
  else
    .crossFaceNonedge

/-- The full TPR-6 symmetry group, derived rather than supplied as a hand-entered permutation
list. -/
def fullSymmetryGroup : SymmetryGroup Position :=
  signatureSymmetryGroup pairSignature

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∀ left right, pairSignature (symmetry left) (symmetry right) =
    pairSignature left right)
  infer_instance

/-- Apply a face permutation and the same corner permutation on both triangular faces. -/
def coordinatePermutation (face : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) :
    Equiv.Perm Position :=
  coordinates.trans ((Equiv.prodCongr face corner).trans coordinates.symm)

@[simp] theorem coordinates_coordinatePermutation
    (face : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) (position : Position) :
    coordinates (coordinatePermutation face corner position) =
      (face (coordinates position).1, corner (coordinates position).2) := by
  simp only [coordinatePermutation, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.apply_symm_apply]
  cases coordinates position
  rfl

/-- Swap the two triangular faces. -/
def faceSwap : Equiv.Perm Position :=
  coordinatePermutation (Equiv.swap 0 1) 1

/-- Rotate both triangular faces through one third of a turn. -/
def oneThirdRotation : Equiv.Perm Position :=
  coordinatePermutation 1 ((Equiv.swap 0 1) * (Equiv.swap 1 2))

/-- Reflect both triangular faces in the same vertical mirror plane. -/
def verticalReflection : Equiv.Perm Position :=
  coordinatePermutation 1 (Equiv.swap 1 2)

theorem coordinatePermutation_mem_fullSymmetryGroup
    (face : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) :
    coordinatePermutation face corner ∈ fullSymmetryGroup := by
  intro left right
  simp [pairSignature]

/-- A coordinate frame, consisting of a face relabeling and one common corner relabeling. -/
abbrev CoordinateFrame := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 3)

/-- Every coordinate frame is a member of the signature-derived group. -/
def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame.1 frame.2,
    coordinatePermutation_mem_fullSymmetryGroup frame.1 frame.2⟩

/-- Different face/corner frames induce different permutations of the six positions. -/
theorem coordinatePermutation_injective :
    Function.Injective (fun frame : CoordinateFrame =>
      coordinatePermutation frame.1 frame.2) := by
  rintro ⟨leftFace, leftCorner⟩ ⟨rightFace, rightCorner⟩ same
  apply Prod.ext
  · apply Equiv.ext
    intro face
    let position : Position := coordinates.symm (face, 0)
    have atPosition := congrArg
      (fun symmetry : Equiv.Perm Position => coordinates (symmetry position)) same
    have firstCoordinates := congrArg Prod.fst atPosition
    simpa [position] using firstCoordinates
  · apply Equiv.ext
    intro corner
    let position : Position := coordinates.symm (0, corner)
    have atPosition := congrArg
      (fun symmetry : Equiv.Perm Position => coordinates (symmetry position)) same
    have secondCoordinates := congrArg Prod.snd atPosition
    simpa [position] using secondCoordinates

theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  intro left right same
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

@[simp] theorem faceSwap_mem_fullSymmetryGroup :
    faceSwap ∈ fullSymmetryGroup :=
  coordinatePermutation_mem_fullSymmetryGroup _ _

@[simp] theorem oneThirdRotation_mem_fullSymmetryGroup :
    oneThirdRotation ∈ fullSymmetryGroup :=
  coordinatePermutation_mem_fullSymmetryGroup _ _

@[simp] theorem verticalReflection_mem_fullSymmetryGroup :
    verticalReflection ∈ fullSymmetryGroup :=
  coordinatePermutation_mem_fullSymmetryGroup _ _

theorem oneThirdRotation_cubed : oneThirdRotation ^ 3 = 1 := by
  decide

theorem oneThirdRotation_ne_one : oneThirdRotation ≠ 1 := by
  decide

theorem verticalReflection_squared : verticalReflection ^ 2 = 1 := by
  decide

theorem faceSwap_squared : faceSwap ^ 2 = 1 := by
  decide

/-- The derived full vertex-symmetry group of TPR-6 has exactly twelve elements. -/
theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 12 := by
  decide

/-- There are `2! * 3! = 12` face/corner coordinate frames. -/
theorem card_coordinateFrame : Fintype.card CoordinateFrame = 12 := by
  decide

/-- The coordinate description exhausts the signature-derived symmetry group. -/
theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  exact ((Fintype.bijective_iff_injective_and_card coordinateSymmetry).2
    ⟨coordinateSymmetry_injective, card_coordinateFrame.trans card_fullSymmetryGroup.symm⟩).2

/-- Exact classification of the full signature symmetries: an admitted permutation is precisely an
optional permutation of the two faces together with one common permutation of the three corners. -/
theorem mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∃ face : Equiv.Perm (Fin 2), ∃ corner : Equiv.Perm (Fin 3),
        symmetry = coordinatePermutation face corner := by
  constructor
  · intro member
    rcases coordinateSymmetry_surjective ⟨symmetry, member⟩ with ⟨⟨face, corner⟩, same⟩
    exact ⟨face, corner, (congrArg Subtype.val same).symm⟩
  · rintro ⟨face, corner, rfl⟩
    exact coordinatePermutation_mem_fullSymmetryGroup face corner

/-- Executable, frame-independent TPR-6 priority index. -/
noncomputable def canonicalPriorityIndex
    (placement : Position → BlueBookP93.PriorityNumber) :
    List CanonicalPriorityDigit :=
  FiniteSymmetry.canonicalPriorityIndex fullSymmetryGroup placement

/-- Every derived TPR-6 symmetry leaves the canonical priority index unchanged. -/
theorem canonicalPriorityIndex_invariant
    (placement : Position → BlueBookP93.PriorityNumber)
    (symmetry : fullSymmetryGroup) :
    canonicalPriorityIndex (relabel symmetry.1 placement) =
      canonicalPriorityIndex placement :=
  FiniteSymmetry.canonicalIndex_relabel fullSymmetryGroup
    (fun position => priorityDigit (placement position)) symmetry

/-- Equality of canonical TPR-6 indices is exactly equivalence under a full prism symmetry. -/
theorem canonicalPriorityIndex_eq_iff
    (left right : Position → BlueBookP93.PriorityNumber) :
    canonicalPriorityIndex left = canonicalPriorityIndex right ↔
      SymmetryEquivalent fullSymmetryGroup left right :=
  FiniteSymmetry.canonicalPriorityIndex_eq_iff fullSymmetryGroup left right

/-- Consequently, nonsymmetry-equivalent TPR-6 ligand placements cannot collide. -/
theorem canonicalPriorityIndex_distinguishes
    (left right : Position → BlueBookP93.PriorityNumber)
    (notEquivalent : ¬SymmetryEquivalent fullSymmetryGroup left right) :
    canonicalPriorityIndex left ≠ canonicalPriorityIndex right :=
  FiniteSymmetry.canonicalPriorityIndex_distinguishes_diastereomers
    fullSymmetryGroup left right notEquivalent

end TetraStereo.OneCenter.RedBookIR9.TrigonalPrismFiniteSymmetry
