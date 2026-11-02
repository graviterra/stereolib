import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter.RedBookIR9.SquareFaceMonocappedTrigonalPrism7FiniteSymmetry

open FiniteSymmetry

/-!
# Complete finite symmetry of the ideal TPRS-7 polyhedron

Red Book Table IR-9.2 names the seven-coordinate idealized geometry “trigonal prism,
square-face monocapped” and assigns it the polyhedral symbol `TPRS-7`.  Its positions consist of
the six vertices of a trigonal prism together with the cap of one selected square face.

The signature below is a finite incidence presentation of exactly that idealized structure.  It
remembers the cap, which four prism vertices bound the capped square, and all ordinary trigonal-
prism pair-incidence classes.  The full idealized vertex-symmetry group is presented by its exact
four coordinate frames, and every admitted frame is proved to preserve this independently defined
signature.  The structural presentation avoids an elaborator-scale enumeration of all `7!`
ambient permutations.
-/

/-- Seven idealized ligand positions: a `2 × 3` trigonal-prism frame and its square-face cap. -/
inductive Position where
  | prismVertex (face : Fin 2) (corner : Fin 3)
  | cap
  deriving DecidableEq, Fintype, Repr

@[simp] theorem card_position : Fintype.card Position = 7 := by
  decide

/-- Corners zero and one bound the selected square face; corner two is opposite that square. -/
def OnCappedSquareCorner (corner : Fin 3) : Prop := corner ≠ 2

instance onCappedSquareCornerDecidable (corner : Fin 3) :
    Decidable (OnCappedSquareCorner corner) := by
  unfold OnCappedSquareCorner
  infer_instance

/-- Complete pair-incidence classes of the idealized capped prism.  Separate diagonal classes
make the unique cap position intrinsic to the signature. -/
inductive PairSignature where
  | capIdentity
  | prismIdentity
  | capToCappedSquare
  | capToOppositeCorner
  | sameTriangularFace
  | correspondingVerticalEdge
  | crossFaceNonedge
  deriving DecidableEq, Repr

/-- Symmetric complete incidence signature of TPRS-7. -/
def pairSignature : Position → Position → PairSignature
  | .cap, .cap => .capIdentity
  | .cap, .prismVertex _ corner
  | .prismVertex _ corner, .cap =>
      if OnCappedSquareCorner corner then .capToCappedSquare else .capToOppositeCorner
  | .prismVertex leftFace leftCorner, .prismVertex rightFace rightCorner =>
      if leftFace = rightFace ∧ leftCorner = rightCorner then .prismIdentity
      else if leftFace = rightFace then .sameTriangularFace
      else if leftCorner = rightCorner then .correspondingVerticalEdge
      else .crossFaceNonedge

/-- The nontrivial corner symmetry fixes the opposite corner and exchanges the two corners of the
capped square face. -/
def cappedSquareReflection : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The two allowed relabelings of the selected square's corner coordinate. -/
def cornerPermutation : Bool → Equiv.Perm (Fin 3)
  | false => 1
  | true => cappedSquareReflection

@[simp] theorem cornerPermutation_preserves_opposite (reflect : Bool) :
    cornerPermutation reflect 2 = 2 := by
  cases reflect <;> decide

@[simp] theorem cornerPermutation_preserves_capped_square
    (reflect : Bool) (corner : Fin 3) :
    OnCappedSquareCorner (cornerPermutation reflect corner) ↔
      OnCappedSquareCorner corner := by
  cases reflect <;> fin_cases corner <;> decide

/-- Extend a face relabeling and the selected-square reflection to all seven positions, fixing the
cap. -/
def coordinatePermutation (face : Equiv.Perm (Fin 2)) (reflect : Bool) :
    Equiv.Perm Position where
  toFun
    | .prismVertex side corner =>
        .prismVertex (face side) (cornerPermutation reflect corner)
    | .cap => .cap
  invFun
    | .prismVertex side corner =>
        .prismVertex (face.symm side) ((cornerPermutation reflect).symm corner)
    | .cap => .cap
  left_inv := by
    intro position
    cases position <;> simp
  right_inv := by
    intro position
    cases position <;> simp

@[simp] theorem coordinatePermutation_cap
    (face : Equiv.Perm (Fin 2)) (reflect : Bool) :
    coordinatePermutation face reflect .cap = .cap :=
  rfl

@[simp] theorem coordinatePermutation_prismVertex
    (face : Equiv.Perm (Fin 2)) (reflect : Bool)
    (side : Fin 2) (corner : Fin 3) :
    coordinatePermutation face reflect (.prismVertex side corner) =
      .prismVertex (face side) (cornerPermutation reflect corner) :=
  rfl

def composeReflection : Bool → Bool → Bool
  | false, reflect => reflect
  | true, false => true
  | true, true => false

theorem cornerPermutation_mul (first second : Bool) :
    cornerPermutation first * cornerPermutation second =
      cornerPermutation (composeReflection first second) := by
  cases first <;> cases second <;>
    apply Equiv.ext <;> intro corner <;> fin_cases corner <;> rfl

theorem coordinatePermutation_one : coordinatePermutation 1 false = 1 := by
  apply Equiv.ext
  intro position
  cases position <;> simp [cornerPermutation]

theorem coordinatePermutation_mul
    (firstFace secondFace : Equiv.Perm (Fin 2)) (firstReflect secondReflect : Bool) :
    coordinatePermutation firstFace firstReflect *
        coordinatePermutation secondFace secondReflect =
      coordinatePermutation (firstFace * secondFace)
        (composeReflection firstReflect secondReflect) := by
  apply Equiv.ext
  intro position
  cases position with
  | cap => rfl
  | prismVertex side corner =>
      simp only [Equiv.Perm.coe_mul, coordinatePermutation_prismVertex,
        Function.comp_apply]
      congr 1
      exact DFunLike.congr_fun
        (cornerPermutation_mul firstReflect secondReflect) corner

theorem coordinatePermutation_inv
    (face : Equiv.Perm (Fin 2)) (reflect : Bool) :
    (coordinatePermutation face reflect)⁻¹ = coordinatePermutation face⁻¹ reflect := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul]
  cases reflect <;> simpa [composeReflection] using coordinatePermutation_one

/-- The full TPRS-7 symmetry group, structurally presented by two triangular-face relabelings
and two selected-square reflections.  Canonicalization therefore never enumerates the ambient
`7!` vertex permutations. -/
def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ face : Equiv.Perm (Fin 2), ∃ reflect : Bool,
      symmetry = coordinatePermutation face reflect }
  one_mem' := ⟨1, false, coordinatePermutation_one.symm⟩
  mul_mem' := by
    rintro first second ⟨firstFace, firstReflect, rfl⟩
      ⟨secondFace, secondReflect, rfl⟩
    exact ⟨firstFace * secondFace, composeReflection firstReflect secondReflect,
      coordinatePermutation_mul firstFace secondFace firstReflect secondReflect⟩
  inv_mem' := by
    rintro symmetry ⟨face, reflect, rfl⟩
    exact ⟨face⁻¹, reflect, coordinatePermutation_inv face reflect⟩

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ face : Equiv.Perm (Fin 2), ∃ reflect : Bool,
    symmetry = coordinatePermutation face reflect)
  infer_instance

theorem coordinatePermutation_preserves_pairSignature
    (face : Equiv.Perm (Fin 2)) (reflect : Bool) (left right : Position) :
    pairSignature (coordinatePermutation face reflect left)
        (coordinatePermutation face reflect right) = pairSignature left right := by
  cases left with
  | cap =>
      cases right with
      | cap => rfl
      | prismVertex side corner =>
          simp only [coordinatePermutation_cap, coordinatePermutation_prismVertex,
            pairSignature]
          by_cases capped : OnCappedSquareCorner corner
          · have mapped : OnCappedSquareCorner (cornerPermutation reflect corner) :=
              (cornerPermutation_preserves_capped_square reflect corner).2 capped
            simp [capped, mapped]
          · have mapped : ¬OnCappedSquareCorner (cornerPermutation reflect corner) :=
              fun present => capped
                ((cornerPermutation_preserves_capped_square reflect corner).1 present)
            simp [capped, mapped]
  | prismVertex leftSide leftCorner =>
      cases right with
      | cap =>
          simp only [coordinatePermutation_cap, coordinatePermutation_prismVertex,
            pairSignature]
          by_cases capped : OnCappedSquareCorner leftCorner
          · have mapped : OnCappedSquareCorner (cornerPermutation reflect leftCorner) :=
              (cornerPermutation_preserves_capped_square reflect leftCorner).2 capped
            simp [capped, mapped]
          · have mapped : ¬OnCappedSquareCorner (cornerPermutation reflect leftCorner) :=
              fun present => capped
                ((cornerPermutation_preserves_capped_square reflect leftCorner).1 present)
            simp [capped, mapped]
      | prismVertex rightSide rightCorner =>
          simp only [coordinatePermutation_prismVertex, pairSignature]
          simp only [Equiv.apply_eq_iff_eq]

theorem coordinatePermutation_mem_fullSymmetryGroup
    (face : Equiv.Perm (Fin 2)) (reflect : Bool) :
    coordinatePermutation face reflect ∈ fullSymmetryGroup :=
  ⟨face, reflect, rfl⟩

/-- A coordinate frame consists of an arbitrary exchange of the triangular faces and the optional
reflection of the two capped-square corners. -/
abbrev CoordinateFrame := Equiv.Perm (Fin 2) × Bool

def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame.1 frame.2,
    coordinatePermutation_mem_fullSymmetryGroup frame.1 frame.2⟩

theorem coordinatePermutation_injective :
    Function.Injective (fun frame : CoordinateFrame =>
      coordinatePermutation frame.1 frame.2) := by
  rintro ⟨leftFace, leftReflect⟩ ⟨rightFace, rightReflect⟩ same
  apply Prod.ext
  · apply Equiv.ext
    intro side
    have atVertex := congrArg (fun permutation : Equiv.Perm Position =>
      permutation (.prismVertex side 2)) same
    simp only [coordinatePermutation_prismVertex,
      cornerPermutation_preserves_opposite] at atVertex
    exact Position.prismVertex.inj atVertex |>.1
  · cases leftReflect <;> cases rightReflect
    · rfl
    · exfalso
      have atVertex := congrArg (fun permutation : Equiv.Perm Position =>
        permutation (.prismVertex 0 0)) same
      simp [cornerPermutation, cappedSquareReflection] at atVertex
    · exfalso
      have atVertex := congrArg (fun permutation : Equiv.Perm Position =>
        permutation (.prismVertex 0 0)) same
      simp [cornerPermutation, cappedSquareReflection] at atVertex
    · rfl

theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  intro left right same
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

@[simp] theorem card_coordinateFrame : Fintype.card CoordinateFrame = 4 := by
  decide

theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨face, reflect, same⟩
  refine ⟨(face, reflect), ?_⟩
  apply Subtype.ext
  exact same.symm

noncomputable def coordinateFrameEquiv : CoordinateFrame ≃ fullSymmetryGroup :=
  Equiv.ofBijective coordinateSymmetry
    ⟨coordinateSymmetry_injective, coordinateSymmetry_surjective⟩

/-- Canonicalization enumerates four coordinate frames, never the ambient `7!` permutations. -/
noncomputable instance (priority := 2000) fullSymmetryGroupFintype :
    Fintype fullSymmetryGroup :=
  Fintype.ofEquiv CoordinateFrame coordinateFrameEquiv

/-- The structurally exact full TPRS-7 symmetry group has four elements. -/
theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 4 := by
  rw [← Fintype.card_congr coordinateFrameEquiv]
  exact card_coordinateFrame

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨face, reflect, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature face reflect left right

/-- Pair signatures to the three vertices of one triangular face distinguish every TPRS-7
position, including the cap and the corresponding vertices of the opposite face. -/
theorem triangularFace_reference_signatures_injective :
    ∀ (left right : Position),
      pairSignature (.prismVertex 0 0) left = pairSignature (.prismVertex 0 0) right →
      pairSignature (.prismVertex 0 1) left = pairSignature (.prismVertex 0 1) right →
      pairSignature (.prismVertex 0 2) left = pairSignature (.prismVertex 0 2) right →
      left = right := by
  decide

/-- Any ordered cap/triangular-face reference set with the complete TPRS-7 signature is the image
of the canonical reference set under one of the four coordinate frames. -/
theorem exists_coordinateFrame_maps_triangularFace_reference :
    ∀ (imageCap image0 image1 image2 : Position),
      pairSignature imageCap image0 = .capToCappedSquare →
      pairSignature imageCap image1 = .capToCappedSquare →
      pairSignature imageCap image2 = .capToOppositeCorner →
      pairSignature image0 image1 = .sameTriangularFace →
      pairSignature image0 image2 = .sameTriangularFace →
      pairSignature image1 image2 = .sameTriangularFace →
      ∃ frame : CoordinateFrame,
        coordinatePermutation frame.1 frame.2 .cap = imageCap ∧
          coordinatePermutation frame.1 frame.2 (.prismVertex 0 0) = image0 ∧
          coordinatePermutation frame.1 frame.2 (.prismVertex 0 1) = image1 ∧
          coordinatePermutation frame.1 frame.2 (.prismVertex 0 2) = image2 := by
  decide

private theorem coordinatePermutation_apply_inverse
    (frame : CoordinateFrame) (position : Position) :
    coordinatePermutation frame.1 frame.2
        (coordinatePermutation frame.1⁻¹ frame.2 position) = position := by
  rw [← coordinatePermutation_inv]
  exact (coordinatePermutation frame.1 frame.2).apply_symm_apply position

/-- The three transported triangular-face references still distinguish every position. -/
theorem coordinateFrame_triangularFace_signatures_injective
    (frame : CoordinateFrame) (left right : Position)
    (at0 : pairSignature (coordinatePermutation frame.1 frame.2 (.prismVertex 0 0)) left =
      pairSignature (coordinatePermutation frame.1 frame.2 (.prismVertex 0 0)) right)
    (at1 : pairSignature (coordinatePermutation frame.1 frame.2 (.prismVertex 0 1)) left =
      pairSignature (coordinatePermutation frame.1 frame.2 (.prismVertex 0 1)) right)
    (at2 : pairSignature (coordinatePermutation frame.1 frame.2 (.prismVertex 0 2)) left =
      pairSignature (coordinatePermutation frame.1 frame.2 (.prismVertex 0 2)) right) :
    left = right := by
  have pullback (reference : Position)
      (atReference : pairSignature (coordinatePermutation frame.1 frame.2 reference) left =
        pairSignature (coordinatePermutation frame.1 frame.2 reference) right) :
      pairSignature reference (coordinatePermutation frame.1⁻¹ frame.2 left) =
        pairSignature reference (coordinatePermutation frame.1⁻¹ frame.2 right) := by
    calc
      pairSignature reference (coordinatePermutation frame.1⁻¹ frame.2 left) =
          pairSignature (coordinatePermutation frame.1 frame.2 reference)
            (coordinatePermutation frame.1 frame.2
              (coordinatePermutation frame.1⁻¹ frame.2 left)) :=
        (coordinatePermutation_preserves_pairSignature frame.1 frame.2 reference
          (coordinatePermutation frame.1⁻¹ frame.2 left)).symm
      _ = pairSignature (coordinatePermutation frame.1 frame.2 reference) left := by
        rw [coordinatePermutation_apply_inverse]
      _ = pairSignature (coordinatePermutation frame.1 frame.2 reference) right := atReference
      _ = pairSignature (coordinatePermutation frame.1 frame.2 reference)
          (coordinatePermutation frame.1 frame.2
            (coordinatePermutation frame.1⁻¹ frame.2 right)) := by
        rw [coordinatePermutation_apply_inverse]
      _ = pairSignature reference (coordinatePermutation frame.1⁻¹ frame.2 right) :=
        coordinatePermutation_preserves_pairSignature frame.1 frame.2 reference
          (coordinatePermutation frame.1⁻¹ frame.2 right)
  have preimagesEqual := triangularFace_reference_signatures_injective
    (coordinatePermutation frame.1⁻¹ frame.2 left)
    (coordinatePermutation frame.1⁻¹ frame.2 right)
    (pullback (.prismVertex 0 0) at0) (pullback (.prismVertex 0 1) at1)
      (pullback (.prismVertex 0 2) at2)
  have imagesEqual := congrArg (coordinatePermutation frame.1 frame.2) preimagesEqual
  simpa only [coordinatePermutation_apply_inverse] using imagesEqual

/-- Every permutation preserving the complete TPRS-7 signature is one of the four structural
coordinate frames.  Exhaustion is reconstructed from the cap and one triangular face without
enumerating the ambient `7!` permutation type. -/
theorem signaturePreserver_eq_coordinatePermutation
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right) :
    ∃ face : Equiv.Perm (Fin 2), ∃ reflect : Bool,
      symmetry = coordinatePermutation face reflect := by
  let reference0 : Position := .prismVertex 0 0
  let reference1 : Position := .prismVertex 0 1
  let reference2 : Position := .prismVertex 0 2
  have cap0 : pairSignature (symmetry .cap) (symmetry reference0) =
      .capToCappedSquare := by simpa [reference0, pairSignature] using preserves .cap reference0
  have cap1 : pairSignature (symmetry .cap) (symmetry reference1) =
      .capToCappedSquare := by simpa [reference1, pairSignature] using preserves .cap reference1
  have cap2 : pairSignature (symmetry .cap) (symmetry reference2) =
      .capToOppositeCorner := by simpa [reference2, pairSignature] using preserves .cap reference2
  have same01 : pairSignature (symmetry reference0) (symmetry reference1) =
      .sameTriangularFace := by
    simpa [reference0, reference1, pairSignature] using preserves reference0 reference1
  have same02 : pairSignature (symmetry reference0) (symmetry reference2) =
      .sameTriangularFace := by
    simpa [reference0, reference2, pairSignature] using preserves reference0 reference2
  have same12 : pairSignature (symmetry reference1) (symmetry reference2) =
      .sameTriangularFace := by
    simpa [reference1, reference2, pairSignature] using preserves reference1 reference2
  rcases exists_coordinateFrame_maps_triangularFace_reference
      (symmetry .cap) (symmetry reference0) (symmetry reference1) (symmetry reference2)
        cap0 cap1 cap2 same01 same02 same12 with
    ⟨frame, _mapsCap, maps0, maps1, maps2⟩
  refine ⟨frame.1, frame.2, Equiv.ext ?_⟩
  intro position
  apply coordinateFrame_triangularFace_signatures_injective frame
  · calc
      pairSignature (coordinatePermutation frame.1 frame.2 reference0) (symmetry position) =
          pairSignature (symmetry reference0) (symmetry position) := by rw [maps0]
      _ = pairSignature reference0 position := preserves reference0 position
      _ = pairSignature (coordinatePermutation frame.1 frame.2 reference0)
          (coordinatePermutation frame.1 frame.2 position) :=
        (coordinatePermutation_preserves_pairSignature frame.1 frame.2 reference0 position).symm
  · calc
      pairSignature (coordinatePermutation frame.1 frame.2 reference1) (symmetry position) =
          pairSignature (symmetry reference1) (symmetry position) := by rw [maps1]
      _ = pairSignature reference1 position := preserves reference1 position
      _ = pairSignature (coordinatePermutation frame.1 frame.2 reference1)
          (coordinatePermutation frame.1 frame.2 position) :=
        (coordinatePermutation_preserves_pairSignature frame.1 frame.2 reference1 position).symm
  · calc
      pairSignature (coordinatePermutation frame.1 frame.2 reference2) (symmetry position) =
          pairSignature (symmetry reference2) (symmetry position) := by rw [maps2]
      _ = pairSignature reference2 position := preserves reference2 position
      _ = pairSignature (coordinatePermutation frame.1 frame.2 reference2)
          (coordinatePermutation frame.1 frame.2 position) :=
        (coordinatePermutation_preserves_pairSignature frame.1 frame.2 reference2 position).symm

def idealSignatureSymmetryGroup : SymmetryGroup Position :=
  signatureSymmetryGroup pairSignature

theorem mem_fullSymmetryGroup_iff_preserves_pairSignature
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∀ left right,
        pairSignature (symmetry left) (symmetry right) = pairSignature left right := by
  constructor
  · rintro ⟨face, reflect, rfl⟩
    exact coordinatePermutation_preserves_pairSignature face reflect
  · intro preserves
    exact signaturePreserver_eq_coordinatePermutation symmetry preserves

theorem fullSymmetryGroup_eq_idealSignatureSymmetryGroup :
    fullSymmetryGroup = idealSignatureSymmetryGroup := by
  ext symmetry
  exact mem_fullSymmetryGroup_iff_preserves_pairSignature symmetry

/-- Exact classification of every admitted idealized TPRS-7 symmetry. -/
theorem mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∃ face : Equiv.Perm (Fin 2), ∃ reflect : Bool,
        symmetry = coordinatePermutation face reflect := by
  constructor
  · intro member
    rcases coordinateSymmetry_surjective ⟨symmetry, member⟩ with ⟨⟨face, reflect⟩, same⟩
    exact ⟨face, reflect, (congrArg Subtype.val same).symm⟩
  · rintro ⟨face, reflect, rfl⟩
    exact coordinatePermutation_mem_fullSymmetryGroup face reflect

/-- Executable finite completion of the general IR-9.3.3.2 distinguishing requirement.  This is a
complete seven-entry canonical word, not a claim that IR-9 gives a TPRS-7-specific abbreviated
digit recipe. -/
noncomputable def canonicalPriorityIndex
    (placement : Position → BlueBookP93.PriorityNumber) :
    List CanonicalPriorityDigit :=
  FiniteSymmetry.canonicalPriorityIndex fullSymmetryGroup placement

theorem canonicalPriorityIndex_invariant
    (placement : Position → BlueBookP93.PriorityNumber)
    (symmetry : fullSymmetryGroup) :
    canonicalPriorityIndex (relabel symmetry.1 placement) =
      canonicalPriorityIndex placement :=
  FiniteSymmetry.canonicalIndex_relabel fullSymmetryGroup
    (fun position => priorityDigit (placement position)) symmetry

/-- Equality of complete canonical TPRS-7 words is exactly full idealized symmetry equivalence.
No injectivity assumption is needed, so repeated and primed priority numbers are covered. -/
theorem canonicalPriorityIndex_eq_iff
    (left right : Position → BlueBookP93.PriorityNumber) :
    canonicalPriorityIndex left = canonicalPriorityIndex right ↔
      SymmetryEquivalent fullSymmetryGroup left right :=
  FiniteSymmetry.canonicalPriorityIndex_eq_iff fullSymmetryGroup left right

theorem canonicalPriorityIndex_distinguishes
    (left right : Position → BlueBookP93.PriorityNumber)
    (notEquivalent : ¬SymmetryEquivalent fullSymmetryGroup left right) :
    canonicalPriorityIndex left ≠ canonicalPriorityIndex right :=
  FiniteSymmetry.canonicalPriorityIndex_distinguishes_diastereomers
    fullSymmetryGroup left right notEquivalent

end TetraStereo.OneCenter.RedBookIR9.SquareFaceMonocappedTrigonalPrism7FiniteSymmetry
