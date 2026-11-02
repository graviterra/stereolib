import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for OCF-7

Red Book Table IR-9.2 identifies the seven-coordinate face-monocapped octahedron as `OCF-7`.
IR-9.3.3.2 requires a priority-number configuration index to distinguish diastereoisomeric
placements, but IR-9.3.3.3--8 supplies literal digit recipes only for SP-4, OC-6, SPY-4/5, the
bipyramids, TS-3, and SS-4.  It does not publish a geometry-specific OCF-7 digit recipe.

This file therefore does not attribute an invented short index to IUPAC.  It gives the OCF-7
positions an exact typed idealized model and applies the already proved finite-symmetry completion
of the general IR-9.3.3.2 distinguishing requirement.  The index is the least complete priority
word over every full symmetry of that model.  Equality of these words is proved equivalent to
full idealized OCF-7 symmetry, not merely implied by it.

No coordinate distortion threshold and no unsupported absolute `A`/`C` assignment is introduced.
-/

/-! ## Typed OCF-7 positions and structurally exact full symmetry -/

/-- The cap, the three vertices of the capped octahedral face, and their three octahedral
opposites.  Sharing the same `Fin 3` corner records the three antipodal pairs of the underlying
octahedron. -/
inductive Position where
  | cap
  | cappedFace (corner : Fin 3)
  | oppositeFace (corner : Fin 3)
  deriving DecidableEq, Fintype, Repr

theorem position_card : Fintype.card Position = 7 := by
  decide

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.faceMonocappedOctahedron.coordinationNumber = 7 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.faceMonocappedOctahedron.symbol = "OCF-7" := rfl

/-- Complete pairwise incidence classes of the idealized face-monocapped octahedron.  They retain
the cap/capped-face role in addition to octahedral opposition; this is deliberately richer than
squared distance alone, since a cap-to-capped-face edge and an octahedral edge can have the same
length in an ideal coordinate realization. -/
inductive PairSignature where
  | identical
  | capToCappedFace
  | capToOppositeFace
  | octahedralOpposite
  | octahedralEdge
  deriving DecidableEq, Repr

/-- Pairwise signature of the typed OCF-7 model. -/
def pairSignature (left right : Position) : PairSignature :=
  if left = right then
    .identical
  else
    match left, right with
    | .cap, .cappedFace _ | .cappedFace _, .cap => .capToCappedFace
    | .cap, .oppositeFace _ | .oppositeFace _, .cap => .capToOppositeFace
    | .cappedFace leftCorner, .oppositeFace rightCorner
    | .oppositeFace rightCorner, .cappedFace leftCorner =>
        if leftCorner = rightCorner then .octahedralOpposite else .octahedralEdge
    | _, _ => .octahedralEdge

/-- Every permutation of the three capped-face corners acts simultaneously on the corresponding
opposite vertices while fixing the cap. -/
def coordinatePermutation (corner : Equiv.Perm (Fin 3)) : Equiv.Perm Position where
  toFun
    | .cap => .cap
    | .cappedFace index => .cappedFace (corner index)
    | .oppositeFace index => .oppositeFace (corner index)
  invFun
    | .cap => .cap
    | .cappedFace index => .cappedFace (corner.symm index)
    | .oppositeFace index => .oppositeFace (corner.symm index)
  left_inv := by
    intro position
    cases position <;> simp
  right_inv := by
    intro position
    cases position <;> simp

@[simp] theorem coordinatePermutation_cap (corner : Equiv.Perm (Fin 3)) :
    coordinatePermutation corner .cap = .cap := rfl

@[simp] theorem coordinatePermutation_cappedFace
    (corner : Equiv.Perm (Fin 3)) (index : Fin 3) :
    coordinatePermutation corner (.cappedFace index) = .cappedFace (corner index) := rfl

@[simp] theorem coordinatePermutation_oppositeFace
    (corner : Equiv.Perm (Fin 3)) (index : Fin 3) :
    coordinatePermutation corner (.oppositeFace index) = .oppositeFace (corner index) := rfl

private theorem coordinatePermutation_one_structural : coordinatePermutation 1 = 1 := by
  apply Equiv.ext
  intro position
  cases position <;> simp

private theorem coordinatePermutation_mul_structural (first second : Equiv.Perm (Fin 3)) :
    coordinatePermutation first * coordinatePermutation second =
      coordinatePermutation (first * second) := by
  apply Equiv.ext
  intro position
  cases position <;> simp [Equiv.Perm.coe_mul]

private theorem coordinatePermutation_inv_structural (corner : Equiv.Perm (Fin 3)) :
    (coordinatePermutation corner)⁻¹ = coordinatePermutation corner⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul_structural]
  simpa using coordinatePermutation_one_structural

/-- The full OCF-7 symmetry group, structurally presented by the six simultaneous permutations
of the capped-face corners and their octahedral opposites.  This avoids enumerating all `7!`
ambient vertex permutations during elaboration and canonicalization. -/
def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ corner : Equiv.Perm (Fin 3), symmetry = coordinatePermutation corner }
  one_mem' := ⟨1, coordinatePermutation_one_structural.symm⟩
  mul_mem' := by
    rintro first second ⟨firstCorner, rfl⟩ ⟨secondCorner, rfl⟩
    exact ⟨firstCorner * secondCorner,
      coordinatePermutation_mul_structural firstCorner secondCorner⟩
  inv_mem' := by
    rintro symmetry ⟨corner, rfl⟩
    exact ⟨corner⁻¹, coordinatePermutation_inv_structural corner⟩

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ corner : Equiv.Perm (Fin 3),
    symmetry = coordinatePermutation corner)
  infer_instance

theorem coordinatePermutation_preserves_pairSignature
    (corner : Equiv.Perm (Fin 3)) (left right : Position) :
    pairSignature (coordinatePermutation corner left)
        (coordinatePermutation corner right) = pairSignature left right := by
  cases left <;> cases right <;>
    simp [pairSignature]

theorem coordinatePermutation_mem_fullSymmetryGroup (corner : Equiv.Perm (Fin 3)) :
    coordinatePermutation corner ∈ fullSymmetryGroup :=
  ⟨corner, rfl⟩

abbrev CoordinateFrame := Equiv.Perm (Fin 3)

def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame, coordinatePermutation_mem_fullSymmetryGroup frame⟩

theorem coordinatePermutation_injective : Function.Injective coordinatePermutation := by
  intro left right same
  apply Equiv.ext
  intro corner
  have atCorner := DFunLike.congr_fun same (Position.cappedFace corner)
  simpa using atCorner

theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  intro left right same
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

theorem card_coordinateFrame : Fintype.card CoordinateFrame = 6 := by
  decide

theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨corner, same⟩
  refine ⟨corner, ?_⟩
  apply Subtype.ext
  exact same.symm

noncomputable def coordinateFrameEquiv : CoordinateFrame ≃ fullSymmetryGroup :=
  Equiv.ofBijective coordinateSymmetry
    ⟨coordinateSymmetry_injective, coordinateSymmetry_surjective⟩

/-- Canonicalization enumerates six coordinate frames, never the ambient `7!` permutations. -/
noncomputable instance (priority := 2000) fullSymmetryGroupFintype :
    Fintype fullSymmetryGroup :=
  Fintype.ofEquiv CoordinateFrame coordinateFrameEquiv

/-- The structurally exact full group has the six symmetries of the capped triangular face. -/
theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 6 := by
  rw [← Fintype.card_congr coordinateFrameEquiv]
  exact card_coordinateFrame

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨corner, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature corner left right

/-- Pair signatures to the three capped-face vertices distinguish every OCF-7 position. -/
theorem cappedFace_reference_signatures_injective :
    ∀ (left right : Position),
      pairSignature (.cappedFace 0) left = pairSignature (.cappedFace 0) right →
      pairSignature (.cappedFace 1) left = pairSignature (.cappedFace 1) right →
      pairSignature (.cappedFace 2) left = pairSignature (.cappedFace 2) right →
      left = right := by
  decide

/-- Any ordered cap/capped-face reference tetrahedron with the OCF-7 signature is the image of
the canonical reference tetrahedron under one of the six coordinate frames. -/
theorem exists_coordinateFrame_maps_cappedFace_reference :
    ∀ (imageCap image0 image1 image2 : Position),
      pairSignature imageCap image0 = .capToCappedFace →
      pairSignature imageCap image1 = .capToCappedFace →
      pairSignature imageCap image2 = .capToCappedFace →
      pairSignature image0 image1 = .octahedralEdge →
      pairSignature image0 image2 = .octahedralEdge →
      pairSignature image1 image2 = .octahedralEdge →
      ∃ frame : CoordinateFrame,
        coordinatePermutation frame .cap = imageCap ∧
          coordinatePermutation frame (.cappedFace 0) = image0 ∧
          coordinatePermutation frame (.cappedFace 1) = image1 ∧
          coordinatePermutation frame (.cappedFace 2) = image2 := by
  decide

private theorem coordinatePermutation_apply_inverse
    (frame : CoordinateFrame) (position : Position) :
    coordinatePermutation frame (coordinatePermutation frame⁻¹ position) = position := by
  rw [← coordinatePermutation_inv_structural]
  exact (coordinatePermutation frame).apply_symm_apply position

/-- The three transported capped-face references still distinguish every position. -/
theorem coordinateFrame_cappedFace_signatures_injective
    (frame : CoordinateFrame) (left right : Position)
    (at0 : pairSignature (coordinatePermutation frame (.cappedFace 0)) left =
      pairSignature (coordinatePermutation frame (.cappedFace 0)) right)
    (at1 : pairSignature (coordinatePermutation frame (.cappedFace 1)) left =
      pairSignature (coordinatePermutation frame (.cappedFace 1)) right)
    (at2 : pairSignature (coordinatePermutation frame (.cappedFace 2)) left =
      pairSignature (coordinatePermutation frame (.cappedFace 2)) right) :
    left = right := by
  have pullback (reference : Position)
      (atReference : pairSignature (coordinatePermutation frame reference) left =
        pairSignature (coordinatePermutation frame reference) right) :
      pairSignature reference (coordinatePermutation frame⁻¹ left) =
        pairSignature reference (coordinatePermutation frame⁻¹ right) := by
    calc
      pairSignature reference (coordinatePermutation frame⁻¹ left) =
          pairSignature (coordinatePermutation frame reference)
            (coordinatePermutation frame (coordinatePermutation frame⁻¹ left)) :=
        (coordinatePermutation_preserves_pairSignature frame reference
          (coordinatePermutation frame⁻¹ left)).symm
      _ = pairSignature (coordinatePermutation frame reference) left := by
        rw [coordinatePermutation_apply_inverse]
      _ = pairSignature (coordinatePermutation frame reference) right := atReference
      _ = pairSignature (coordinatePermutation frame reference)
          (coordinatePermutation frame (coordinatePermutation frame⁻¹ right)) := by
        rw [coordinatePermutation_apply_inverse]
      _ = pairSignature reference (coordinatePermutation frame⁻¹ right) :=
        coordinatePermutation_preserves_pairSignature frame reference
          (coordinatePermutation frame⁻¹ right)
  have preimagesEqual := cappedFace_reference_signatures_injective
    (coordinatePermutation frame⁻¹ left) (coordinatePermutation frame⁻¹ right)
    (pullback (.cappedFace 0) at0) (pullback (.cappedFace 1) at1)
      (pullback (.cappedFace 2) at2)
  have imagesEqual := congrArg (coordinatePermutation frame) preimagesEqual
  simpa only [coordinatePermutation_apply_inverse] using imagesEqual

/-- Every permutation preserving the complete OCF-7 signature is one of the six structural
coordinate frames.  Exhaustion is reconstructed from the cap and capped-face reference
tetrahedron, without enumerating the ambient `7!` permutation type. -/
theorem signaturePreserver_eq_coordinatePermutation
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right) :
    ∃ frame : CoordinateFrame, symmetry = coordinatePermutation frame := by
  have cap0 : pairSignature (symmetry .cap) (symmetry (.cappedFace 0)) =
      .capToCappedFace := by simpa [pairSignature] using preserves .cap (.cappedFace 0)
  have cap1 : pairSignature (symmetry .cap) (symmetry (.cappedFace 1)) =
      .capToCappedFace := by simpa [pairSignature] using preserves .cap (.cappedFace 1)
  have cap2 : pairSignature (symmetry .cap) (symmetry (.cappedFace 2)) =
      .capToCappedFace := by simpa [pairSignature] using preserves .cap (.cappedFace 2)
  have edge01 : pairSignature (symmetry (.cappedFace 0)) (symmetry (.cappedFace 1)) =
      .octahedralEdge := by
    simpa [pairSignature] using preserves (.cappedFace 0) (.cappedFace 1)
  have edge02 : pairSignature (symmetry (.cappedFace 0)) (symmetry (.cappedFace 2)) =
      .octahedralEdge := by
    simpa [pairSignature] using preserves (.cappedFace 0) (.cappedFace 2)
  have edge12 : pairSignature (symmetry (.cappedFace 1)) (symmetry (.cappedFace 2)) =
      .octahedralEdge := by
    simpa [pairSignature] using preserves (.cappedFace 1) (.cappedFace 2)
  rcases exists_coordinateFrame_maps_cappedFace_reference
      (symmetry .cap) (symmetry (.cappedFace 0)) (symmetry (.cappedFace 1))
        (symmetry (.cappedFace 2)) cap0 cap1 cap2 edge01 edge02 edge12 with
    ⟨frame, _mapsCap, maps0, maps1, maps2⟩
  refine ⟨frame, Equiv.ext ?_⟩
  intro position
  apply coordinateFrame_cappedFace_signatures_injective frame
  · calc
      pairSignature (coordinatePermutation frame (.cappedFace 0)) (symmetry position) =
          pairSignature (symmetry (.cappedFace 0)) (symmetry position) := by rw [maps0]
      _ = pairSignature (.cappedFace 0) position := preserves (.cappedFace 0) position
      _ = pairSignature (coordinatePermutation frame (.cappedFace 0))
          (coordinatePermutation frame position) :=
        (coordinatePermutation_preserves_pairSignature frame (.cappedFace 0) position).symm
  · calc
      pairSignature (coordinatePermutation frame (.cappedFace 1)) (symmetry position) =
          pairSignature (symmetry (.cappedFace 1)) (symmetry position) := by rw [maps1]
      _ = pairSignature (.cappedFace 1) position := preserves (.cappedFace 1) position
      _ = pairSignature (coordinatePermutation frame (.cappedFace 1))
          (coordinatePermutation frame position) :=
        (coordinatePermutation_preserves_pairSignature frame (.cappedFace 1) position).symm
  · calc
      pairSignature (coordinatePermutation frame (.cappedFace 2)) (symmetry position) =
          pairSignature (symmetry (.cappedFace 2)) (symmetry position) := by rw [maps2]
      _ = pairSignature (.cappedFace 2) position := preserves (.cappedFace 2) position
      _ = pairSignature (coordinatePermutation frame (.cappedFace 2))
          (coordinatePermutation frame position) :=
        (coordinatePermutation_preserves_pairSignature frame (.cappedFace 2) position).symm

def idealSignatureSymmetryGroup : SymmetryGroup Position :=
  signatureSymmetryGroup pairSignature

theorem mem_fullSymmetryGroup_iff_preserves_pairSignature
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∀ left right,
        pairSignature (symmetry left) (symmetry right) = pairSignature left right := by
  constructor
  · rintro ⟨frame, rfl⟩
    exact coordinatePermutation_preserves_pairSignature frame
  · intro preserves
    exact signaturePreserver_eq_coordinatePermutation symmetry preserves

theorem fullSymmetryGroup_eq_idealSignatureSymmetryGroup :
    fullSymmetryGroup = idealSignatureSymmetryGroup := by
  ext symmetry
  exact mem_fullSymmetryGroup_iff_preserves_pairSignature symmetry

theorem mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∃ corner : Equiv.Perm (Fin 3), symmetry = coordinatePermutation corner := by
  constructor
  · intro member
    rcases coordinateSymmetry_surjective ⟨symmetry, member⟩ with ⟨corner, same⟩
    exact ⟨corner, (congrArg Subtype.val same).symm⟩
  · rintro ⟨corner, rfl⟩
    exact coordinatePermutation_mem_fullSymmetryGroup corner

/-! ## Complete source-priority index -/

/-- An explicit typed enumeration used to state equality of complete molecular composition.  It
does not purport to be an unprinted Red Book OCF-7 digit order. -/
def typedPositionOrder : List Position :=
  [ .cap,
    .cappedFace 0, .cappedFace 1, .cappedFace 2,
    .oppositeFace 0, .oppositeFace 1, .oppositeFace 2 ]

theorem typedPositionOrder_nodup : typedPositionOrder.Nodup := by
  decide

theorem mem_typedPositionOrder (position : Position) : position ∈ typedPositionOrder := by
  cases position with
  | cap => simp [typedPositionOrder]
  | cappedFace corner => fin_cases corner <;> simp [typedPositionOrder]
  | oppositeFace corner => fin_cases corner <;> simp [typedPositionOrder]

def placementWord (placement : Position → PriorityNumber) : List PriorityNumber :=
  typedPositionOrder.map placement

def SamePriorityMultiset (left right : Position → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

/-- Mathematical completion of the IR-9.3.3.2 relative configuration index for idealized OCF-7.
Every admitted full-symmetry frame contributes one complete seven-priority word and the least word
is selected. -/
noncomputable def sourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  canonicalPriorityIndex fullSymmetryGroup placement

def Equivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

/-- Every full idealized OCF-7 symmetry leaves the complete priority index unchanged. -/
theorem sourceIndex_invariant
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup) :
    sourceIndex (relabel symmetry.1 placement) = sourceIndex placement :=
  canonicalIndex_relabel fullSymmetryGroup
    (fun position => priorityDigit (placement position)) symmetry

/-- Exact OCF-7 completeness, including repeated and primed priority numbers: equal indices are
equivalent to, and not merely implied by, a full idealized OCF-7 symmetry. -/
theorem sourceIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber) :
    sourceIndex left = sourceIndex right ↔ Equivalent left right :=
  canonicalPriorityIndex_eq_iff fullSymmetryGroup left right

/-- The conventional fixed-composition, distinct-priority chemical domain is an immediate
specialization of the stronger unconditional exact theorem. -/
theorem sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (_leftInjective : Function.Injective left)
    (_rightInjective : Function.Injective right)
    (_sameMultiset : SamePriorityMultiset left right) :
    sourceIndex left = sourceIndex right ↔ Equivalent left right :=
  sourceIndex_eq_iff_symmetryEquivalent left right

theorem sourceIndex_distinguishes_diastereomers
    (left right : Position → PriorityNumber) (notEquivalent : ¬Equivalent left right) :
    sourceIndex left ≠ sourceIndex right :=
  canonicalPriorityIndex_distinguishes_diastereomers
    fullSymmetryGroup left right notEquivalent

/-! ## Production-facing constructor and exact conformance bridge -/

/-- Production-facing OCF-7 constructor.  Production currently has no shorter literal OCF-7
constructor to refine, so this deliberately returns the complete canonical digit word. -/
noncomputable def faceMonocappedOctahedronConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- The production-facing constructor is exactly the independent source construction after the
already-established production-to-source priority translation. -/
theorem faceMonocappedOctahedronConfigurationIndex_conforms_source
    (placement : Position → PolyhedralPriorityNumber) :
    faceMonocappedOctahedronConfigurationIndex placement =
      sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position)) := rfl

theorem priorityOfProduction_injective :
    Function.Injective BlueBookP93.priorityOfProduction := by
  intro left right same
  cases left
  cases right
  simp [BlueBookP93.priorityOfProduction] at same
  simp_all

def ProductionEquivalent
    (left right : Position → PolyhedralPriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

/-- Exact collision boundary of the new production-facing constructor. -/
theorem productionConfigurationIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber) :
    faceMonocappedOctahedronConfigurationIndex left =
        faceMonocappedOctahedronConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [faceMonocappedOctahedronConfigurationIndex,
    faceMonocappedOctahedronConfigurationIndex,
    sourceIndex_eq_iff_symmetryEquivalent]
  constructor
  · rintro ⟨symmetry, sourceSame⟩
    refine ⟨symmetry, ?_⟩
    funext position
    apply priorityOfProduction_injective
    exact congrFun sourceSame position
  · rintro ⟨symmetry, productionSame⟩
    refine ⟨symmetry, ?_⟩
    funext position
    exact congrArg BlueBookP93.priorityOfProduction
      (congrFun productionSame position)

/-- Fixed-composition/injective production specialization requested by the usual chemical
comparison domain. -/
theorem productionConfigurationIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PolyhedralPriorityNumber)
    (_leftInjective : Function.Injective left)
    (_rightInjective : Function.Injective right)
    (_sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    faceMonocappedOctahedronConfigurationIndex left =
        faceMonocappedOctahedronConfigurationIndex right ↔
      ProductionEquivalent left right :=
  productionConfigurationIndex_eq_iff_symmetryEquivalent left right

end TetraStereo.OneCenter.RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness
