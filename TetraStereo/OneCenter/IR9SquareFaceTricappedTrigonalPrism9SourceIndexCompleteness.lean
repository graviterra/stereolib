import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for TPRS-9

The square-face-tricapped trigonal prism carries one cap on each of its three rectangular faces.
Its nine positions are the six prism vertices in two triangular faces and three square-face caps.
An arbitrary exchange of the triangular faces and an arbitrary simultaneous permutation of the
three corner/square-face labels gives every structural frame, for a faithful group of order
`2 × 6 = 12`.

The complete signature below records cap-to-square-face incidence, triangular-face edges,
corresponding vertical edges, and cross-face nonedges.  The complete canonical priority word is
then an exact relative-orbit classifier for repeated and primed priorities.

IR-9 gives no TPRS-9-specific short-index or absolute-axis construction.  This separately named
mathematical completion therefore adds neither an `A`/`C` convention nor a distortion tolerance.
-/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.squareFaceTricappedTrigonalPrism.coordinationNumber = 9 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.squareFaceTricappedTrigonalPrism.symbol = "TPRS-9" := rfl

theorem no_published_squareFaceTricappedTrigonalPrism_configurationIndexInput
    (input : RedBookIR9.ConfigurationIndexInput) :
    input.geometry ≠ .squareFaceTricappedTrigonalPrism := by
  cases input with
  | squarePlanar _ => simp [RedBookIR9.ConfigurationIndexInput.geometry]
  | octahedral _ _ => simp [RedBookIR9.ConfigurationIndexInput.geometry]
  | squarePyramid4 _ => simp [RedBookIR9.ConfigurationIndexInput.geometry]
  | squarePyramid5 _ _ => simp [RedBookIR9.ConfigurationIndexInput.geometry]
  | bipyramidal kind _ _ _ =>
      cases kind <;>
        simp [RedBookIR9.ConfigurationIndexInput.geometry,
          RedBookIR9.BipyramidKind.geometry]
  | tShape _ => simp [RedBookIR9.ConfigurationIndexInput.geometry]
  | seeSaw _ _ => simp [RedBookIR9.ConfigurationIndexInput.geometry]
  | trigonalPrism _ _ => simp [RedBookIR9.ConfigurationIndexInput.geometry]

theorem squareFaceTricappedTrigonalPrism_absoluteOrientation_only_none
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (rotation : Option BlueBookP93.RotationSense) :
    RedBookIR9.AbsoluteOrientationRecognized observation
        .squareFaceTricappedTrigonalPrism rotation ↔
      observation = .none ∧ rotation = none := by
  cases observation <;> cases rotation <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## Typed nine-position incidence and twelve structural frames -/

inductive Position where
  | prismVertex (face : Fin 2) (corner : Fin 3)
  | cap (squareFace : Fin 3)
  deriving DecidableEq, Fintype, Repr

@[simp] theorem position_card : Fintype.card Position = 9 := by
  decide

/-- Square-face label is the unique prism corner omitted by that rectangular face. -/
def CapIncidentToCorner (squareFace corner : Fin 3) : Prop :=
  squareFace ≠ corner

instance capIncidentToCornerDecidable (squareFace corner : Fin 3) :
    Decidable (CapIncidentToCorner squareFace corner) := by
  unfold CapIncidentToCorner
  infer_instance

inductive PairSignature where
  | identical
  | capPair
  | capToSquareFace
  | capToOppositeVerticalEdge
  | sameTriangularFace
  | correspondingVerticalEdge
  | crossFaceNonedge
  deriving DecidableEq, Repr

def pairSignature (left right : Position) : PairSignature :=
  if left = right then .identical
  else
    match left, right with
    | .cap _, .cap _ => .capPair
    | .cap squareFace, .prismVertex _ corner
    | .prismVertex _ corner, .cap squareFace =>
        if CapIncidentToCorner squareFace corner then
          .capToSquareFace
        else
          .capToOppositeVerticalEdge
    | .prismVertex leftFace leftCorner, .prismVertex rightFace rightCorner =>
        if leftFace = rightFace then .sameTriangularFace
        else if leftCorner = rightCorner then .correspondingVerticalEdge
        else .crossFaceNonedge

abbrev CoordinateFrame := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 3)

def coordinatePermutation
    (triangularFace : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) :
    Equiv.Perm Position where
  toFun
    | .prismVertex face index => .prismVertex (triangularFace face) (corner index)
    | .cap squareFace => .cap (corner squareFace)
  invFun
    | .prismVertex face index =>
        .prismVertex (triangularFace.symm face) (corner.symm index)
    | .cap squareFace => .cap (corner.symm squareFace)
  left_inv := by
    intro position
    cases position <;> simp
  right_inv := by
    intro position
    cases position <;> simp

@[simp] theorem coordinatePermutation_prismVertex
    (triangularFace : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3))
    (face : Fin 2) (index : Fin 3) :
    coordinatePermutation triangularFace corner (.prismVertex face index) =
      .prismVertex (triangularFace face) (corner index) := rfl

@[simp] theorem coordinatePermutation_cap
    (triangularFace : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3))
    (squareFace : Fin 3) :
    coordinatePermutation triangularFace corner (.cap squareFace) =
      .cap (corner squareFace) := rfl

theorem coordinatePermutation_one : coordinatePermutation 1 1 = 1 := by
  apply Equiv.ext
  intro position
  cases position <;> simp

theorem coordinatePermutation_mul
    (firstTriangular secondTriangular : Equiv.Perm (Fin 2))
    (firstCorner secondCorner : Equiv.Perm (Fin 3)) :
    coordinatePermutation firstTriangular firstCorner *
        coordinatePermutation secondTriangular secondCorner =
      coordinatePermutation (firstTriangular * secondTriangular)
        (firstCorner * secondCorner) := by
  apply Equiv.ext
  intro position
  cases position <;> simp [Equiv.Perm.coe_mul]

theorem coordinatePermutation_inv
    (triangularFace : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) :
    (coordinatePermutation triangularFace corner)⁻¹ =
      coordinatePermutation triangularFace⁻¹ corner⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul]
  simpa using coordinatePermutation_one

def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ triangularFace : Equiv.Perm (Fin 2), ∃ corner : Equiv.Perm (Fin 3),
      symmetry = coordinatePermutation triangularFace corner }
  one_mem' := ⟨1, 1, coordinatePermutation_one.symm⟩
  mul_mem' := by
    rintro first second ⟨firstTriangular, firstCorner, rfl⟩
      ⟨secondTriangular, secondCorner, rfl⟩
    exact ⟨firstTriangular * secondTriangular, firstCorner * secondCorner,
      coordinatePermutation_mul firstTriangular secondTriangular
        firstCorner secondCorner⟩
  inv_mem' := by
    rintro symmetry ⟨triangularFace, corner, rfl⟩
    exact ⟨triangularFace⁻¹, corner⁻¹,
      coordinatePermutation_inv triangularFace corner⟩

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ triangularFace : Equiv.Perm (Fin 2),
    ∃ corner : Equiv.Perm (Fin 3),
      symmetry = coordinatePermutation triangularFace corner)
  infer_instance

def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame.1 frame.2, frame.1, frame.2, rfl⟩

theorem coordinatePermutation_injective :
    Function.Injective (fun frame : CoordinateFrame =>
      coordinatePermutation frame.1 frame.2) := by
  rintro ⟨leftTriangular, leftCorner⟩ ⟨rightTriangular, rightCorner⟩ same
  apply Prod.ext
  · apply Equiv.ext
    intro face
    have atVertex := congrArg (fun permutation : Equiv.Perm Position =>
      permutation (.prismVertex face 0)) same
    exact (Position.prismVertex.inj atVertex).1
  · apply Equiv.ext
    intro corner
    have atCap := congrArg (fun permutation : Equiv.Perm Position =>
      permutation (.cap corner)) same
    exact Position.cap.inj atCap

theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  intro left right same
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨triangularFace, corner, same⟩
  refine ⟨(triangularFace, corner), ?_⟩
  apply Subtype.ext
  exact same.symm

noncomputable def coordinateFrameEquiv : CoordinateFrame ≃ fullSymmetryGroup :=
  Equiv.ofBijective coordinateSymmetry
    ⟨coordinateSymmetry_injective, coordinateSymmetry_surjective⟩

noncomputable instance (priority := 2000) fullSymmetryGroupFintype :
    Fintype fullSymmetryGroup :=
  Fintype.ofEquiv CoordinateFrame coordinateFrameEquiv

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 12 := by
  rw [← Fintype.card_congr coordinateFrameEquiv]
  decide

theorem coordinatePermutation_preserves_pairSignature :
    ∀ (triangularFace : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3))
      (left right : Position),
      pairSignature (coordinatePermutation triangularFace corner left)
          (coordinatePermutation triangularFace corner right) =
        pairSignature left right := by
  intro triangularFace corner left right
  cases left <;> cases right <;>
    simp [pairSignature, CapIncidentToCorner]

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨triangularFace, corner, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature
    triangularFace corner left right

theorem mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∃ triangularFace : Equiv.Perm (Fin 2), ∃ corner : Equiv.Perm (Fin 3),
        symmetry = coordinatePermutation triangularFace corner :=
  Iff.rfl

/-! ## Complete mathematical source index and production bridge -/

noncomputable def typedPositionOrder : List Position := Finset.univ.toList

noncomputable def placementWord (placement : Position → PriorityNumber) :
    List PriorityNumber := typedPositionOrder.map placement

noncomputable def SamePriorityMultiset
    (left right : Position → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

noncomputable def sourceIndex (placement : Position → PriorityNumber) :
    List PriorityDigit := canonicalPriorityIndex fullSymmetryGroup placement

def Equivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

theorem sourceIndex_invariant
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup) :
    sourceIndex (relabel symmetry.1 placement) = sourceIndex placement :=
  canonicalIndex_relabel fullSymmetryGroup
    (fun position => priorityDigit (placement position)) symmetry

theorem sourceIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber) :
    sourceIndex left = sourceIndex right ↔ Equivalent left right :=
  canonicalPriorityIndex_eq_iff fullSymmetryGroup left right

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

noncomputable def squareFaceTricappedTrigonalPrismCompleteConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

theorem squareFaceTricappedTrigonalPrismCompleteConfigurationIndex_conforms_mathematical_source
    (placement : Position → PolyhedralPriorityNumber) :
    squareFaceTricappedTrigonalPrismCompleteConfigurationIndex placement =
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

theorem productionCompleteIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber) :
    squareFaceTricappedTrigonalPrismCompleteConfigurationIndex left =
        squareFaceTricappedTrigonalPrismCompleteConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [squareFaceTricappedTrigonalPrismCompleteConfigurationIndex,
    squareFaceTricappedTrigonalPrismCompleteConfigurationIndex,
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

end TetraStereo.OneCenter.RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness
