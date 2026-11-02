import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for TPRS-8

A square-face-bicapped trigonal prism selects two of the prism's three rectangular faces.  They
share one vertical prism edge, leaving the third square face intrinsically unselected.  The full
idealized action independently exchanges the two triangular ends and optionally reflects the
corner coordinate through the shared selected-face edge; that reflection also exchanges the two
caps.  Hence the structural full group has `2 × 2 = 4` frames.

The pair signature below records both caps, cap-to-square-face incidence, the two triangular
faces, corresponding vertical edges, and cross-face nonedges.  Every structural frame preserves
it.  Canonicalizing the complete eight-priority word gives an exact relative-orbit classifier for
arbitrary repeated and primed priorities.

No TPRS-8-specific abbreviated index, absolute reference-axis rule, or universal distortion
tolerance is printed in the transcribed IR-9 rules, so this mathematical completion is separately
named and does not manufacture an `A`/`C` label.
-/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.squareFaceBicappedTrigonalPrism.coordinationNumber = 8 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.squareFaceBicappedTrigonalPrism.symbol = "TPRS-8" := rfl

theorem no_published_squareFaceBicappedTrigonalPrism_configurationIndexInput
    (input : RedBookIR9.ConfigurationIndexInput) :
    input.geometry ≠ .squareFaceBicappedTrigonalPrism := by
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

theorem squareFaceBicappedTrigonalPrism_absoluteOrientation_only_none
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (rotation : Option BlueBookP93.RotationSense) :
    RedBookIR9.AbsoluteOrientationRecognized observation
        .squareFaceBicappedTrigonalPrism rotation ↔
      observation = .none ∧ rotation = none := by
  cases observation <;> cases rotation <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## Typed incidence and four structural frames -/

inductive Position where
  | prismVertex (face : Fin 2) (corner : Fin 3)
  | cap (selectedFace : Fin 2)
  deriving DecidableEq, Fintype, Repr

@[simp] theorem position_card : Fintype.card Position = 8 := by
  decide

/-- The selected cap-face labels correspond to the square faces omitting outer corner 0 or 2.
Corner 1 lies on their shared vertical edge. -/
def omittedCorner : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 2

def CapIncidentToCorner (selectedFace : Fin 2) (corner : Fin 3) : Prop :=
  corner ≠ omittedCorner selectedFace

instance capIncidentToCornerDecidable (selectedFace : Fin 2) (corner : Fin 3) :
    Decidable (CapIncidentToCorner selectedFace corner) := by
  unfold CapIncidentToCorner
  infer_instance

inductive PairSignature where
  | identical
  | capPair
  | capToSelectedSquare
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
    | .cap selected, .prismVertex _ corner
    | .prismVertex _ corner, .cap selected =>
        if CapIncidentToCorner selected corner then
          .capToSelectedSquare
        else
          .capToOppositeVerticalEdge
    | .prismVertex leftFace leftCorner, .prismVertex rightFace rightCorner =>
        if leftFace = rightFace then .sameTriangularFace
        else if leftCorner = rightCorner then .correspondingVerticalEdge
        else .crossFaceNonedge

/-- The nontrivial selected-face relabeling.  It exchanges the two selected square faces. -/
def selectedFaceReflection : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- Its induced reflection on prism corners exchanges outer corners 0 and 2 and fixes the shared
corner 1. -/
def outerCornerReflection : Equiv.Perm (Fin 3) := Equiv.swap 0 2

def cornerPermutation (selectedFace : Equiv.Perm (Fin 2)) : Equiv.Perm (Fin 3) :=
  if selectedFace = 1 then 1 else outerCornerReflection

theorem cornerPermutation_one : cornerPermutation (1 : Equiv.Perm (Fin 2)) = 1 := by
  simp [cornerPermutation]

theorem cornerPermutation_mul
    (first second : Equiv.Perm (Fin 2)) :
    cornerPermutation first * cornerPermutation second =
      cornerPermutation (first * second) := by
  decide +revert

theorem cornerPermutation_inv (selectedFace : Equiv.Perm (Fin 2)) :
    (cornerPermutation selectedFace)⁻¹ = cornerPermutation selectedFace⁻¹ := by
  decide +revert

abbrev CoordinateFrame := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)

def coordinatePermutation
    (triangularFace selectedFace : Equiv.Perm (Fin 2)) :
    Equiv.Perm Position where
  toFun
    | .prismVertex face corner =>
        .prismVertex (triangularFace face) (cornerPermutation selectedFace corner)
    | .cap selected => .cap (selectedFace selected)
  invFun
    | .prismVertex face corner =>
        .prismVertex (triangularFace.symm face)
          ((cornerPermutation selectedFace).symm corner)
    | .cap selected => .cap (selectedFace.symm selected)
  left_inv := by
    intro position
    cases position <;> simp
  right_inv := by
    intro position
    cases position <;> simp

@[simp] theorem coordinatePermutation_prismVertex
    (triangularFace selectedFace : Equiv.Perm (Fin 2))
    (face : Fin 2) (corner : Fin 3) :
    coordinatePermutation triangularFace selectedFace (.prismVertex face corner) =
      .prismVertex (triangularFace face) (cornerPermutation selectedFace corner) := rfl

@[simp] theorem coordinatePermutation_cap
    (triangularFace selectedFace : Equiv.Perm (Fin 2)) (selected : Fin 2) :
    coordinatePermutation triangularFace selectedFace (.cap selected) =
      .cap (selectedFace selected) := rfl

theorem coordinatePermutation_one : coordinatePermutation 1 1 = 1 := by
  apply Equiv.ext
  intro position
  cases position <;> simp [cornerPermutation_one]

theorem coordinatePermutation_mul
    (firstTriangular secondTriangular : Equiv.Perm (Fin 2))
    (firstSelected secondSelected : Equiv.Perm (Fin 2)) :
    coordinatePermutation firstTriangular firstSelected *
        coordinatePermutation secondTriangular secondSelected =
      coordinatePermutation (firstTriangular * secondTriangular)
        (firstSelected * secondSelected) := by
  apply Equiv.ext
  intro position
  cases position with
  | cap selected => simp [Equiv.Perm.coe_mul]
  | prismVertex face corner =>
      simp only [Equiv.Perm.coe_mul, Function.comp_apply,
        coordinatePermutation_prismVertex]
      congr 1
      exact congrArg (fun permutation : Equiv.Perm (Fin 3) => permutation corner)
        (cornerPermutation_mul firstSelected secondSelected)

theorem coordinatePermutation_inv
    (triangularFace selectedFace : Equiv.Perm (Fin 2)) :
    (coordinatePermutation triangularFace selectedFace)⁻¹ =
      coordinatePermutation triangularFace⁻¹ selectedFace⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul]
  simpa using coordinatePermutation_one

def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ triangularFace selectedFace : Equiv.Perm (Fin 2),
      symmetry = coordinatePermutation triangularFace selectedFace }
  one_mem' := ⟨1, 1, coordinatePermutation_one.symm⟩
  mul_mem' := by
    rintro first second ⟨firstTriangular, firstSelected, rfl⟩
      ⟨secondTriangular, secondSelected, rfl⟩
    exact ⟨firstTriangular * secondTriangular,
      firstSelected * secondSelected,
      coordinatePermutation_mul firstTriangular secondTriangular
        firstSelected secondSelected⟩
  inv_mem' := by
    rintro symmetry ⟨triangularFace, selectedFace, rfl⟩
    exact ⟨triangularFace⁻¹, selectedFace⁻¹,
      coordinatePermutation_inv triangularFace selectedFace⟩

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ triangularFace selectedFace : Equiv.Perm (Fin 2),
    symmetry = coordinatePermutation triangularFace selectedFace)
  infer_instance

def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame.1 frame.2, frame.1, frame.2, rfl⟩

theorem coordinatePermutation_injective :
    Function.Injective (fun frame : CoordinateFrame =>
      coordinatePermutation frame.1 frame.2) := by
  rintro ⟨leftTriangular, leftSelected⟩ ⟨rightTriangular, rightSelected⟩ same
  apply Prod.ext
  · apply Equiv.ext
    intro face
    have atVertex := congrArg (fun permutation : Equiv.Perm Position =>
      permutation (.prismVertex face 1)) same
    exact (Position.prismVertex.inj atVertex).1
  · apply Equiv.ext
    intro selected
    have atCap := congrArg (fun permutation : Equiv.Perm Position =>
      permutation (.cap selected)) same
    exact Position.cap.inj atCap

theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  intro left right same
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨triangularFace, selectedFace, same⟩
  refine ⟨(triangularFace, selectedFace), ?_⟩
  apply Subtype.ext
  exact same.symm

noncomputable def coordinateFrameEquiv : CoordinateFrame ≃ fullSymmetryGroup :=
  Equiv.ofBijective coordinateSymmetry
    ⟨coordinateSymmetry_injective, coordinateSymmetry_surjective⟩

noncomputable instance (priority := 2000) fullSymmetryGroupFintype :
    Fintype fullSymmetryGroup :=
  Fintype.ofEquiv CoordinateFrame coordinateFrameEquiv

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 4 := by
  rw [← Fintype.card_congr coordinateFrameEquiv]
  decide

theorem coordinatePermutation_preserves_pairSignature :
    ∀ (triangularFace selectedFace : Equiv.Perm (Fin 2))
      (left right : Position),
      pairSignature (coordinatePermutation triangularFace selectedFace left)
          (coordinatePermutation triangularFace selectedFace right) =
        pairSignature left right := by
  decide

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨triangularFace, selectedFace, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature
    triangularFace selectedFace left right

theorem mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∃ triangularFace selectedFace : Equiv.Perm (Fin 2),
        symmetry = coordinatePermutation triangularFace selectedFace :=
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

noncomputable def squareFaceBicappedTrigonalPrismCompleteConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

theorem squareFaceBicappedTrigonalPrismCompleteConfigurationIndex_conforms_mathematical_source
    (placement : Position → PolyhedralPriorityNumber) :
    squareFaceBicappedTrigonalPrismCompleteConfigurationIndex placement =
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
    squareFaceBicappedTrigonalPrismCompleteConfigurationIndex left =
        squareFaceBicappedTrigonalPrismCompleteConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [squareFaceBicappedTrigonalPrismCompleteConfigurationIndex,
    squareFaceBicappedTrigonalPrismCompleteConfigurationIndex,
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

end TetraStereo.OneCenter.RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness
