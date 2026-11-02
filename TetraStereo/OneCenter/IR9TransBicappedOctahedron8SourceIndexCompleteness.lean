import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for OCT-8

An ideal trans-bicapped octahedron has two caps on opposite octahedral faces.  Relative to that
face axis, the six original octahedral vertices are three antipodal pairs: each cap is incident to
one member of every pair.  Thus a typed position is either a cap with a face side, or a base
vertex with the same side and one of three antipodal-pair coordinates.

The complete incidence signature below remembers cap/base roles, capped-face incidence,
octahedral opposition, and all remaining octahedral edges.  The structural coordinate group
consists of an arbitrary exchange of the two opposite capped faces and an arbitrary simultaneous
permutation of the three antipodal pairs, hence `2 × 6 = 12` frames.  Its complete canonical
priority word is proved collision-free under exactly this idealized symmetry relation.

IR-9.3.3.3--8 gives no OCT-8-specific short digit recipe or absolute reference-axis construction.
The index below is therefore a separately named mathematical completion of IR-9.3.3.2, not an
attributed source recipe.  It introduces neither a distortion threshold nor an `A`/`C` label.
-/

/-! ## Exact source applicability boundary -/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.transBicappedOctahedron.coordinationNumber = 8 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.transBicappedOctahedron.symbol = "OCT-8" := rfl

theorem no_published_transBicappedOctahedron_configurationIndexInput
    (input : RedBookIR9.ConfigurationIndexInput) :
    input.geometry ≠ .transBicappedOctahedron := by
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

theorem transBicappedOctahedron_absoluteOrientation_only_none
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (rotation : Option BlueBookP93.RotationSense) :
    RedBookIR9.AbsoluteOrientationRecognized observation
        .transBicappedOctahedron rotation ↔
      observation = .none ∧ rotation = none := by
  cases observation <;> cases rotation <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## Typed OCT-8 incidence and structural full group -/

inductive Position where
  | cap (side : Fin 2)
  | baseVertex (side : Fin 2) (pair : Fin 3)
  deriving DecidableEq, Fintype, Repr

@[simp] theorem position_card : Fintype.card Position = 8 := by
  decide

inductive PairSignature where
  | identical
  | oppositeCaps
  | capIncidentVertex
  | capFarVertex
  | octahedralAntipodes
  | sameCappedFaceEdge
  | crossFaceEdge
  deriving DecidableEq, Repr

/-- Complete cap/incidence signature of an ideal trans-bicapped octahedron. -/
def pairSignature (left right : Position) : PairSignature :=
  if left = right then .identical
  else
    match left, right with
    | .cap _, .cap _ => .oppositeCaps
    | .cap capSide, .baseVertex vertexSide _
    | .baseVertex vertexSide _, .cap capSide =>
        if capSide = vertexSide then .capIncidentVertex else .capFarVertex
    | .baseVertex leftSide leftPair, .baseVertex rightSide rightPair =>
        if leftPair = rightPair then .octahedralAntipodes
        else if leftSide = rightSide then .sameCappedFaceEdge else .crossFaceEdge

abbrev CoordinateFrame := Equiv.Perm (Fin 2) × Equiv.Perm (Fin 3)

def coordinatePermutation
    (side : Equiv.Perm (Fin 2)) (pair : Equiv.Perm (Fin 3)) :
    Equiv.Perm Position where
  toFun
    | .cap index => .cap (side index)
    | .baseVertex face index => .baseVertex (side face) (pair index)
  invFun
    | .cap index => .cap (side.symm index)
    | .baseVertex face index => .baseVertex (side.symm face) (pair.symm index)
  left_inv := by
    intro position
    cases position <;> simp
  right_inv := by
    intro position
    cases position <;> simp

@[simp] theorem coordinatePermutation_cap
    (side : Equiv.Perm (Fin 2)) (pair : Equiv.Perm (Fin 3)) (index : Fin 2) :
    coordinatePermutation side pair (.cap index) = .cap (side index) := rfl

@[simp] theorem coordinatePermutation_baseVertex
    (side : Equiv.Perm (Fin 2)) (pair : Equiv.Perm (Fin 3))
    (face : Fin 2) (index : Fin 3) :
    coordinatePermutation side pair (.baseVertex face index) =
      .baseVertex (side face) (pair index) := rfl

theorem coordinatePermutation_one : coordinatePermutation 1 1 = 1 := by
  apply Equiv.ext
  intro position
  cases position <;> simp

theorem coordinatePermutation_mul
    (firstSide secondSide : Equiv.Perm (Fin 2))
    (firstPair secondPair : Equiv.Perm (Fin 3)) :
    coordinatePermutation firstSide firstPair *
        coordinatePermutation secondSide secondPair =
      coordinatePermutation (firstSide * secondSide) (firstPair * secondPair) := by
  apply Equiv.ext
  intro position
  cases position <;> simp [Equiv.Perm.coe_mul]

theorem coordinatePermutation_inv
    (side : Equiv.Perm (Fin 2)) (pair : Equiv.Perm (Fin 3)) :
    (coordinatePermutation side pair)⁻¹ = coordinatePermutation side⁻¹ pair⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul]
  simpa using coordinatePermutation_one

/-- All twelve structural OCT-8 frames. -/
def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ side : Equiv.Perm (Fin 2), ∃ pair : Equiv.Perm (Fin 3),
      symmetry = coordinatePermutation side pair }
  one_mem' := ⟨1, 1, coordinatePermutation_one.symm⟩
  mul_mem' := by
    rintro first second ⟨firstSide, firstPair, rfl⟩
      ⟨secondSide, secondPair, rfl⟩
    exact ⟨firstSide * secondSide, firstPair * secondPair,
      coordinatePermutation_mul firstSide secondSide firstPair secondPair⟩
  inv_mem' := by
    rintro symmetry ⟨side, pair, rfl⟩
    exact ⟨side⁻¹, pair⁻¹, coordinatePermutation_inv side pair⟩

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ side : Equiv.Perm (Fin 2), ∃ pair : Equiv.Perm (Fin 3),
    symmetry = coordinatePermutation side pair)
  infer_instance

def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame.1 frame.2, frame.1, frame.2, rfl⟩

theorem coordinatePermutation_injective :
    Function.Injective (fun frame : CoordinateFrame =>
      coordinatePermutation frame.1 frame.2) := by
  rintro ⟨leftSide, leftPair⟩ ⟨rightSide, rightPair⟩ same
  apply Prod.ext
  · apply Equiv.ext
    intro side
    have atCap := congrArg (fun permutation : Equiv.Perm Position =>
      permutation (.cap side)) same
    exact Position.cap.inj atCap
  · apply Equiv.ext
    intro pair
    have atVertex := congrArg (fun permutation : Equiv.Perm Position =>
      permutation (.baseVertex 0 pair)) same
    exact (Position.baseVertex.inj atVertex).2

theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  intro left right same
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨side, pair, same⟩
  refine ⟨(side, pair), ?_⟩
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

/-- Every structural frame preserves the independently stated complete incidence signature. -/
theorem coordinatePermutation_preserves_pairSignature :
    ∀ (side : Equiv.Perm (Fin 2)) (pair : Equiv.Perm (Fin 3))
      (left right : Position),
      pairSignature (coordinatePermutation side pair left)
          (coordinatePermutation side pair right) = pairSignature left right := by
  intro side pair left right
  cases left <;> cases right <;>
    simp [pairSignature]

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨side, pair, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature side pair left right

theorem mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∃ side : Equiv.Perm (Fin 2), ∃ pair : Equiv.Perm (Fin 3),
        symmetry = coordinatePermutation side pair :=
  Iff.rfl

/-! ## Complete mathematical source index -/

noncomputable def typedPositionOrder : List Position := Finset.univ.toList

theorem typedPositionOrder_nodup : typedPositionOrder.Nodup :=
  Finset.nodup_toList _

theorem mem_typedPositionOrder (position : Position) : position ∈ typedPositionOrder := by
  simp [typedPositionOrder]

noncomputable def placementWord (placement : Position → PriorityNumber) :
    List PriorityNumber :=
  typedPositionOrder.map placement

noncomputable def SamePriorityMultiset
    (left right : Position → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

noncomputable def sourceIndex (placement : Position → PriorityNumber) :
    List PriorityDigit :=
  canonicalPriorityIndex fullSymmetryGroup placement

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

/-! ## Production-facing mathematical completion -/

noncomputable def transBicappedOctahedronCompleteConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

theorem transBicappedOctahedronCompleteConfigurationIndex_conforms_mathematical_source
    (placement : Position → PolyhedralPriorityNumber) :
    transBicappedOctahedronCompleteConfigurationIndex placement =
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
    transBicappedOctahedronCompleteConfigurationIndex left =
        transBicappedOctahedronCompleteConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [transBicappedOctahedronCompleteConfigurationIndex,
    transBicappedOctahedronCompleteConfigurationIndex,
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

theorem productionCompleteIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PolyhedralPriorityNumber)
    (_leftInjective : Function.Injective left)
    (_rightInjective : Function.Injective right)
    (_sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    transBicappedOctahedronCompleteConfigurationIndex left =
        transBicappedOctahedronCompleteConfigurationIndex right ↔
      ProductionEquivalent left right :=
  productionCompleteIndex_eq_iff_symmetryEquivalent left right

end TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness
