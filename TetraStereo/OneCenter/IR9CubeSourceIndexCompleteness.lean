import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.CubeSourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for CU-8

Red Book Table IR-9.2 lists the eight-coordinate cube as `CU-8`.  IR-9.3.3.2 requires a
priority-number configuration index which distinguishes diastereoisomeric placements, but the
geometry-specific recipes in IR-9.3.3.3--8 cover only SP-4, OC-6, SPY-4/5, the bipyramids,
TS-3, and SS-4.  No CU-8 digit recipe is published there.

This file records that authority boundary as a theorem over the independently transcribed IR-9
input vocabulary.  It then supplies a deliberately separate mathematical completion for an exact
ideal cube: the least complete priority word under every signed-coordinate cube frame.  Those
48 frames are proved exhaustive for the structural cube group and preserve the complete Hamming-
distance signature.  Equality of the resulting words is proved equivalent to that full symmetry.
It is not presented as a literal, unpublished Red Book short-index convention.

No nearest-geometry distortion threshold and no unsupported cube `A`/`C` reference axis is
introduced.
-/

/-! ## Exact source applicability boundary -/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.cube.coordinationNumber = 8 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.cube.symbol = "CU-8" := rfl

/-- Exhaustiveness over the transcribed IR-9.3.3 geometry-specific constructors: none is a cube
recipe.  CU-8 is in the geometry table, but IR-9.3.3.3--8 supplies no corresponding constructor. -/
theorem no_published_cube_configurationIndexInput
    (input : RedBookIR9.ConfigurationIndexInput) :
    input.geometry ≠ .cube := by
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

/-- The only absolute-orientation observation accepted for CU-8 by the transcribed IR-9 router is
the absence of an absolute descriptor.  In particular, no cube-specific `A`/`C` sense is silently
inferred from the general C/A prose without a geometry-specific reference-axis convention. -/
theorem cube_absoluteOrientation_only_none
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (rotation : Option BlueBookP93.RotationSense) :
    RedBookIR9.AbsoluteOrientationRecognized observation .cube rotation ↔
      observation = .none ∧ rotation = none := by
  cases observation <;> cases rotation <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## Typed cube and independently derived full symmetry -/

/-- A cube vertex is its three independent binary coordinate signs. -/
abbrev Position := Fin 3 → Bool

theorem position_card : Fintype.card Position = 8 := by
  decide

/-- The all-negative reference corner. -/
def origin : Position := fun _ => false

/-- Number of coordinate signs on which two vertices differ.  Values `1`, `2`, and `3` are
respectively edge, face-diagonal, and body-diagonal incidence classes. -/
def pairSignature (left right : Position) : Nat :=
  (Finset.univ.filter fun coordinate => left coordinate ≠ right coordinate).card

/-- Independently flip any of the three coordinate signs. -/
def flipPermutation (flip : Position) : Equiv.Perm Position where
  toFun position := fun coordinate => flip coordinate ^^ position coordinate
  invFun position := fun coordinate => flip coordinate ^^ position coordinate
  left_inv := by
    intro position
    funext coordinate
    simp
  right_inv := by
    intro position
    funext coordinate
    simp

/-- Permute the three mutually perpendicular cube axes. -/
def axisPermutation (axis : Equiv.Perm (Fin 3)) : Equiv.Perm Position where
  toFun position := fun coordinate => position (axis.symm coordinate)
  invFun position := fun coordinate => position (axis coordinate)
  left_inv := by
    intro position
    funext coordinate
    simp
  right_inv := by
    intro position
    funext coordinate
    simp

/-- One exact ideal-cube frame: an independent sign flip followed by an axis permutation. -/
def coordinatePermutation (flip : Position) (axis : Equiv.Perm (Fin 3)) :
    Equiv.Perm Position :=
  flipPermutation flip * axisPermutation axis

def composeFlip (firstFlip : Position) (firstAxis : Equiv.Perm (Fin 3))
    (secondFlip : Position) : Position :=
  fun coordinate => firstFlip coordinate ^^ secondFlip (firstAxis.symm coordinate)

theorem coordinatePermutation_mul
    (firstFlip : Position) (firstAxis : Equiv.Perm (Fin 3))
    (secondFlip : Position) (secondAxis : Equiv.Perm (Fin 3)) :
    coordinatePermutation firstFlip firstAxis *
        coordinatePermutation secondFlip secondAxis =
      coordinatePermutation (composeFlip firstFlip firstAxis secondFlip)
        (firstAxis * secondAxis) := by
  apply Equiv.ext
  intro position
  funext coordinate
  simp [coordinatePermutation, flipPermutation, axisPermutation, composeFlip]
  congr 1

theorem coordinatePermutation_origin_one :
    coordinatePermutation origin 1 = 1 := by
  apply Equiv.ext
  intro position
  funext coordinate
  simp [coordinatePermutation, origin, flipPermutation, axisPermutation]

def inverseFlip (flip : Position) (axis : Equiv.Perm (Fin 3)) : Position :=
  fun coordinate => flip (axis coordinate)

theorem coordinatePermutation_inverse
    (flip : Position) (axis : Equiv.Perm (Fin 3)) :
    (coordinatePermutation flip axis)⁻¹ =
      coordinatePermutation (inverseFlip flip axis) axis⁻¹ := by
  apply Equiv.ext
  intro position
  funext coordinate
  simp [coordinatePermutation, inverseFlip, flipPermutation, axisPermutation]
  change position (axis coordinate) = position (axis.symm.symm coordinate)
  rw [axis.symm_symm]

/-- The full ideal-cube group, structurally presented as the 8 independent sign translations
times the 6 permutations of the three perpendicular axes.  This presentation avoids enumerating
all `8!` vertex permutations during kernel checking. -/
def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ flip : Position, ∃ axis : Equiv.Perm (Fin 3),
      symmetry = coordinatePermutation flip axis }
  one_mem' := by
    exact ⟨origin, 1, coordinatePermutation_origin_one.symm⟩
  mul_mem' := by
    rintro first second ⟨firstFlip, firstAxis, rfl⟩
      ⟨secondFlip, secondAxis, rfl⟩
    exact ⟨composeFlip firstFlip firstAxis secondFlip, firstAxis * secondAxis,
      coordinatePermutation_mul firstFlip firstAxis secondFlip secondAxis⟩
  inv_mem' := by
    rintro symmetry ⟨flip, axis, rfl⟩
    exact ⟨inverseFlip flip axis, axis⁻¹,
      coordinatePermutation_inverse flip axis⟩

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ flip : Position, ∃ axis : Equiv.Perm (Fin 3),
    symmetry = coordinatePermutation flip axis)
  infer_instance

abbrev CoordinateFrame := Position × Equiv.Perm (Fin 3)

def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame.1 frame.2, frame.1, frame.2, rfl⟩

/-- The signed-coordinate action is faithful.  This closed 48-frame fact is reduced by the kernel,
without scanning the ambient `8!` vertex permutations. -/
theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  decide

theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨flip, axis, same⟩
  refine ⟨(flip, axis), ?_⟩
  apply Subtype.ext
  exact same.symm

noncomputable def coordinateFrameEquiv : CoordinateFrame ≃ fullSymmetryGroup :=
  Equiv.ofBijective coordinateSymmetry
    ⟨coordinateSymmetry_injective, coordinateSymmetry_surjective⟩

/-- Use the structural 48-frame enumeration for every downstream canonical-index and orientation
proof, rather than the generic ambient-permutation `Fintype`. -/
noncomputable instance (priority := 2000) fullSymmetryGroupFintype :
    Fintype fullSymmetryGroup :=
  Fintype.ofEquiv CoordinateFrame coordinateFrameEquiv

/-- The structurally exhaustive full ideal-cube group has order `8 * 6 = 48`. -/
theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 48 := by
  rw [← Fintype.card_congr coordinateFrameEquiv]
  decide

/-- Every admitted signed-coordinate frame preserves the complete Hamming-distance signature of
the ideal cube. -/
theorem coordinatePermutation_preserves_pairSignature :
    ∀ (flip : Position) (axis : Equiv.Perm (Fin 3)) (left right : Position),
      pairSignature (coordinatePermutation flip axis left)
          (coordinatePermutation flip axis right) = pairSignature left right := by
  decide

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨flip, axis, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature flip axis left right

/-! ## Complete source-priority index -/

/-- Fixed typed enumeration used only to state equality of complete priority composition. -/
noncomputable def typedPositionOrder : List Position := Finset.univ.toList

theorem typedPositionOrder_nodup : typedPositionOrder.Nodup := by
  exact Finset.nodup_toList _

theorem mem_typedPositionOrder (position : Position) : position ∈ typedPositionOrder := by
  simp [typedPositionOrder]

noncomputable def placementWord (placement : Position → PriorityNumber) : List PriorityNumber :=
  typedPositionOrder.map placement

noncomputable def SamePriorityMultiset (left right : Position → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

/-- Mathematical completion of the general IR-9.3.3.2 distinguishing requirement for an exact
ideal CU-8 geometry.  This is a complete canonical word, not an attributed short source recipe. -/
noncomputable def sourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  canonicalPriorityIndex fullSymmetryGroup placement

def Equivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

/-- Every full ideal-cube symmetry leaves the complete mathematical index unchanged. -/
theorem sourceIndex_invariant
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup) :
    sourceIndex (relabel symmetry.1 placement) = sourceIndex placement :=
  canonicalIndex_relabel fullSymmetryGroup
    (fun position => priorityDigit (placement position)) symmetry

/-- Unconditional exact CU-8 classification, including repeated and primed priority numbers. -/
theorem sourceIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber) :
    sourceIndex left = sourceIndex right ↔ Equivalent left right :=
  canonicalPriorityIndex_eq_iff fullSymmetryGroup left right

/-- Conventional distinct-priority, fixed-composition specialization. -/
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

/-! ## Production-facing mathematical completion and exact bridge -/

/-- Production-priority wrapper around the complete ideal-cube classifier.  Its name and type
deliberately expose a mathematical completion, rather than claiming a source-published CU-8
short-index recipe. -/
noncomputable def cubeCompleteConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

theorem cubeCompleteConfigurationIndex_conforms_mathematical_source
    (placement : Position → PolyhedralPriorityNumber) :
    cubeCompleteConfigurationIndex placement =
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
    cubeCompleteConfigurationIndex left = cubeCompleteConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [cubeCompleteConfigurationIndex, cubeCompleteConfigurationIndex,
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
    cubeCompleteConfigurationIndex left = cubeCompleteConfigurationIndex right ↔
      ProductionEquivalent left right :=
  productionCompleteIndex_eq_iff_symmetryEquivalent left right

end TetraStereo.OneCenter.RedBookIR9.CubeSourceIndexCompleteness
