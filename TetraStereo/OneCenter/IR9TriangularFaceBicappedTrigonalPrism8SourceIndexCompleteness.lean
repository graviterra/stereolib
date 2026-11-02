import TetraStereo.OneCenter.IR9TransBicappedOctahedron8SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for TPRT-8

An ideal triangular-face-bicapped trigonal prism has one cap on each triangular face, together
with the six prism vertices in three corresponding vertical pairs.  Its vertex action is the
faithful product of an arbitrary exchange of the two capped triangular faces and an arbitrary
permutation of the three corresponding corners.  This is the same abstract `S2 × S3` action as
the trans-bicapped octahedron, but the independent incidence signature below is TPRT-specific:
it distinguishes cap incidence, triangular-face edges, corresponding vertical edges, and
cross-face nonedges.

The shared structural action has already been proved faithful and exhaustive as twelve coordinate
frames.  Here Lean proves that every frame preserves the TPRT-8 signature and that canonicalizing
the complete priority word is collision-free under exactly that structural symmetry relation.
Repeated and primed priorities are included.

IR-9 prints no TPRT-8-specific abbreviated index or absolute reference-axis recipe, so this is a
separately named mathematical completion, with no invented `A`/`C` assignment or distortion
tolerance.
-/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.triangularFaceBicappedTrigonalPrism.coordinationNumber = 8 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.triangularFaceBicappedTrigonalPrism.symbol = "TPRT-8" := rfl

theorem no_published_triangularFaceBicappedTrigonalPrism_configurationIndexInput
    (input : RedBookIR9.ConfigurationIndexInput) :
    input.geometry ≠ .triangularFaceBicappedTrigonalPrism := by
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

theorem triangularFaceBicappedTrigonalPrism_absoluteOrientation_only_none
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (rotation : Option BlueBookP93.RotationSense) :
    RedBookIR9.AbsoluteOrientationRecognized observation
        .triangularFaceBicappedTrigonalPrism rotation ↔
      observation = .none ∧ rotation = none := by
  cases observation <;> cases rotation <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## TPRT-specific incidence over the shared two-face/three-corner action -/

/-- Reuse the already kernel-proved two-caps plus two-by-three typed carrier.  Here
`baseVertex side corner` is read as a trigonal-prism vertex. -/
abbrev Position := TransBicappedOctahedron8SourceIndexCompleteness.Position
abbrev CoordinateFrame :=
  TransBicappedOctahedron8SourceIndexCompleteness.CoordinateFrame
abbrev coordinatePermutation :=
  TransBicappedOctahedron8SourceIndexCompleteness.coordinatePermutation
abbrev fullSymmetryGroup : SymmetryGroup Position :=
  TransBicappedOctahedron8SourceIndexCompleteness.fullSymmetryGroup

inductive PairSignature where
  | identical
  | oppositeCaps
  | capToOwnTriangularFace
  | capToOppositeTriangularFace
  | sameTriangularFaceEdge
  | correspondingVerticalEdge
  | crossFaceNonedge
  deriving DecidableEq, Repr

def pairSignature (left right : Position) : PairSignature :=
  if left = right then .identical
  else
    match left, right with
    | .cap _, .cap _ => .oppositeCaps
    | .cap capSide, .baseVertex vertexSide _
    | .baseVertex vertexSide _, .cap capSide =>
        if capSide = vertexSide then
          .capToOwnTriangularFace
        else
          .capToOppositeTriangularFace
    | .baseVertex leftSide leftCorner, .baseVertex rightSide rightCorner =>
        if leftSide = rightSide then .sameTriangularFaceEdge
        else if leftCorner = rightCorner then .correspondingVerticalEdge
        else .crossFaceNonedge

theorem coordinatePermutation_preserves_pairSignature :
    ∀ (side : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3))
      (left right : Position),
      pairSignature (coordinatePermutation side corner left)
          (coordinatePermutation side corner right) = pairSignature left right := by
  intro side corner left right
  cases left <;> cases right <;>
    simp [pairSignature, coordinatePermutation]

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨side, corner, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature side corner left right

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 12 :=
  TransBicappedOctahedron8SourceIndexCompleteness.card_fullSymmetryGroup

theorem coordinatePermutation_injective :
    Function.Injective (fun frame : CoordinateFrame =>
      coordinatePermutation frame.1 frame.2) :=
  TransBicappedOctahedron8SourceIndexCompleteness.coordinatePermutation_injective

theorem mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    (symmetry : Equiv.Perm Position) :
    symmetry ∈ fullSymmetryGroup ↔
      ∃ side : Equiv.Perm (Fin 2), ∃ corner : Equiv.Perm (Fin 3),
        symmetry = coordinatePermutation side corner :=
  TransBicappedOctahedron8SourceIndexCompleteness.mem_fullSymmetryGroup_iff_exists_coordinatePermutation
    symmetry

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

noncomputable def triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

theorem triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex_conforms_mathematical_source
    (placement : Position → PolyhedralPriorityNumber) :
    triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex placement =
      sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position)) := rfl

theorem priorityOfProduction_injective :
    Function.Injective BlueBookP93.priorityOfProduction :=
  TransBicappedOctahedron8SourceIndexCompleteness.priorityOfProduction_injective

def ProductionEquivalent
    (left right : Position → PolyhedralPriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

theorem productionCompleteIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber) :
    triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex left =
        triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex,
    triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex,
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
    triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex left =
        triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex right ↔
      ProductionEquivalent left right :=
  productionCompleteIndex_eq_iff_symmetryEquivalent left right

end TetraStereo.OneCenter.RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness
