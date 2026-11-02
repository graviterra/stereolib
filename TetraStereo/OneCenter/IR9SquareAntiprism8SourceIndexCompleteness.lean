import TetraStereo.OneCenter.IR9BipyramidalAbsoluteSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquareAntiprism8SourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for SAPR-8

Red Book Table IR-9.3 lists the eight-coordinate square antiprism as `SAPR-8`.
IR-9.3.3.2 requires a configuration index that distinguishes diastereomeric ligand placements,
but IR-9.3.3.3--8 gives no SAPR-8-specific short digit recipe.

This file first proves that negative applicability boundary over the independently transcribed
IR-9 constructors.  It then supplies a separately named mathematical completion for an exact
ideal square antiprism.  Its eight positions are the alternating vertices of the antiprism's
zig-zag rim.  The complete cyclic-distance signature derives exactly the sixteen dihedral
frames.  Canonicalizing the complete priority word over those frames is proved collision-free:
two outputs agree exactly when a full idealized symmetry transports one placement to the other.

The construction supports repeated and primed priority numbers.  It does not invent a distortion
tolerance, a Red-Book short index, or a SAPR-8-specific `A`/`C` reference axis.
-/

/-! ## Exact source applicability boundary -/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.squareAntiprism.coordinationNumber = 8 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.squareAntiprism.symbol = "SAPR-8" := rfl

/-- None of the transcribed IR-9.3.3 geometry-specific index constructors is a SAPR-8 recipe. -/
theorem no_published_squareAntiprism_configurationIndexInput
    (input : RedBookIR9.ConfigurationIndexInput) :
    input.geometry ≠ .squareAntiprism := by
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

/-- The transcribed absolute-orientation router accepts only absence of an absolute descriptor for
SAPR-8.  No geometry-specific `A`/`C` convention is silently inferred from general prose. -/
theorem squareAntiprism_absoluteOrientation_only_none
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (rotation : Option BlueBookP93.RotationSense) :
    RedBookIR9.AbsoluteOrientationRecognized observation .squareAntiprism rotation ↔
      observation = .none ∧ rotation = none := by
  cases observation <;> cases rotation <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## Typed ideal square antiprism and its complete signature -/

/-- The alternating eight-vertex zig-zag rim of an ideal square antiprism.  Even and odd
positions lie on its two square faces. -/
abbrev Position := ZMod 8

@[simp] theorem position_card : Fintype.card Position = 8 := by
  decide

/-- Cyclic separation along the alternating zig-zag rim.  Values `1` and `2` are respectively a
cross-face rim edge and a same-square edge; `3` and `4` are the two nonedge classes.  Thus this
single exact signature remembers every pair-incidence class of the ideal square antiprism. -/
def pairSignature (left right : Position) : Nat :=
  Nat.min (right - left).val (left - right).val

/-- One idealized square-antiprism frame: a rotation or reflection of its alternating rim. -/
abbrev CoordinateFrame := DihedralGroup 8

def coordinatePermutation (frame : CoordinateFrame) : Equiv.Perm Position :=
  BipyramidalAbsoluteSymmetry.polygonPermutation frame

@[simp] theorem coordinatePermutation_one :
    coordinatePermutation (1 : CoordinateFrame) = 1 :=
  BipyramidalAbsoluteSymmetry.polygonPermutation_one

theorem coordinatePermutation_mul (first second : CoordinateFrame) :
    coordinatePermutation first * coordinatePermutation second =
      coordinatePermutation (first * second) :=
  BipyramidalAbsoluteSymmetry.polygonPermutation_mul first second

theorem coordinatePermutation_inv (frame : CoordinateFrame) :
    (coordinatePermutation frame)⁻¹ = coordinatePermutation frame⁻¹ :=
  BipyramidalAbsoluteSymmetry.polygonPermutation_inv frame

/-- All structurally admitted ideal SAPR-8 symmetries, presented by the sixteen dihedral frames
rather than by an enumeration of all `8!` permutations. -/
def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ frame : CoordinateFrame, symmetry = coordinatePermutation frame }
  one_mem' := ⟨1, coordinatePermutation_one.symm⟩
  mul_mem' := by
    rintro first second ⟨firstFrame, rfl⟩ ⟨secondFrame, rfl⟩
    exact ⟨firstFrame * secondFrame,
      coordinatePermutation_mul firstFrame secondFrame⟩
  inv_mem' := by
    rintro symmetry ⟨frame, rfl⟩
    exact ⟨frame⁻¹, coordinatePermutation_inv frame⟩

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ frame : CoordinateFrame, symmetry = coordinatePermutation frame)
  infer_instance

def coordinateSymmetry (frame : CoordinateFrame) : fullSymmetryGroup :=
  ⟨coordinatePermutation frame, frame, rfl⟩

/-- Faithfulness stated directly for the underlying vertex permutations. -/
theorem coordinatePermutation_injective :
    Function.Injective coordinatePermutation := by
  apply BipyramidalAbsoluteSymmetry.polygonPermutation_injective (n := 8)
  decide

/-- The sixteen dihedral frames act faithfully on the eight positions. -/
theorem coordinateSymmetry_injective : Function.Injective coordinateSymmetry := by
  intro left right same
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

theorem coordinateSymmetry_surjective : Function.Surjective coordinateSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨frame, same⟩
  refine ⟨frame, ?_⟩
  apply Subtype.ext
  exact same.symm

noncomputable def coordinateFrameEquiv : CoordinateFrame ≃ fullSymmetryGroup :=
  Equiv.ofBijective coordinateSymmetry
    ⟨coordinateSymmetry_injective, coordinateSymmetry_surjective⟩

/-- Downstream canonicalization enumerates sixteen frames, never the ambient `8!` permutations. -/
noncomputable instance (priority := 2000) fullSymmetryGroupFintype :
    Fintype fullSymmetryGroup :=
  Fintype.ofEquiv CoordinateFrame coordinateFrameEquiv

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 16 := by
  rw [← Fintype.card_congr coordinateFrameEquiv]
  decide

/-- Every admitted frame preserves all cyclic-separation/incidence classes. -/
theorem coordinatePermutation_preserves_pairSignature :
    ∀ (frame : CoordinateFrame) (left right : Position),
      pairSignature (coordinatePermutation frame left)
          (coordinatePermutation frame right) = pairSignature left right := by
  decide

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨frame, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature frame left right

/-- Distances to the two endpoints of an oriented rim edge determine every SAPR-8 position. -/
theorem pairSignature_coordinates_injective :
    ∀ (first second left right : Position),
      pairSignature first second = 1 →
      pairSignature first left = pairSignature first right →
      pairSignature second left = pairSignature second right →
      left = right := by
  decide

/-- Every oriented rim edge is the image of the reference edge under a dihedral frame.  Frame
faithfulness above separately supplies uniqueness when it is needed. -/
theorem exists_coordinateFrame_maps_referenceEdge :
    ∀ (first second : Position), pairSignature first second = 1 →
      ∃ frame : CoordinateFrame,
        coordinatePermutation frame 0 = first ∧
          coordinatePermutation frame 1 = second := by
  decide

/-- A permutation preserving the complete SAPR-8 signature is necessarily one of the sixteen
coordinate frames.  This proves exhaustion structurally from two reference vertices; it does not
enumerate the ambient symmetric group. -/
theorem signaturePreserver_eq_coordinatePermutation
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right) :
    ∃ frame : CoordinateFrame, symmetry = coordinatePermutation frame := by
  have adjacent : pairSignature (symmetry 0) (symmetry 1) = 1 := by
    rw [preserves]
    decide
  rcases exists_coordinateFrame_maps_referenceEdge
      (symmetry 0) (symmetry 1) adjacent with ⟨frame, mapsReference⟩
  refine ⟨frame, Equiv.ext ?_⟩
  intro position
  apply pairSignature_coordinates_injective
      (symmetry 0) (symmetry 1) (symmetry position)
      (coordinatePermutation frame position) adjacent
  · calc
      pairSignature (symmetry 0) (symmetry position) = pairSignature 0 position :=
        preserves 0 position
      _ = pairSignature (symmetry 0) (coordinatePermutation frame position) := by
        rw [← mapsReference.1]
        exact (coordinatePermutation_preserves_pairSignature frame 0 position).symm
  · calc
      pairSignature (symmetry 1) (symmetry position) = pairSignature 1 position :=
        preserves 1 position
      _ = pairSignature (symmetry 1) (coordinatePermutation frame position) := by
        rw [← mapsReference.2]
        exact (coordinatePermutation_preserves_pairSignature frame 1 position).symm

def idealSignatureSymmetryGroup : SymmetryGroup Position :=
  signatureSymmetryGroup pairSignature

/-- Exact classification: membership in the structural sixteen-frame group is equivalent to
preservation of the independently stated complete pair signature. -/
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

/-- The structural dihedral presentation equals the signature-derived full symmetry group. -/
theorem fullSymmetryGroup_eq_idealSignatureSymmetryGroup :
    fullSymmetryGroup = idealSignatureSymmetryGroup := by
  ext symmetry
  exact mem_fullSymmetryGroup_iff_preserves_pairSignature symmetry

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

/-- Mathematical completion of IR-9.3.3.2 for exact ideal SAPR-8, intentionally separate from
the absent source-specific abbreviated recipe. -/
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

/-- Unconditional, collision-free relative classification, including repeated and primed
priority numbers. -/
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

noncomputable def squareAntiprismCompleteConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

theorem squareAntiprismCompleteConfigurationIndex_conforms_mathematical_source
    (placement : Position → PolyhedralPriorityNumber) :
    squareAntiprismCompleteConfigurationIndex placement =
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
    squareAntiprismCompleteConfigurationIndex left =
        squareAntiprismCompleteConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [squareAntiprismCompleteConfigurationIndex,
    squareAntiprismCompleteConfigurationIndex,
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
    squareAntiprismCompleteConfigurationIndex left =
        squareAntiprismCompleteConfigurationIndex right ↔
      ProductionEquivalent left right :=
  productionCompleteIndex_eq_iff_symmetryEquivalent left right

end TetraStereo.OneCenter.RedBookIR9.SquareAntiprism8SourceIndexCompleteness
