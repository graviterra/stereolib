import TetraStereo.OneCenter.IR9BipyramidalAbsoluteSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact idealized relative-index classification for DD-8

The eight-coordinate `dodecahedron` in Red Book Table IR-9.3 is the trigonal dodecahedron
(snub disphenoid), not the twenty-vertex regular dodecahedron.  Its `D2d` action preserves two
four-position ligand-site families, conventionally called A and B.  Each family has the same
four-slot cyclic incidence, and every spatial symmetry applies one common dihedral frame to both.

The independent signature below records the ordered A/B site classes and the cyclic separation of
the two slots.  Lean proves that its complete automorphism group is exactly the eight diagonal
dihedral frames.  Canonicalization over that structurally bounded group then gives a collision-free
complete mathematical index for every priority placement, including repeated and primed values.

IR-9.3.3.3--8 prints no DD-8-specific abbreviated index, and the transcribed absolute router has
no DD-8-specific reference-axis convention.  The complete word is therefore explicitly a
mathematical completion of the general distinguishing requirement, not an attributed source
recipe.  No arbitrary-coordinate distortion threshold is introduced.
-/

/-! ## Exact source applicability boundary -/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.dodecahedron.coordinationNumber = 8 := rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.dodecahedron.symbol = "DD-8" := rfl

theorem no_published_dodecahedron_configurationIndexInput
    (input : RedBookIR9.ConfigurationIndexInput) :
    input.geometry ≠ .dodecahedron := by
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

theorem dodecahedron_absoluteOrientation_only_none
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (rotation : Option BlueBookP93.RotationSense) :
    RedBookIR9.AbsoluteOrientationRecognized observation .dodecahedron rotation ↔
      observation = .none ∧ rotation = none := by
  cases observation <;> cases rotation <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## Independent typed DD-8 signature -/

/-- The two symmetry-inequivalent four-site families of an ideal trigonal dodecahedron. -/
inductive SiteClass where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- A typed ligand position is an A/B site class and one of four cyclic slots. -/
abbrev Position := SiteClass × ZMod 4

@[simp] theorem position_card : Fintype.card Position = 8 := by
  decide

/-- Unoriented cyclic separation of two four-family slots. -/
def slotSignature (left right : ZMod 4) : Nat :=
  Nat.min (right - left).val (left - right).val

/-- Complete ordered pair signature: both A/B site classes and their common cyclic separation. -/
def pairSignature (left right : Position) : SiteClass × SiteClass × Nat :=
  (left.1, right.1, slotSignature left.2 right.2)

/-- One full `D2d` frame, represented by its faithful dihedral action on the four slots. -/
abbrev CoordinateFrame := DihedralGroup 4

def slotPermutation (frame : CoordinateFrame) : Equiv.Perm (ZMod 4) :=
  BipyramidalAbsoluteSymmetry.polygonPermutation frame

@[simp] theorem slotPermutation_one :
    slotPermutation (1 : CoordinateFrame) = 1 :=
  BipyramidalAbsoluteSymmetry.polygonPermutation_one

theorem slotPermutation_mul (first second : CoordinateFrame) :
    slotPermutation first * slotPermutation second = slotPermutation (first * second) :=
  BipyramidalAbsoluteSymmetry.polygonPermutation_mul first second

theorem slotPermutation_inv (frame : CoordinateFrame) :
    (slotPermutation frame)⁻¹ = slotPermutation frame⁻¹ :=
  BipyramidalAbsoluteSymmetry.polygonPermutation_inv frame

/-- Apply the same DD-8 frame to the A and B slot families. -/
def coordinatePermutation (frame : CoordinateFrame) : Equiv.Perm Position :=
  Equiv.prodCongr (Equiv.refl SiteClass) (slotPermutation frame)

@[simp] theorem coordinatePermutation_apply
    (frame : CoordinateFrame) (position : Position) :
    coordinatePermutation frame position =
      (position.1, slotPermutation frame position.2) := rfl

@[simp] theorem coordinatePermutation_one :
    coordinatePermutation (1 : CoordinateFrame) = 1 := by
  apply Equiv.ext
  rintro ⟨site, slot⟩
  simp [coordinatePermutation]

theorem coordinatePermutation_mul (first second : CoordinateFrame) :
    coordinatePermutation first * coordinatePermutation second =
      coordinatePermutation (first * second) := by
  apply Equiv.ext
  rintro ⟨site, slot⟩
  apply Prod.ext
  · rfl
  · exact congrArg (fun permutation : Equiv.Perm (ZMod 4) => permutation slot)
      (slotPermutation_mul first second)

theorem coordinatePermutation_inv (frame : CoordinateFrame) :
    (coordinatePermutation frame)⁻¹ = coordinatePermutation frame⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul]
  simp

/-- The structural eight-frame presentation of the full ideal DD-8 symmetry group. -/
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

theorem coordinatePermutation_injective :
    Function.Injective coordinatePermutation := by
  intro left right same
  apply BipyramidalAbsoluteSymmetry.polygonPermutation_injective (n := 4) (by decide)
  apply Equiv.ext
  intro slot
  have atA := congrArg
    (fun permutation : Equiv.Perm Position => (permutation (.A, slot)).2) same
  exact atA

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

noncomputable instance (priority := 2000) fullSymmetryGroupFintype :
    Fintype fullSymmetryGroup :=
  Fintype.ofEquiv CoordinateFrame coordinateFrameEquiv

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 8 := by
  rw [← Fintype.card_congr coordinateFrameEquiv]
  decide

theorem slotPermutation_preserves_slotSignature :
    ∀ (frame : CoordinateFrame) (left right : ZMod 4),
      slotSignature (slotPermutation frame left) (slotPermutation frame right) =
        slotSignature left right := by
  decide

theorem coordinatePermutation_preserves_pairSignature :
    ∀ (frame : CoordinateFrame) (left right : Position),
      pairSignature (coordinatePermutation frame left)
          (coordinatePermutation frame right) = pairSignature left right := by
  intro frame left right
  simp only [pairSignature, coordinatePermutation_apply]
  rw [slotPermutation_preserves_slotSignature]

theorem fullSymmetry_preserves_pairSignature
    (symmetry : fullSymmetryGroup) (left right : Position) :
    pairSignature (symmetry.1 left) (symmetry.1 right) = pairSignature left right := by
  rcases symmetry.2 with ⟨frame, same⟩
  rw [same]
  exact coordinatePermutation_preserves_pairSignature frame left right

/-- Two slot distances to an oriented reference edge determine the slot. -/
theorem slotSignature_coordinates_injective :
    ∀ (first second left right : ZMod 4),
      slotSignature first second = 1 →
      slotSignature first left = slotSignature first right →
      slotSignature second left = slotSignature second right →
      left = right := by
  decide

theorem exists_coordinateFrame_maps_slotReferenceEdge :
    ∀ (first second : ZMod 4), slotSignature first second = 1 →
      ∃ frame : CoordinateFrame,
        slotPermutation frame 0 = first ∧ slotPermutation frame 1 = second := by
  decide

/-- Any signature-preserving vertex permutation fixes the A/B site class. -/
theorem signaturePreserver_preserves_siteClass
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right)
    (position : Position) :
    (symmetry position).1 = position.1 := by
  exact congrArg (fun signature : SiteClass × SiteClass × Nat => signature.1)
    (preserves position position)

/-- Any signature-preserving vertex permutation preserves cyclic slot separation even between an
A site and a B site. -/
theorem signaturePreserver_preserves_slotSignature
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right)
    (left right : Position) :
    slotSignature (symmetry left).2 (symmetry right).2 =
      slotSignature left.2 right.2 := by
  exact congrArg (fun signature : SiteClass × SiteClass × Nat => signature.2.2)
    (preserves left right)

/-- Exhaustion of the signature automorphisms.  The image of the first two A slots determines one
dihedral frame; distances to those two images reconstruct every A and B slot. -/
theorem signaturePreserver_eq_coordinatePermutation
    (symmetry : Equiv.Perm Position)
    (preserves : ∀ left right,
      pairSignature (symmetry left) (symmetry right) = pairSignature left right) :
    ∃ frame : CoordinateFrame, symmetry = coordinatePermutation frame := by
  let firstReference : Position := (.A, 0)
  let secondReference : Position := (.A, 1)
  have adjacent :
      slotSignature (symmetry firstReference).2 (symmetry secondReference).2 = 1 := by
    rw [signaturePreserver_preserves_slotSignature symmetry preserves]
    decide
  rcases exists_coordinateFrame_maps_slotReferenceEdge
      (symmetry firstReference).2 (symmetry secondReference).2 adjacent with
    ⟨frame, mapsFirst, mapsSecond⟩
  refine ⟨frame, Equiv.ext ?_⟩
  intro position
  apply Prod.ext
  · exact signaturePreserver_preserves_siteClass symmetry preserves position
  · apply slotSignature_coordinates_injective
      (symmetry firstReference).2 (symmetry secondReference).2
      (symmetry position).2 (coordinatePermutation frame position).2 adjacent
    · calc
        slotSignature (symmetry firstReference).2 (symmetry position).2 =
            slotSignature firstReference.2 position.2 :=
          signaturePreserver_preserves_slotSignature symmetry preserves
            firstReference position
        _ = slotSignature (symmetry firstReference).2
              (coordinatePermutation frame position).2 := by
          change slotSignature 0 position.2 =
            slotSignature (symmetry firstReference).2 (slotPermutation frame position.2)
          rw [← mapsFirst]
          exact (slotPermutation_preserves_slotSignature frame 0 position.2).symm
    · calc
        slotSignature (symmetry secondReference).2 (symmetry position).2 =
            slotSignature secondReference.2 position.2 :=
          signaturePreserver_preserves_slotSignature symmetry preserves
            secondReference position
        _ = slotSignature (symmetry secondReference).2
              (coordinatePermutation frame position).2 := by
          change slotSignature 1 position.2 =
            slotSignature (symmetry secondReference).2 (slotPermutation frame position.2)
          rw [← mapsSecond]
          exact (slotPermutation_preserves_slotSignature frame 1 position.2).symm

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

noncomputable def dodecahedronCompleteConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceIndex (fun position => BlueBookP93.priorityOfProduction (placement position))

theorem dodecahedronCompleteConfigurationIndex_conforms_mathematical_source
    (placement : Position → PolyhedralPriorityNumber) :
    dodecahedronCompleteConfigurationIndex placement =
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
    dodecahedronCompleteConfigurationIndex left =
        dodecahedronCompleteConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [dodecahedronCompleteConfigurationIndex,
    dodecahedronCompleteConfigurationIndex,
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
    dodecahedronCompleteConfigurationIndex left =
        dodecahedronCompleteConfigurationIndex right ↔
      ProductionEquivalent left right :=
  productionCompleteIndex_eq_iff_symmetryEquivalent left right

end TetraStereo.OneCenter.RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness
