import TetraStereo.OneCenter.IR9SquareFaceMonocappedTrigonalPrism7FiniteSymmetry

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness

open FiniteSymmetry
open SquareFaceMonocappedTrigonalPrism7FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact IR-9 applicability boundary and finite completion for TPRS-7

Table IR-9.2 authoritatively assigns the idealized square-face-monocapped trigonal prism the symbol
`TPRS-7`.  IR-9.3.3.2 says that a configuration index is to distinguish ligand placements, but the
geometry-specific recipes in IR-9.3.3.3--8 cover only square-planar, octahedral, square-pyramidal,
bipyramidal, T-shaped, and see-saw systems.  In particular, the book does not state how the seventh
cap priority is to enter a TPRS-7 index.  IR-9.3.4 likewise supplies no TPRS-7 reference axis or
absolute-orientation construction.

This module proves that boundary against the independent source sum types.  It then applies the
finite-symmetry theorem to the complete idealized TPRS-7 signature.
The resulting seven-position canonical word fulfills the general distinguishing property exactly,
but is deliberately identified as a mathematical completion rather than a source-printed short
digit recipe.  No distortion cutoff or absolute `A`/`C` suffix is invented.
-/

@[simp] theorem geometry_coordinationNumber :
    BlueBookP93.Geometry.squareFaceMonocappedTrigonalPrism.coordinationNumber = 7 :=
  rfl

@[simp] theorem geometry_symbol :
    BlueBookP93.Geometry.squareFaceMonocappedTrigonalPrism.symbol = "TPRS-7" :=
  rfl

/-! ## Complete placement word and exact relative classification -/

/-- Explicit typed order containing all seven positions.  Its order is only a reference frame for
full-group canonicalization, not an attribution of an unpublished order to IUPAC. -/
def typedPositionOrder : List Position :=
  [ .cap,
    .prismVertex 0 0, .prismVertex 0 1, .prismVertex 0 2,
    .prismVertex 1 0, .prismVertex 1 1, .prismVertex 1 2 ]

theorem typedPositionOrder_nodup : typedPositionOrder.Nodup := by
  decide

theorem mem_typedPositionOrder (position : Position) : position ∈ typedPositionOrder := by
  cases position with
  | cap => simp [typedPositionOrder]
  | prismVertex face corner =>
      fin_cases face <;> fin_cases corner <;> simp [typedPositionOrder]

def placementWord (placement : Position → PriorityNumber) : List PriorityNumber :=
  typedPositionOrder.map placement

/-- Equality of the complete seven-donor priority multiset. -/
def SamePriorityMultiset (left right : Position → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

/-- Finite idealized completion of the general IR-9.3.3.2 configuration-index requirement. -/
noncomputable def sourceGeneralIndex (placement : Position → PriorityNumber) :
    List PriorityDigit :=
  canonicalPriorityIndex placement

def Equivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

/-- Every full idealized TPRS-7 symmetry leaves the complete priority word unchanged. -/
theorem sourceGeneralIndex_invariant
    (placement : Position → PriorityNumber) (symmetry : fullSymmetryGroup) :
    sourceGeneralIndex (relabel symmetry.1 placement) = sourceGeneralIndex placement :=
  canonicalPriorityIndex_invariant placement symmetry

/-- Equal complete words are equivalent to, and not merely implied by, full idealized TPRS-7
symmetry.  This stronger theorem also covers repeated and primed priorities. -/
theorem sourceGeneralIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber) :
    sourceGeneralIndex left = sourceGeneralIndex right ↔ Equivalent left right :=
  canonicalPriorityIndex_eq_iff left right

/-- Conventional fixed-composition and distinct-priority specialization.  The hypotheses state the
usual chemical comparison domain but are not needed by the stronger finite theorem. -/
theorem sourceGeneralIndex_eq_iff_symmetryEquivalent_of_completePriorityMultiset
    (left right : Position → PriorityNumber)
    (_leftInjective : Function.Injective left)
    (_rightInjective : Function.Injective right)
    (_sameMultiset : SamePriorityMultiset left right) :
    sourceGeneralIndex left = sourceGeneralIndex right ↔ Equivalent left right :=
  sourceGeneralIndex_eq_iff_symmetryEquivalent left right

theorem sourceGeneralIndex_distinguishes_diastereomers
    (left right : Position → PriorityNumber) (notEquivalent : ¬Equivalent left right) :
    sourceGeneralIndex left ≠ sourceGeneralIndex right :=
  canonicalPriorityIndex_distinguishes left right notEquivalent

/-! ## Exact source applicability boundary -/

/-- The independently transcribed geometry-specific IR-9.3.3 input vocabulary has no TPRS-7
constructor.  This is the precise formal statement that no source-spelled digit recipe was silently
borrowed from TPR-6 or a bipyramid. -/
theorem no_sourceSpecificConfigurationIndexInput :
    ¬∃ input : RedBookIR9.ConfigurationIndexInput,
      input.geometry = .squareFaceMonocappedTrigonalPrism := by
  rintro ⟨input, sameGeometry⟩
  cases input with
  | squarePlanar _ => cases sameGeometry
  | octahedral _ _ => cases sameGeometry
  | squarePyramid4 _ => cases sameGeometry
  | squarePyramid5 _ _ => cases sameGeometry
  | bipyramidal kind _ _ _ => cases kind <;> cases sameGeometry
  | tShape _ => cases sameGeometry
  | seeSaw _ _ => cases sameGeometry
  | trigonalPrism _ _ => cases sameGeometry

/-- The independent absolute-orientation vocabulary cannot manufacture a TPRS-7 `A`/`C` sense.
The generic `.none` observation remains valid as absence of an absolute suffix. -/
theorem no_sourceSpecificAbsoluteOrientation
    (observation : RedBookIR9.AbsoluteOrientationObservation)
    (sense : BlueBookP93.RotationSense) :
    ¬RedBookIR9.AbsoluteOrientationRecognized observation
      .squareFaceMonocappedTrigonalPrism (some sense) := by
  cases observation <;> cases sense <;>
    simp [RedBookIR9.AbsoluteOrientationRecognized,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?]

/-! ## Production-priority conformance bridge for the finite completion -/

/-- Production-priority entry point for the complete finite word.  It is intentionally separate
from `PolyhedralDescriptor.configurationIndex`, whose source-spelled TPRS-7 syntax is absent. -/
noncomputable def squareFaceMonocappedTrigonalPrismConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  sourceGeneralIndex
    (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- Exact production-to-independent-source bridge. -/
theorem squareFaceMonocappedTrigonalPrismConfigurationIndex_conforms_source
    (placement : Position → PolyhedralPriorityNumber) :
    squareFaceMonocappedTrigonalPrismConfigurationIndex placement =
      sourceGeneralIndex
        (fun position => BlueBookP93.priorityOfProduction (placement position)) :=
  rfl

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

/-- The finite completion has exactly the intended collision relation after production priority
translation. -/
theorem productionCompletionIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber) :
    squareFaceMonocappedTrigonalPrismConfigurationIndex left =
        squareFaceMonocappedTrigonalPrismConfigurationIndex right ↔
      ProductionEquivalent left right := by
  rw [squareFaceMonocappedTrigonalPrismConfigurationIndex,
    squareFaceMonocappedTrigonalPrismConfigurationIndex,
    sourceGeneralIndex_eq_iff_symmetryEquivalent]
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

theorem productionCompletionIndex_eq_iff_symmetryEquivalent_of_completePriorityMultiset
    (left right : Position → PolyhedralPriorityNumber)
    (_leftInjective : Function.Injective left)
    (_rightInjective : Function.Injective right)
    (_sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    squareFaceMonocappedTrigonalPrismConfigurationIndex left =
        squareFaceMonocappedTrigonalPrismConfigurationIndex right ↔
      ProductionEquivalent left right :=
  productionCompletionIndex_eq_iff_symmetryEquivalent left right

end TetraStereo.OneCenter.RedBookIR9.SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness
