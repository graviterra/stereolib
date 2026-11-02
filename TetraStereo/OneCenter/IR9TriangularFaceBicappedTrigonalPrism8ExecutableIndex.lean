import TetraStereo.OneCenter.IR9TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness
import TetraStereo.OneCenter.IR9TransBicappedOctahedron8ExecutableIndex

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness

open FiniteSymmetry

/-!
# Executable TPRT-8 complete mathematical index

TPRT-8 and OCT-8 have distinct incidence signatures but the same proved faithful coordinate
carrier: two capped faces and three corresponding corners, acted on by all twelve `S2 × S3`
frames.  This module reuses only that executable finite action.  Collision completeness is proved
again against the TPRT-specific independent `Equivalent` relation and mathematical source index.
-/

/-- Typed TPRT order: two face caps, then three vertices on each triangular face. -/
def executableTypedPositionOrder : List Position :=
  TransBicappedOctahedron8SourceIndexCompleteness.executableTypedPositionOrder

theorem executableTypedPositionOrder_nodup : executableTypedPositionOrder.Nodup :=
  TransBicappedOctahedron8SourceIndexCompleteness.executableTypedPositionOrder_nodup

theorem mem_executableTypedPositionOrder (position : Position) :
    position ∈ executableTypedPositionOrder :=
  TransBicappedOctahedron8SourceIndexCompleteness.mem_executableTypedPositionOrder position

/-- Assign values to the two caps and two corresponding triangular-face triples. -/
def placementOfEntries {alpha : Type}
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : alpha) : Position → alpha :=
  TransBicappedOctahedron8SourceIndexCompleteness.placementOfEntries
    cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2

/-- Computable TPRT-8 complete word over the shared twelve-frame carrier. -/
def executableSourceIndex (placement : Position → PriorityNumber) : List PriorityDigit :=
  TransBicappedOctahedron8SourceIndexCompleteness.executableSourceIndex placement

/-- Exact executable TPRT-8 completeness under its own incidence interpretation. -/
theorem executableSourceIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔ Equivalent left right := by
  exact TransBicappedOctahedron8SourceIndexCompleteness.executableSourceIndex_eq_iff_symmetryEquivalent
    left right

/-- Executable and existing mathematical TPRT-8 words induce the same classification. -/
theorem executableSourceIndex_sameClassification_as_source
    (left right : Position → PriorityNumber) :
    executableSourceIndex left = executableSourceIndex right ↔
      sourceIndex left = sourceIndex right := by
  rw [executableSourceIndex_eq_iff_symmetryEquivalent,
    sourceIndex_eq_iff_symmetryEquivalent]

/-- Executable production-facing complete TPRT-8 mathematical word. -/
def executableTriangularFaceBicappedTrigonalPrismConfigurationIndex
    (placement : Position → PolyhedralPriorityNumber) : List PriorityDigit :=
  executableSourceIndex
    (fun position => BlueBookP93.priorityOfProduction (placement position))

/-- Executable and mathematical production entries have the same exact collision boundary. -/
theorem executableTriangularFaceBicappedTrigonalPrismConfigurationIndex_sameClassification_as_mathematical
    (left right : Position → PolyhedralPriorityNumber) :
    executableTriangularFaceBicappedTrigonalPrismConfigurationIndex left =
        executableTriangularFaceBicappedTrigonalPrismConfigurationIndex right ↔
      triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex left =
        triangularFaceBicappedTrigonalPrismCompleteConfigurationIndex right := by
  exact executableSourceIndex_sameClassification_as_source
    (fun position => BlueBookP93.priorityOfProduction (left position))
    (fun position => BlueBookP93.priorityOfProduction (right position))

end TetraStereo.OneCenter.RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness
