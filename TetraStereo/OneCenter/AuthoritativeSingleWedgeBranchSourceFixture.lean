import TetraStereo.OneCenter.AuthoritativeSingleWedgeExactPriorityDescriptor
import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuity

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.OneCenter.SingleWedgeBranchSourceFixture

open AuthoritativeChemicalInput AuthoritativeChemicalInput.SingleWedgeSource
open CertifiedLocalizedCIPInput RationalTetrahedralPermutation

/-!
A new literal drawing-only source on the existing Rule-4/5 nonvacuity semantic molecule.
Its two daughter centers have mirrored plain rays and absolute solid wedges. The original 3D
fixture is retained unchanged. No equivalence with its parser annotations or spatial model is
asserted, and occurrence scheduling/source approval remain separate obligations.
-/

def positions : List CartesianPoint2 :=
  [⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨2, 0⟩, ⟨3, 1⟩, ⟨2, 2⟩,
    ⟨-2, 0⟩, ⟨-3, 1⟩, ⟨-2, 2⟩, ⟨3, -1⟩, ⟨-3, -1⟩]

def diagram : DiagramConfiguration :=
  { atomPositions? := some positions, atomConfigurations := [], bonds :=
      [⟨0, 1, .plain, .absolute⟩, ⟨1, 2, .plain, .absolute⟩,
        ⟨1, 3, .plain, .absolute⟩, ⟨3, 4, .plain, .absolute⟩,
        ⟨3, 9, .plain, .absolute⟩, ⟨3, 5, .solidWedge, .absolute⟩,
        ⟨1, 6, .plain, .absolute⟩, ⟨6, 7, .plain, .absolute⟩,
        ⟨6, 10, .plain, .absolute⟩, ⟨6, 8, .solidWedge, .absolute⟩] }

def source : AuthoritativeChemicalInput :=
  { molecule := IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.source.molecule,
    diagram? := some diagram, spatial? := none }

def leftCenter : Fin source.molecule.atomCount := ⟨3, by decide +kernel⟩
def rightCenter : Fin source.molecule.atomCount := ⟨6, by decide +kernel⟩
def leftFrame : SingleWedgeSource.Frame := frameOfDiagram 3 diagram positions
def rightFrame : SingleWedgeSource.Frame := frameOfDiagram 6 diagram positions
def writtenPriorityOrder : List (Fin 4) := [3, 1, 0, 2]

theorem semantic_molecule_preserved :
    source.molecule = IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.source.molecule := rfl

theorem source_structurallyWellFormed : source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide +kernel)

theorem source_has_only_drawing_configuration :
    source.spatial? = none ∧ diagram.atomConfigurations = [] := ⟨rfl, rfl⟩

theorem left_source_frame : SourceFrame source leftCenter.val leftFrame :=
  ⟨diagram, positions, rfl, rfl, by decide +kernel, rfl⟩

theorem right_source_frame : SourceFrame source rightCenter.val rightFrame :=
  ⟨diagram, positions, rfl, rfl, by decide +kernel, rfl⟩

theorem left_extractor_returns_actual_frame : extract? source leftCenter = some leftFrame :=
  (extract?_eq_some_iff source leftCenter leftFrame).mpr left_source_frame

theorem right_extractor_returns_actual_frame : extract? source rightCenter = some rightFrame :=
  (extract?_eq_some_iff source rightCenter rightFrame).mpr right_source_frame

theorem source_endpoint_orders :
    leftFrame.endpoints = [1, 4, 9, 5] ∧ rightFrame.endpoints = [1, 7, 10, 8] := ⟨rfl, rfl⟩

theorem left_endpoint_atomic_separation : SourceEndpointAtomicSeparation source leftFrame := by
  intro left right
  fin_cases left <;> fin_cases right <;> decide +kernel

theorem right_endpoint_atomic_separation : SourceEndpointAtomicSeparation source rightFrame := by
  intro left right
  fin_cases left <;> fin_cases right <;> decide +kernel

theorem written_priority_is_actual_atomic_order :
    writtenPriorityOrder.Perm (List.finRange 4) ∧
      writtenPriorityOrder.Pairwise (fun left right =>
        writtenAtomicPriority source leftFrame right < writtenAtomicPriority source leftFrame left) ∧
      writtenPriorityOrder.Pairwise (fun left right =>
        writtenAtomicPriority source rightFrame right < writtenAtomicPriority source rightFrame left) := by
  decide +kernel

theorem exact_sorted_oriented_volumes :
    CartesianPoint3.orientedVolume leftFrame.fourth leftFrame.second leftFrame.first leftFrame.third = 6 ∧
      CartesianPoint3.orientedVolume rightFrame.fourth rightFrame.second rightFrame.first rightFrame.third = -6 := by
  decide +kernel

/-- Independent exact geometry of the actual source frames, before any occurrence adapter or
priority-sort execution is invoked. The two daughter drawings have opposite uppercase labels:
the left written-priority list has oriented volume `6` (positive, hence `S` under the calibrated
negative-`R`/positive-`S` contract) and the right list has oriented volume `-6` (negative, hence
`R`). -/
theorem actual_sorted_source_geometry :
    descriptorOfPriorityOrderedPoints?
        (writtenPriorityOrder.map (pointVector leftFrame.first leftFrame.second leftFrame.third leftFrame.fourth)) =
      some RS.S ∧
      descriptorOfPriorityOrderedPoints?
        (writtenPriorityOrder.map (pointVector rightFrame.first rightFrame.second rightFrame.third rightFrame.fourth)) =
      some RS.R := by
  decide +kernel

end TetraStereo.OneCenter.SingleWedgeBranchSourceFixture
