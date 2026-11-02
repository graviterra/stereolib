import TetraStereo.OneCenter.AuthoritativeSingleWedgeBranchSourceFixture
import TetraStereo.OneCenter.AuthoritativeSingleWedgeExactPriorityDescriptor

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.RationalTetrahedralPermutation

/-!
# A three-center drawing-only successor source

A new literal drawing-only source over the retained Rule-4/5 nonvacuity semantic molecule of
`SingleWedgeBranchSourceFixture`.  Its bond list is the committed one with the first record
`⟨0, 1, plain⟩` replaced in place by the absolute solid wedge `⟨1, 0, solidWedge⟩`.  The two
daughter centers `3` and `6` keep their mirrored plain rays and their own absolute solid wedges,
so the replacement adds a genuine third, central wedge at atom `1`.  Nothing from the old parser
`@`/`@@` annotations or from its spatial model is transported; neither spatial coordinates nor
`atomConfigurations` entries are read.

The two daughter drawings reproduce the old strict atomic separation, the written priority
`I > Br > C > H` (`[3, 1, 0, 2]`) and the mirrored exact `R`/`S` geometry.  Under the corrected
tetrahedral calibration a negative priority-ordered oriented volume is `R` (clockwise with the
lowest-priority point remote) and a positive one is `S`.  The daughter priority-ordered volumes are
`+6` (left) and `-6` (right), so the actual daughter labels are `S` and `R` respectively.  The
central atom `1` carries two *equal* carbon ligands (endpoints `3` and `6`), so there is no strict
atomic priority and no atomic descriptor shortcut there; its geometry is exposed only under two
explicitly *hypothetical* written priority orders.  Geometry selected by a supplied permutation is
not an actual CIP priority determination.  Occurrence scheduling, Rule-4/5 pseudoasymmetric
production at the centre and source approval remain separate obligations.
-/

def positions : List CartesianPoint2 :=
  [⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨2, -1⟩, ⟨3, 0⟩, ⟨2, 1⟩,
    ⟨-2, -1⟩, ⟨-3, 0⟩, ⟨-2, 1⟩, ⟨3, -2⟩, ⟨-3, -2⟩]

def diagram : DiagramConfiguration :=
  { atomPositions? := some positions, atomConfigurations := [], bonds :=
      [⟨1, 0, .solidWedge, .absolute⟩, ⟨1, 2, .plain, .absolute⟩,
        ⟨1, 3, .plain, .absolute⟩, ⟨3, 4, .plain, .absolute⟩,
        ⟨3, 9, .plain, .absolute⟩, ⟨3, 5, .solidWedge, .absolute⟩,
        ⟨1, 6, .plain, .absolute⟩, ⟨6, 7, .plain, .absolute⟩,
        ⟨6, 10, .plain, .absolute⟩, ⟨6, 8, .solidWedge, .absolute⟩] }

def source : AuthoritativeChemicalInput :=
  { molecule := IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.source.molecule,
    diagram? := some diagram, spatial? := none }

def centralCenter : Fin source.molecule.atomCount := ⟨1, by decide +kernel⟩
def leftCenter : Fin source.molecule.atomCount := ⟨3, by decide +kernel⟩
def rightCenter : Fin source.molecule.atomCount := ⟨6, by decide +kernel⟩

def centralFrame : SingleWedgeSource.Frame := frameOfDiagram 1 diagram positions
def leftFrame : SingleWedgeSource.Frame := frameOfDiagram 3 diagram positions
def rightFrame : SingleWedgeSource.Frame := frameOfDiagram 6 diagram positions

/-- The independent written daughter priority order `I > Br > C > H`, as in the committed source. -/
def writtenPriorityOrder : List (Fin 4) := [3, 1, 0, 2]

/-! The actual written central endpoint order is `[0, 2, 3, 6]` = `[F, Cl, C3, C6]`: the replaced
wedge record is written first, so its fluorine occupies slot `0`.  `Cl` therefore leads and `F`
follows, while the two equal carbon ligands `3` and `6` occupy the remaining two slots.  The two
hypothetical orders below realize exactly those two assignments. -/

def centralHypotheticalOrderLeftFirst : List (Fin 4) := [1, 0, 2, 3]
def centralHypotheticalOrderRightFirst : List (Fin 4) := [1, 0, 3, 2]

theorem semantic_molecule_preserved :
    source.molecule = IUPACNormativeProvision.Rule45CanonicalFamilyNonvacuity.source.molecule := rfl

theorem source_structurallyWellFormed : source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide +kernel)

theorem source_has_only_drawing_configuration :
    source.spatial? = none ∧ diagram.atomConfigurations = [] := ⟨rfl, rfl⟩

theorem central_source_frame : SourceFrame source centralCenter.val centralFrame :=
  ⟨diagram, positions, rfl, rfl, by decide +kernel, rfl⟩

theorem left_source_frame : SourceFrame source leftCenter.val leftFrame :=
  ⟨diagram, positions, rfl, rfl, by decide +kernel, rfl⟩

theorem right_source_frame : SourceFrame source rightCenter.val rightFrame :=
  ⟨diagram, positions, rfl, rfl, by decide +kernel, rfl⟩

theorem central_extractor_returns_actual_frame : extract? source centralCenter = some centralFrame :=
  (extract?_eq_some_iff source centralCenter centralFrame).mpr central_source_frame

theorem left_extractor_returns_actual_frame : extract? source leftCenter = some leftFrame :=
  (extract?_eq_some_iff source leftCenter leftFrame).mpr left_source_frame

theorem right_extractor_returns_actual_frame : extract? source rightCenter = some rightFrame :=
  (extract?_eq_some_iff source rightCenter rightFrame).mpr right_source_frame

/-- Checked actual written endpoint lists: the central slot `0` is the new fluorine wedge. -/
theorem actual_endpoint_orders :
    centralFrame.endpoints = [0, 2, 3, 6] ∧
      leftFrame.endpoints = [1, 4, 9, 5] ∧
      rightFrame.endpoints = [1, 7, 10, 8] := ⟨rfl, rfl, rfl⟩

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

/-- Independent exact geometry of the actual daughter source frames, before any occurrence adapter
or supplied priority permutation is invoked.  The two daughter drawings have opposite uppercase
labels: the left priority-ordered volume is `+6` (hence `S`) and the right one is `-6` (hence `R`). -/
theorem actual_sorted_source_geometry :
    descriptorOfPriorityOrderedPoints?
        (writtenPriorityOrder.map (pointVector leftFrame.first leftFrame.second leftFrame.third leftFrame.fourth)) =
      some RS.S ∧
      descriptorOfPriorityOrderedPoints?
        (writtenPriorityOrder.map (pointVector rightFrame.first rightFrame.second rightFrame.third rightFrame.fourth)) =
      some RS.R := by
  decide +kernel

/-- The central atom's two written carbon ligands carry the same atomic number.  This is why no
strict atomic order and no `SourceEndpointAtomicSeparation` is asserted at the centre. -/
theorem central_carbon_ligands_tie :
    source.molecule.toLocalizedMoleculeGraph.atomZ (⟨3, by decide +kernel⟩ : source.AromaticCanonicalAtom) =
      source.molecule.toLocalizedMoleculeGraph.atomZ (⟨6, by decide +kernel⟩ : source.AromaticCanonicalAtom) := by
  decide +kernel

/-- The central written priority fails injectivity at slots `2` and `3`; no atomic shortcut exists. -/
theorem central_written_priority_tie :
    writtenAtomicPriority source centralFrame 2 = writtenAtomicPriority source centralFrame 3 := by
  decide +kernel

theorem central_has_no_strict_written_order :
    ¬Function.Injective (writtenAtomicPriority source centralFrame) := by
  intro injective
  exact absurd (injective central_written_priority_tie)
    (by decide : (2 : Fin 4) ≠ 3)

theorem central_hypothetical_orders_are_permutations :
    centralHypotheticalOrderLeftFirst.Perm (List.finRange 4) ∧
      centralHypotheticalOrderRightFirst.Perm (List.finRange 4) := ⟨by decide, by decide⟩

/-- Exact central source geometry under the hypothetical written order `[Cl, F, left, right]`.
The priority-ordered determinant is `+12`, so under the corrected calibration this is `S`.  This
is kernel-closed geometry, not an actual CIP priority determination. -/
theorem central_geometry_hypothetical_left_first :
    descriptorOfPriorityOrderedPoints?
      (centralHypotheticalOrderLeftFirst.map
        (pointVector centralFrame.first centralFrame.second centralFrame.third centralFrame.fourth)) =
      some RS.S := by
  decide +kernel

/-- Exact central source geometry under the hypothetical written order `[Cl, F, right, left]`; the
single carbon transposition flips the sign to `-12` and hence the label to `R`.  Again not an
actual CIP priority determination. -/
theorem central_geometry_hypothetical_right_first :
    descriptorOfPriorityOrderedPoints?
      (centralHypotheticalOrderRightFirst.map
        (pointVector centralFrame.first centralFrame.second centralFrame.third centralFrame.fourth)) =
      some RS.R := by
  decide +kernel

end TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource
