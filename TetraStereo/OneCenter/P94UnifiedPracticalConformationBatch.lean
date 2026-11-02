import TetraStereo.OneCenter.P94UnifiedPracticalConformationPerception
import TetraStereo.OneCenter.CIPObservedGeometryAssignmentConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.UnifiedPracticalConformationPerception

/-!
# Batch practical P-94 conformation perception

This module lifts the source-prioritized single-unit selector to a finite unit family. Duplicate
input units cannot duplicate public assignments, and membership retains the exact selected carrier
and its independent specialized-or-fallback judgment.
-/

/-- Exact independent meaning of one successful assignment for one requested unit. -/
def PracticalConformationAssignmentJudgment
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (assignment : P94ConformationAssignment) : Prop :=
  ∃ selected,
    PracticalConformationPerceptionJudgment molecule spatial unit selected ∧
    assignment = selected.toAssignment unit

theorem perceiveConformationAssignment?_eq_some_iff
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) (assignment : P94ConformationAssignment) :
    perceiveConformationAssignment? molecule spatial unit = some assignment ↔
      PracticalConformationAssignmentJudgment molecule spatial unit assignment := by
  constructor
  · intro computed
    unfold perceiveConformationAssignment? at computed
    cases selectedEq : perceiveConformation? molecule spatial unit with
    | none => simp [selectedEq] at computed
    | some selected =>
        have assignmentEq : assignment = selected.toAssignment unit := by
          exact Option.some.inj (by simpa [selectedEq] using computed.symm)
        exact ⟨selected,
          (perceiveConformation?_eq_some_iff
            molecule spatial unit selected).mp selectedEq,
          assignmentEq⟩
  · rintro ⟨selected, judged, rfl⟩
    have selectedEq :=
      (perceiveConformation?_eq_some_iff
        molecule spatial unit selected).mpr judged
    simp [perceiveConformationAssignment?, selectedEq]

/-- Evaluate every requested P-94 unit and erase duplicates caused by repeated requests. -/
def perceiveConformationAssignments (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (units : List P94ConformationUnit) :
    List P94ConformationAssignment :=
  (units.filterMap (perceiveConformationAssignment? molecule spatial)).eraseDups

/-- Independent batch meaning: some requested physical unit has the exact single-unit judgment. -/
def PracticalConformationBatchAssignmentJudgment
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (units : List P94ConformationUnit) (assignment : P94ConformationAssignment) : Prop :=
  ∃ unit ∈ units,
    PracticalConformationAssignmentJudgment molecule spatial unit assignment

theorem mem_perceiveConformationAssignments_iff
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (units : List P94ConformationUnit) (assignment : P94ConformationAssignment) :
    assignment ∈ perceiveConformationAssignments molecule spatial units ↔
      PracticalConformationBatchAssignmentJudgment
        molecule spatial units assignment := by
  rw [perceiveConformationAssignments, mem_eraseDups_iff_mem_lawful,
    List.mem_filterMap]
  exact exists_congr fun unit => and_congr_right fun _ =>
    perceiveConformationAssignment?_eq_some_iff
      molecule spatial unit assignment

theorem perceiveConformationAssignments_nodup
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (units : List P94ConformationUnit) :
    (perceiveConformationAssignments molecule spatial units).Nodup := by
  exact eraseDups_nodup_lawful _

/-- Every retained batch assignment has the pre-existing independent P-94 evidence package. -/
theorem perceiveConformationAssignments_member_independent
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (units : List P94ConformationUnit) (assignment : P94ConformationAssignment)
    (present : assignment ∈ perceiveConformationAssignments molecule spatial units) :
    ∃ evidence : P94ConformationEvidence Unit Unit,
      IndependentP94ConformationAssignment molecule [evidence] assignment := by
  rcases (mem_perceiveConformationAssignments_iff
    molecule spatial units assignment).mp present with
    ⟨unit, _, selected, judged, assignmentEq⟩
  have selectedEq :=
    (perceiveConformation?_eq_some_iff
      molecule spatial unit selected).mpr judged
  apply perceiveConformationAssignment?_some_independent
    molecule spatial unit assignment
  simp [perceiveConformationAssignment?, selectedEq, assignmentEq]

end BlueBookP94.UnifiedPracticalConformationPerception
end TetraStereo.OneCenter
