import TetraStereo.OneCenter.P94PracticalExecutableCarbohydrateCarrierSelection
import TetraStereo.OneCenter.P94PracticalExecutableCrownSelection
import TetraStereo.OneCenter.P94PracticalExecutableHalfChairSelection
import TetraStereo.OneCenter.P94PracticalExecutableRingSelection

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

namespace BlueBookP94.UnifiedPracticalConformationPerception

open PracticalCarbohydrateCarrierSelection
open PracticalCrownSelection
open PracticalHalfChairSelection
open PracticalRingSelection

/-!
# Unified practical P-94 ring-conformation perception

Specialized source rules take precedence over the generic ring-plane families: a perceived
carbohydrate five-ring twist is tried before ordinary envelope perception, and a monounsaturated
six-ring half-chair is tried before chair/boat perception. Crown and tub carriers have disjoint
typed routes. Every fall-through is retained in the independent judgment.
-/

inductive PracticalConformationSelection where
  | carbohydrateTwist (selected : SelectedCarbohydrateTwist)
  | halfChair (selected : SelectedHalfChair)
  | crown (selected : SelectedCrown)
  | ringPlane (selected : SelectedRingPlane)
  deriving DecidableEq, Repr

def PracticalConformationSelection.toAssignment
    (unit : P94ConformationUnit) : PracticalConformationSelection → P94ConformationAssignment
  | .carbohydrateTwist _ => { unit := unit, descriptor := .twist }
  | .halfChair _ => { unit := unit, descriptor := .halfChair }
  | .crown _ => { unit := unit, descriptor := .crown }
  | .ringPlane selected => { unit := unit, descriptor := selected.descriptor }

def perceiveConformation? (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) : Option PracticalConformationSelection :=
  match unit.kind with
  | .fiveMemberedRing =>
      match automaticCarbohydrateTwistSelection? molecule spatial unit with
      | some selected => some (.carbohydrateTwist selected)
      | none => (automaticRingSelection? molecule spatial unit).map .ringPlane
  | .sixMemberedRing =>
      match automaticHalfChairSelection? molecule spatial unit with
      | some selected => some (.halfChair selected)
      | none =>
          if halfChairCarrier? molecule unit then none
          else (automaticRingSelection? molecule spatial unit).map .ringPlane
  | .crownRing =>
      (automaticCrownSelection? molecule spatial unit).map .crown
  | .eightMemberedTubRing =>
      (automaticRingSelection? molecule spatial unit).map .ringPlane
  | .wholeMoleculeConformation | .torsionAxis | .bicyclicBridge => none

inductive PracticalConformationPerceptionJudgment
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit) : PracticalConformationSelection → Prop
  | carbohydrateTwist {selected}
      (kind : unit.kind = .fiveMemberedRing)
      (judged : AutomaticCarbohydrateTwistSelectionJudgment
        molecule spatial unit selected) :
      PracticalConformationPerceptionJudgment molecule spatial unit
        (.carbohydrateTwist selected)
  | fiveRingPlane {selected}
      (kind : unit.kind = .fiveMemberedRing)
      (specializedRefused : automaticCarbohydrateTwistSelection? molecule spatial unit = none)
      (judged : AutomaticRingSelectionJudgment molecule spatial unit selected) :
      PracticalConformationPerceptionJudgment molecule spatial unit (.ringPlane selected)
  | halfChair {selected}
      (kind : unit.kind = .sixMemberedRing)
      (judged : AutomaticHalfChairSelectionJudgment molecule spatial unit selected) :
      PracticalConformationPerceptionJudgment molecule spatial unit (.halfChair selected)
  | sixRingPlane {selected}
      (kind : unit.kind = .sixMemberedRing)
      (specializedRefused : automaticHalfChairSelection? molecule spatial unit = none)
      (carrierInapplicable : halfChairCarrier? molecule unit = false)
      (judged : AutomaticRingSelectionJudgment molecule spatial unit selected) :
      PracticalConformationPerceptionJudgment molecule spatial unit (.ringPlane selected)
  | crown {selected}
      (kind : unit.kind = .crownRing)
      (judged : PracticalCrownSelectionJudgment molecule spatial unit selected) :
      PracticalConformationPerceptionJudgment molecule spatial unit (.crown selected)
  | tub {selected}
      (kind : unit.kind = .eightMemberedTubRing)
      (judged : AutomaticRingSelectionJudgment molecule spatial unit selected) :
      PracticalConformationPerceptionJudgment molecule spatial unit (.ringPlane selected)

theorem perceiveConformation?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (selected : PracticalConformationSelection) :
    perceiveConformation? molecule spatial unit = some selected ↔
      PracticalConformationPerceptionJudgment molecule spatial unit selected := by
  constructor
  · intro computed
    cases kindEq : unit.kind with
    | fiveMemberedRing =>
        cases specializedEq : automaticCarbohydrateTwistSelection? molecule spatial unit with
        | none =>
            cases generalEq : automaticRingSelection? molecule spatial unit with
            | none => simp [perceiveConformation?, kindEq, specializedEq, generalEq] at computed
            | some general =>
                have selectedEq : selected = .ringPlane general := by
                  simpa [perceiveConformation?, kindEq, specializedEq, generalEq] using computed.symm
                subst selected
                exact .fiveRingPlane kindEq specializedEq
                  ((automaticRingSelection?_eq_some_iff molecule spatial unit general).mp generalEq)
        | some specialized =>
            have selectedEq : selected = .carbohydrateTwist specialized := by
              simpa [perceiveConformation?, kindEq, specializedEq] using computed.symm
            subst selected
            exact .carbohydrateTwist kindEq
              ((automaticCarbohydrateTwistSelection?_eq_some_iff
                molecule spatial unit specialized).mp specializedEq)
    | sixMemberedRing =>
        cases specializedEq : automaticHalfChairSelection? molecule spatial unit with
        | none =>
            cases carrierEq : halfChairCarrier? molecule unit with
            | false =>
                cases generalEq : automaticRingSelection? molecule spatial unit with
                | none =>
                    simp [perceiveConformation?, kindEq, specializedEq,
                      carrierEq, generalEq] at computed
                | some general =>
                    have selectedEq : selected = .ringPlane general := by
                      simpa [perceiveConformation?, kindEq, specializedEq,
                        carrierEq, generalEq] using computed.symm
                    subst selected
                    exact .sixRingPlane kindEq specializedEq carrierEq
                      ((automaticRingSelection?_eq_some_iff
                        molecule spatial unit general).mp generalEq)
            | true =>
                simp [perceiveConformation?, kindEq, specializedEq,
                  carrierEq] at computed
        | some specialized =>
            have selectedEq : selected = .halfChair specialized := by
              simpa [perceiveConformation?, kindEq, specializedEq] using computed.symm
            subst selected
            exact .halfChair kindEq
              ((automaticHalfChairSelection?_eq_some_iff
                molecule spatial unit specialized).mp specializedEq)
    | crownRing =>
        cases crownEq : automaticCrownSelection? molecule spatial unit with
        | none => simp [perceiveConformation?, kindEq, crownEq] at computed
        | some crown =>
            have selectedEq : selected = .crown crown := by
              simpa [perceiveConformation?, kindEq, crownEq] using computed.symm
            subst selected
            exact .crown kindEq
              ((automaticCrownSelection?_eq_some_iff molecule spatial unit crown).mp crownEq)
    | eightMemberedTubRing =>
        cases tubEq : automaticRingSelection? molecule spatial unit with
        | none => simp [perceiveConformation?, kindEq, tubEq] at computed
        | some tub =>
            have selectedEq : selected = .ringPlane tub := by
              simpa [perceiveConformation?, kindEq, tubEq] using computed.symm
            subst selected
            exact .tub kindEq
              ((automaticRingSelection?_eq_some_iff molecule spatial unit tub).mp tubEq)
    | wholeMoleculeConformation | torsionAxis | bicyclicBridge =>
        simp [perceiveConformation?, kindEq] at computed
  · intro judged
    cases judged with
    | carbohydrateTwist kind judged =>
        have selectedEq := (automaticCarbohydrateTwistSelection?_eq_some_iff
          molecule spatial unit _).mpr judged
        simp [perceiveConformation?, kind, selectedEq]
    | fiveRingPlane kind refused judged =>
        have selectedEq := (automaticRingSelection?_eq_some_iff
          molecule spatial unit _).mpr judged
        simp [perceiveConformation?, kind, refused, selectedEq]
    | halfChair kind judged =>
        have selectedEq := (automaticHalfChairSelection?_eq_some_iff
          molecule spatial unit _).mpr judged
        simp [perceiveConformation?, kind, selectedEq]
    | sixRingPlane kind refused carrierInapplicable judged =>
        have selectedEq := (automaticRingSelection?_eq_some_iff
          molecule spatial unit _).mpr judged
        simp [perceiveConformation?, kind, refused, carrierInapplicable, selectedEq]
    | crown kind judged =>
        have selectedEq := (automaticCrownSelection?_eq_some_iff
          molecule spatial unit _).mpr judged
        simp [perceiveConformation?, kind, selectedEq]
    | tub kind judged =>
        have selectedEq := (automaticRingSelection?_eq_some_iff
          molecule spatial unit _).mpr judged
        simp [perceiveConformation?, kind, selectedEq]

theorem perceiveConformation?_eq_none_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    perceiveConformation? molecule spatial unit = none ↔
      ¬∃ selected, PracticalConformationPerceptionJudgment molecule spatial unit selected := by
  rw [← not_iff_not]
  simp only [not_not, Option.ne_none_iff_isSome, Option.isSome_iff_exists]
  exact exists_congr fun selected =>
    perceiveConformation?_eq_some_iff molecule spatial unit selected

/-- A recognized monounsaturated six-ring belongs to the half-chair route. If its exact geometry
cannot be resolved, the unified selector refuses instead of reclassifying it as chair or boat. -/
theorem perceiveConformation?_eq_none_of_halfChairCarrier_of_unresolved
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (unit : P94ConformationUnit)
    (kind : unit.kind = .sixMemberedRing)
    (carrier : halfChairCarrier? molecule unit = true)
    (unresolved : automaticHalfChairSelection? molecule spatial unit = none) :
    perceiveConformation? molecule spatial unit = none := by
  simp [perceiveConformation?, kind, carrier, unresolved]

def perceiveConformationAssignment? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit) :
    Option P94ConformationAssignment :=
  (perceiveConformation? molecule spatial unit).map (·.toAssignment unit)

theorem perceiveConformationAssignment?_some_independent (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (assignment : P94ConformationAssignment)
    (computed : perceiveConformationAssignment? molecule spatial unit = some assignment) :
    ∃ evidence : P94ConformationEvidence Unit Unit,
      IndependentP94ConformationAssignment molecule [evidence] assignment := by
  cases selectedEq : perceiveConformation? molecule spatial unit with
  | none => simp [perceiveConformationAssignment?, selectedEq] at computed
  | some selected =>
      have assignmentEq : selected.toAssignment unit = assignment := by
        exact Option.some.inj (by simpa [perceiveConformationAssignment?, selectedEq] using computed)
      have judged := (perceiveConformation?_eq_some_iff
        molecule spatial unit selected).mp selectedEq
      cases judged with
      | carbohydrateTwist kind judged =>
          have underlying := (automaticCarbohydrateTwistSelection?_eq_some_iff
            molecule spatial unit _).mpr judged
          apply automaticCarbohydrateTwistAssignment?_some_independent molecule spatial unit assignment
          simpa [automaticCarbohydrateTwistAssignment?, underlying] using assignmentEq
      | fiveRingPlane kind refused judged =>
          have underlying := (automaticRingSelection?_eq_some_iff
            molecule spatial unit _).mpr judged
          apply automaticRingAssignment?_some_independent molecule spatial unit assignment
          simpa [automaticRingAssignment?, underlying] using assignmentEq
      | halfChair kind judged =>
          have underlying := (automaticHalfChairSelection?_eq_some_iff
            molecule spatial unit _).mpr judged
          apply automaticHalfChairAssignment?_some_independent molecule spatial unit assignment
          simpa [automaticHalfChairAssignment?, underlying] using assignmentEq
      | sixRingPlane kind refused carrierInapplicable judged =>
          have underlying := (automaticRingSelection?_eq_some_iff
            molecule spatial unit _).mpr judged
          apply automaticRingAssignment?_some_independent molecule spatial unit assignment
          simpa [automaticRingAssignment?, underlying] using assignmentEq
      | crown kind judged =>
          have underlying := (automaticCrownSelection?_eq_some_iff
            molecule spatial unit _).mpr judged
          apply automaticCrownAssignment?_some_independent molecule spatial unit assignment
          simpa [automaticCrownAssignment?, underlying] using assignmentEq
      | tub kind judged =>
          have underlying := (automaticRingSelection?_eq_some_iff
            molecule spatial unit _).mpr judged
          apply automaticRingAssignment?_some_independent molecule spatial unit assignment
          simpa [automaticRingAssignment?, underlying] using assignmentEq

end BlueBookP94.UnifiedPracticalConformationPerception

end TetraStereo.OneCenter
