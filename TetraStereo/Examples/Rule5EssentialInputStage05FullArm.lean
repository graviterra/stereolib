import TetraStereo.Examples.Rule5EssentialInputStage04OtherFact

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

def fullState : State discovery := fun occurrence =>
  if sameOccurrence occurrence source then some sourceLabel
  else if sameOccurrence occurrence other then some otherLabel
  else none

def withoutSource : State discovery := fun occurrence =>
  if sameOccurrence occurrence source then none else fullState occurrence

theorem withoutSource_differsOnlyAt :
    DiffersOnlyAt withoutSource fullState source := by
  intro other notEqual
  have different : sameOccurrence other source = false := by
    cases equal : sameOccurrence other source with
    | false => rfl
    | true => exact (notEqual ((sameOccurrence_eq_true_iff other source).mp equal)).elim
  simp [withoutSource, fullState, different]

def fullTargetFact : OccurrenceAuxFact :=
  { key :=
      { history := [1]
        provenance := .realAtom }
    atom := 1
    descriptor := .R
    uppercase := false
    priorityPositions := [1, 0, 2, 3] }

/-- The current framed arm decision, including its Rule-5 pseudo flag. -/
theorem fixture_full_arm_decision :
    FrameRuntime.decisionComplete? fixtureMolecule
      (fixtureProfile (canonicalCenterRoot 1)) false [sourceFact, otherFact] fuel
      (fixtureCenterCursor 3) (fixtureCenterCursor 6) =
      some { ordering := .gt, pseudo := true } := by decide +kernel

end TetraStereo.Examples.Rule5EssentialDependency
