import TetraStereo.Examples.VS298OccurrenceFactDefinitions

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter

/-- The production occurrence scheduler retains both root-relative facts. -/
theorem productionStateFactEquations :
    (state.factAt? leftSource, state.factAt? rightSource) =
      (some leftExpectedFact, some rightExpectedFact) := by decide

theorem leftFact : state.factAt? leftSource = some leftExpectedFact :=
  congrArg Prod.fst productionStateFactEquations

theorem rightFact : state.factAt? rightSource = some rightExpectedFact :=
  congrArg Prod.snd productionStateFactEquations

end TetraStereo.Examples.VS298
