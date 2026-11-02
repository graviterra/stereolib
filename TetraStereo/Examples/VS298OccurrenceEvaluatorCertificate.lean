import TetraStereo.Examples.VS298OccurrenceStateFactCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter

/-- Direct production recomputation agrees at both selected occurrence frames. -/
theorem productionEvaluatorEquations :
    (occurrenceFact? molecule fuel state leftSource,
      occurrenceFact? molecule fuel state rightSource) =
    (some leftExpectedFact, some rightExpectedFact) := by decide

theorem leftOccurrenceFact :
    occurrenceFact? molecule fuel state leftSource = some leftExpectedFact :=
  congrArg Prod.fst productionEvaluatorEquations

theorem rightOccurrenceFact :
    occurrenceFact? molecule fuel state rightSource = some rightExpectedFact :=
  congrArg Prod.snd productionEvaluatorEquations

end TetraStereo.Examples.VS298
