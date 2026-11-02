import TetraStereo.Examples.Rule5EssentialInputStage12OtherInput

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem facts_keys_distinct : sourceFact.key ≠ otherFact.key := by decide

theorem fullState_inactive (occurrence : ProductionOccurrence)
    (differentSource : occurrence ≠ source) (differentOther : occurrence ≠ other) :
    fullState occurrence = none := by
  have sourceUnequal : sameOccurrence occurrence source = false := by
    cases equal : sameOccurrence occurrence source with
    | false => rfl
    | true =>
        exact (differentSource ((sameOccurrence_eq_true_iff occurrence source).mp equal)).elim
  have otherUnequal : sameOccurrence occurrence other = false := by
    cases equal : sameOccurrence occurrence other with
    | false => rfl
    | true =>
        exact (differentOther ((sameOccurrence_eq_true_iff occurrence other).mp equal)).elim
  simp [fullState, sourceUnequal, otherUnequal]

end TetraStereo.Examples.Rule5EssentialDependency
