import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

/-- Number of Rules-1--5 equivalence groups in the certified adjacent partition. -/
def rule6GroupCount (adjacent : List (Option Ordering)) : Nat :=
  1 + (adjacent.filter fun decision => decision == some Ordering.gt).length

end TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
