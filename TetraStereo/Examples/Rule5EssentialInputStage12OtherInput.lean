import TetraStereo.Examples.Rule5EssentialInputStage11OtherFrame

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

theorem other_input_accepted : inputFact? fullState other = some otherFact := by
  have notSource : sameOccurrence other source = false := by
    cases equal : sameOccurrence other source with
    | false => rfl
    | true =>
        exact (source_ne_other ((sameOccurrence_eq_true_iff other source).mp equal).symm).elim
  have stateEq : fullState other = some otherLabel := by
    have self : sameOccurrence other other = true :=
      (sameOccurrence_eq_true_iff other other).2 rfl
    simp only [fullState, notSource, self, Bool.false_eq_true, ↓reduceIte]
  simp [inputFact?, stateEq, otherLabel, labelOfOrdinaryFact,
    otherFact, factKey, other_node, ligandRootNode, other_ligand_atom, descriptorOfFact,
    descriptorSense, canonicalOccurrenceKey, RawMolecule.canonicalRoot]

end TetraStereo.Examples.Rule5EssentialDependency
