import TetraStereo.Examples.Rule5EssentialRuntimeFixture

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

def centerOne : Fin molecule.atomCount := ⟨1, by decide⟩
def root : Root molecule := ⟨centerOne, by decide⟩

@[simp] theorem root_center_atom : (centerAtom root).val = 1 := rfl

theorem discoveryAvailable : (discoverAll? molecule).isSome := by
  rw [molecule_eq_fixture]
  decide +kernel

def discovery : Discovery molecule :=
  (discoverAll? molecule).get discoveryAvailable

abbrev ProductionOccurrence :=
  ProductionCIPOccurrenceDiscovery.Occurrence discovery

end TetraStereo.Examples.Rule5EssentialDependency
