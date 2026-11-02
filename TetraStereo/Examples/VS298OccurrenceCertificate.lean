import TetraStereo.OneCenter.ProductionCIPOccurrenceDiscovery

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery

def smiles : String := "Cl[C@H]1C[C@]2(C1)C[C@H](C2)Cl"

def raw : RawMolecule :=
  match parseOpenSMILES smiles with
  | .ok molecule => molecule
  | .error _ => { atoms := [], bonds := [] }

def result := normalizeRawMolecule raw
def molecule := result.parsed.withExplicitHydrogens
def fuel := analysisFuel molecule

def centerOne : Fin molecule.atomCount := ⟨1, by decide⟩

def root : Root molecule :=
  ⟨centerOne, by decide⟩

/-- Exhaustive executable discovery succeeds for every molecule-derived final root.  Using the
total `Discovery` carrier below prevents the regression from silently selecting only center 1. -/
theorem discoveryAvailable : (discoverAll? molecule).isSome := by decide

/-- The complete molecule-derived occurrence discovery. -/
def discovery : Discovery molecule :=
  (discoverAll? molecule).get discoveryAvailable

/-- Center 1 is obtained from the exhaustive family, not supplied as a caller-selected family. -/
def centerDiscovery : CenterDiscovery molecule root :=
  discovery.center root

/-- The stored center is the result of the concrete production center-discovery execution. -/
theorem centerDiscovery_executable :
    discoverCenter? molecule root = some centerDiscovery :=
  discovery.center_discovered root

end TetraStereo.Examples.VS298
