import TetraStereo.Engine.RingCarbonReport
import TetraStereo.Engine.CentresSpiroSource
import TetraStereo.Examples.LocalizedChemicalRingSpiroProjection
import TetraStereo.Examples.BlueBookRule4aSource
import TetraStereo.Examples.BlueBookCyclobutanediol

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option Elab.async false

namespace TetraStereo.Examples.BlueBookCarbonReports
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority

/-- The four source carbons in the numbered ring. The two methines have
a lowercase descriptor; the two methylenes each have two identical H atoms. -/
def diolExpected (hand : PseudoRS) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  [(0,some (.pseudoasymmetric hand)),(1,none),(2,some (.pseudoasymmetric hand)),(3,none)]

def diolReport (g : Geometry) :=
  (classifyDiscoveredRingCarbons? BlueBookCyclobutanediol.molecule g 2 2).map (·.labels)

/-- All four bonds at C0 are already materialized. An extra bracket H would
raise that carbon's valence demand to five. -/
private def extraHydrogen : RawMolecule :=
  let m := BlueBookCyclobutanediol.molecule
  {m with atoms := m.atoms.modify 0 fun atom => {atom with explicitHydrogens? := some 1}}

theorem rejects_fifth_bond :
    extraHydrogen.usedValenceAt 0 = 5 ∧ saturatedWithHalogens extraHydrogen = false ∧
    (classifyDiscoveredRingCarbons? extraHydrogen BlueBookCyclobutanediol.geometry 2 2).isNone = true := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel⟩

theorem published_diol :
    diolReport BlueBookCyclobutanediol.geometry = some (diolExpected .r) ∧
    diolReport (mirror BlueBookCyclobutanediol.geometry) = some (diolExpected .r) ∧
    diolReport BlueBookCyclobutanediol.invertedThird = some (diolExpected .s) := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

/-- All eleven carbons in the numbering of the P-92.5.1 digraph,
including the freshly rooted nonstereogenic center C5. -/
def alcoholExpected : List (Nat × Option LocalizedAuxiliaryLabel) :=
  [(1,none),(2,some (.chiral .R)),(3,some (.pseudoasymmetric .s)),(4,some (.chiral .S)),
   (5,none),(6,some (.chiral .R)),(7,none),(8,some (.chiral .S)),(9,none),
   (10,some (.chiral .R)),(11,none)]

def alcoholReport (g : Geometry) :=
  (classifyDiscoveredRingCarbons? BlueBookRule4aSource.molecule g 3 1).map (·.labels)

private def alcoholLabel (i : Nat) := (alcoholExpected.lookup i).join

private def alcoholRow (i : Nat) :=
  (RingCarbonReport.atCarbon? BlueBookRule4aSource.molecule BlueBookRule4aSource.geometry
    3 (fun _ => none) (fun _ => 1) i).map RingCarbonReport.Verdict.label

theorem published_alcohol : alcoholReport BlueBookRule4aSource.geometry = some alcoholExpected := by
  have carbonIds : RingCarbonReport.carbons BlueBookRule4aSource.molecule =
      [1,2,3,4,5,6,7,8,9,10,11] := by decide +kernel
  have row (i : Nat) (hi : i ∈ RingCarbonReport.carbons BlueBookRule4aSource.molecule) :
      alcoholRow i = some (alcoholLabel i) := by
    rw [carbonIds] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  exact (classifyRingCarbons?_labels_of_rows alcoholLabel
    BlueBookRule4aSource.constitution_at_four.1 row).trans (by rw [carbonIds]; rfl)

def spiroExpected (h : RS) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  [(0,some (.chiral h)),(2,none),(3,none),(4,none),(6,none),(7,none),(8,none)]

def spiroGeometry : Geometry := fun i => LocalizedChemicalRingSpiroProjection.spatial.positions[i]?

/-- All seven carbon sites of the published 1,6-dioxaspiro[4.4]nonane.
The central carbon uses the choices in the original two-pair frame. -/
theorem published_spiro :
    (classifyDiscoveredRingCarbons? CentresRing.SpiroSource.molecule spiroGeometry 1 1).map
      (·.labels) = some (spiroExpected .R) ∧
    (classifyDiscoveredRingCarbons? CentresRing.SpiroSource.molecule (mirror spiroGeometry) 1 1).map
      (·.labels) = some (spiroExpected .S) := by
  constructor <;> decide +kernel

end TetraStereo.Examples.BlueBookCarbonReports
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReports.published_diol
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReports.published_alcohol
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReports.published_spiro
assert_kernel_only TetraStereo.Examples.BlueBookCarbonReports.rejects_fifth_bond
