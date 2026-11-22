import TetraStereo.Engine.RingLocalIsotopeReport
import TetraStereo.Examples.RingThiiraneCoverage

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

namespace TetraStereo.Examples.RingThiiraneIsotope
open OneCenter Engine LocalizedGenericMarkedRecalculation RingChemicalPriority
open RingThiiraneCoverage LocalIsotopeCarbonReport

/-- The actual four arms of the deuterated ring carbon, in descending priority. -/
def chdRanking := (ranking? deuterated 2).get (by decide +kernel)

theorem ordered_sites : chdRanking.order = [3,1,8,9] := by decide +kernel

def deuterium := chdRanking.arms[2]'(by decide +kernel)
def hydrogen := chdRanking.arms[3]'(by decide +kernel)

/-- Ordinary H and D have the exact AME masses (in picodaltons) used by
the checker. Their complete constitutional observations coincide at every depth. -/
theorem deuterium_over_hydrogen :
    deuterium.cursor.node.history.reverse = [2,8] ∧ hydrogen.cursor.node.history.reverse = [2,9] ∧
    deuterium.atom.isotope? = some 2 ∧ hydrogen.atom.isotope? = none ∧
    deuterium.mass? = some 2014101777844 ∧ hydrogen.mass? = some 1007825031898 ∧
    TerminalHigher deuterium hydrogen ∧
    ∀ d, IsotopePriority.Isomorphic deuterated [2] (d+1) deuterium.cursor hydrogen.cursor := by
  have higher : TerminalHigher deuterium hydrogen := by decide +kernel
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,higher,(terminal_priority higher).1⟩

theorem isotope_readbacks :
    Recursive.geometric (LocalizedChemicalRingPhysicalSense.inputGeometry isotopeInput.certified)
      chdRanking.order chdRanking.order = some ⟨.S,.R⟩ := by decide +kernel

/-- The independent hydrogen-pair and strict Rule 1a witnesses at the
other carbons still apply to the isotopically substituted molecule. -/
theorem other_carbons :
    (RingCarbonReport.hydrogens? deuterated 0).isSome = true ∧
    atomicOrder? deuterated [1] 2 = some [3,2,0,7] ∧
    Recursive.geometric (LocalizedChemicalRingPhysicalSense.inputGeometry isotopeInput.certified)
      [3,2,0,7] [3,2,0,7] = some ⟨.S,.R⟩ := by decide +kernel

/-- Every carbon has a verdict, including the two distinct uppercase S
assignments and the methyl carbon's pair of constitutionally equivalent hydrogens. -/
theorem all_carbon_verdicts :
    (LocalIsotopeCarbonReport.check isotopeInput 2).map Report.labels =
      some [(0,none),(1,some (.chiral .S)),(2,some (.chiral .S))] := by decide +kernel

/-- The same ring with explicit protium at atom 8 and ordinary hydrogen at atom 9. -/
def protiated : RawMolecule := { molecule with
  atoms := molecule.atoms.set 8 { AtomSpec.aliphatic .H with isotope? := some 1 } }

def protiumInput := (LocalizedChemicalRing.admitRawSpatial? protiated spatial).get (by decide +kernel)

theorem protium_admitted : LocalizedChemicalRing.admitRawSpatial? protiated spatial = some protiumInput :=
  (Option.some_get _).symm

def protiumTie := (hydrogenTie? protiated 2).get (by decide +kernel)

/-- Source notation differs at the two real sites. Their complete observations
give the same tabulated mass and the official comparator proves equality. -/
theorem protium_spelling :
    protiated.atoms[8]? ≠ protiated.atoms[9]? ∧
    ({protiumTie.left.arm.cursor.node.atom,protiumTie.right.arm.cursor.node.atom} : Finset Nat) = {8,9} ∧
    protiumTie.left.observation.sourceMass = 1007825031898 ∧
    protiumTie.right.observation.sourceMass = 1007825031898 ∧
    (RingCarbonReport.hydrogens? protiated 2).isNone = true ∧
    (AtomicCarbonReport.check protiumInput 2).isNone = true := by decide +kernel

theorem protium_verdicts :
    (LocalIsotopeCarbonReport.check protiumInput 2).map Report.labels =
      some [(0,none),(1,some (.chiral .S)),(2,none)] := by decide +kernel

end TetraStereo.Examples.RingThiiraneIsotope

assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.ordered_sites
assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.deuterium_over_hydrogen
assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.isotope_readbacks
assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.all_carbon_verdicts
assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.other_carbons
assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.protium_admitted
assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.protium_spelling
assert_kernel_only TetraStereo.Examples.RingThiiraneIsotope.protium_verdicts
