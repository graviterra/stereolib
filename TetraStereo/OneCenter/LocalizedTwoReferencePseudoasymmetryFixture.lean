import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline
import TetraStereo.KernelOnly

set_option autoImplicit false




























namespace TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture

open TetraStereo.OneCenter

private def element (z : Nat) (p : 0 < z) (b : z ≤ 118) : PeriodicElement :=
  { atomicNumber := z, positive := p, atMost118 := b }
def carbon : PeriodicElement := element 6 (by decide) (by decide)
def hydrogen : PeriodicElement := element 1 (by decide) (by decide)
def nitrogen : PeriodicElement := element 7 (by decide) (by decide)
def fluorine : PeriodicElement := element 9 (by decide) (by decide)
def chlorine : PeriodicElement := element 17 (by decide) (by decide)
def bromine : PeriodicElement := element 35 (by decide) (by decide)
def atom (e : PeriodicElement) : SemanticAtom := { element := e }
def singleBond (l r : Nat) : SemanticInteraction := { participants := [l, r], kind := .covalent 1 }

/-- Atom `0` is the centre; `1 = H`, `2 = Cl`; `3` and `18` are the arm nitrogens; the `A` centres
are `4, 11 | 19, 26` and the `B` centres `7, 14 | 22, 29`. -/
def source : AuthoritativeChemicalInput :=
  { molecule := { atoms := [carbon, hydrogen, chlorine, nitrogen, carbon, hydrogen, fluorine, carbon, hydrogen, chlorine, bromine, carbon, hydrogen, fluorine, carbon, hydrogen, chlorine, bromine, nitrogen, carbon, hydrogen, fluorine, carbon, hydrogen, chlorine, bromine, carbon, hydrogen, fluorine, carbon, hydrogen, chlorine, bromine].map atom,
                   interactions := [singleBond 0 1, singleBond 0 2, singleBond 0 3, singleBond 3 4, singleBond 4 5, singleBond 4 6, singleBond 4 7, singleBond 7 8, singleBond 7 9, singleBond 7 10, singleBond 3 11, singleBond 11 12, singleBond 11 13, singleBond 11 14, singleBond 14 15, singleBond 14 16, singleBond 14 17, singleBond 0 18, singleBond 18 19, singleBond 19 20, singleBond 19 21, singleBond 19 22, singleBond 22 23, singleBond 22 24, singleBond 22 25, singleBond 18 26, singleBond 26 27, singleBond 26 28, singleBond 26 29, singleBond 29 30, singleBond 29 31, singleBond 29 32] },
     spatial? := some { positions := [{ x := 0, y := 0, z := 0 },
 { x := 0, y := 0, z := 150 },
 { x := 0, y := -141, z := -50 },
 { x := 130, y := 65, z := -39 },
 { x := 86, y := 116, z := 95 },
 { x := 101, y := -33, z := 101 },
 { x := -17, y := 152, z := -8 },
 { x := 218, y := 178, z := 58 },
 { x := 174, y := 230, z := 192 },
 { x := 116, y := 213, z := -45 },
 { x := 233, y := 28, z := 65 },
 { x := 25, y := 98, z := -141 },
 { x := 60, y := 221, z := -64 },
 { x := 147, y := 45, z := -210 },
 { x := -28, y := -7, z := -47 },
 { x := -10, y := -67, z := -183 },
 { x := -125, y := 107, z := -55 },
 { x := 104, y := 43, z := 3 },
 { x := -130, y := 65, z := -39 },
 { x := -86, y := 116, z := 95 },
 { x := -101, y := -33, z := 101 },
 { x := 17, y := 152, z := -8 },
 { x := -218, y := 178, z := 58 },
 { x := -174, y := 230, z := 192 },
 { x := -116, y := 213, z := -45 },
 { x := -233, y := 28, z := 65 },
 { x := -25, y := 98, z := -141 },
 { x := -60, y := 221, z := -64 },
 { x := -147, y := 45, z := -210 },
 { x := 28, y := -7, z := -47 },
 { x := 10, y := -67, z := -183 },
 { x := 125, y := 107, z := -55 },
 { x := -104, y := 43, z := 3 }] } }

theorem source_structurallyWellFormed : source.structurallyWellFormed? = true := by
  decide +kernel

theorem source_localizedGraphReady : source.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

theorem source_noDoubleTest : source.molecule.noLocalizedDoubleBondRecords? = true := by
  decide +kernel

def certifiedSource : CertifiedAuthoritativeChemicalInput :=
  { input := source,
     structurallyWellFormed :=
       (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
         source_structurallyWellFormed }

def localizedSource : CertifiedLocalizedCIPInput :=
  { certified := certifiedSource,
     graphReady :=
       (certifiedSource.input.molecule.localizedCIPGraphReady?_eq_true_iff).mp
         source_localizedGraphReady }

/-- The actual runtime input of the localized universal reference pipeline. -/
def input : LocalizedUniversalReference.Input := { certified := localizedSource }

/-- **Admission.**  The real `admitSource?` pipeline returns exactly the constructed input. -/
theorem admission : LocalizedUniversalReference.admitSource? source = some input := rfl

end TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture.admission
