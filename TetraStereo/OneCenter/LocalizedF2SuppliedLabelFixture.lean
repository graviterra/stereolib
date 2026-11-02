import TetraStereo.OneCenter.AuthoritativeCIPGraph
import TetraStereo.OneCenter.LocalizedOccurrenceCarrier
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.F2SuppliedLabelFixture

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput




def element (z : Nat) (positive : 0 < z) (bounded : z ≤ 118) : PeriodicElement :=
  { atomicNumber := z, positive := positive, atMost118 := bounded }

def hydrogenElement : PeriodicElement := element 1 (by decide) (by decide)
def carbonElement : PeriodicElement := element 6 (by decide) (by decide)
def oxygenElement : PeriodicElement := element 8 (by decide) (by decide)

def atomOf (e : PeriodicElement) : SemanticAtom := { element := e }
def hydrogenAtom : SemanticAtom := atomOf hydrogenElement
def carbonAtom : SemanticAtom := atomOf carbonElement
def oxygenAtom : SemanticAtom := atomOf oxygenElement

def singleBond (a b : Nat) : SemanticInteraction :=
  { participants := [a, b], kind := .covalent 1 }

def sourceMolecule : SemanticMolecule where
  atoms := [
    carbonAtom,
    carbonAtom,
    hydrogenAtom,
    hydrogenAtom,
    carbonAtom,
    hydrogenAtom,
    carbonAtom,
    oxygenAtom,
    oxygenAtom,
    oxygenAtom,
    carbonAtom,
    hydrogenAtom,
    carbonAtom,
    hydrogenAtom,
    carbonAtom,
    oxygenAtom,
    oxygenAtom,
    oxygenAtom,
    carbonAtom,
    hydrogenAtom,
    carbonAtom,
    hydrogenAtom,
    carbonAtom,
    oxygenAtom,
    oxygenAtom,
    oxygenAtom,
    carbonAtom,
    hydrogenAtom
  ]
  interactions := [
    singleBond 0 2,
    singleBond 1 3,
    singleBond 0 4,
    singleBond 1 4,
    singleBond 4 5,
    singleBond 4 6,
    singleBond 6 7,
    singleBond 6 8,
    singleBond 6 9,
    singleBond 10 7,
    singleBond 10 8,
    singleBond 10 9,
    singleBond 10 11,
    singleBond 0 12,
    singleBond 1 12,
    singleBond 12 13,
    singleBond 12 14,
    singleBond 14 15,
    singleBond 14 16,
    singleBond 14 17,
    singleBond 18 15,
    singleBond 18 16,
    singleBond 18 17,
    singleBond 18 19,
    singleBond 0 20,
    singleBond 1 20,
    singleBond 20 21,
    singleBond 20 22,
    singleBond 22 23,
    singleBond 22 24,
    singleBond 22 25,
    singleBond 26 23,
    singleBond 26 24,
    singleBond 26 25,
    singleBond 26 27
  ]

def source : AuthoritativeChemicalInput := { molecule := sourceMolecule }

theorem source_structurallyWellFormed : source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by
    decide +kernel)

theorem source_graphReady : source.molecule.LocalizedCIPGraphReady :=
  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff source.molecule).mp (by
    decide +kernel)

assert_kernel_only TetraStereo.OneCenter.F2SuppliedLabelFixture.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.F2SuppliedLabelFixture.source_graphReady

def input : CertifiedLocalizedCIPInput where
  certified :=
    { input := source
      structurallyWellFormed := source_structurallyWellFormed }
  graphReady := source_graphReady

abbrev Atom := Fin 28

def atom (n : Fin 28) : Atom := n

def atom0 : Atom := ⟨0, by decide⟩
def atom1 : Atom := ⟨1, by decide⟩
def atom12 : Atom := ⟨12, by decide⟩
def atom20 : Atom := ⟨20, by decide⟩

theorem input_atomCount : input.certified.input.molecule.atomCount = 28 := rfl

def center12 : input.TetrahedralCenter := ⟨atom12, by decide +kernel⟩
def center20 : input.TetrahedralCenter := ⟨atom20, by decide +kernel⟩

inductive ExportedAuxLabel where
  | unknown
  | chiralR
  | chiralS
  | pseudoR
  | pseudoS
  deriving DecidableEq, Repr

/-- The source distinguishes `Unknown` from null/unassigned. This tagged layer preserves that
fact; the explicit adapter below projects into the current Lean comparator's smaller label type. -/

def root12ExportedAuxLabel (path : List Nat) : Option ExportedAuxLabel :=
  match path with
  | [12, 0] => some .chiralR
  | [12, 1] => some .chiralS
  | [12, 14] => some .pseudoS
  | [12, 0, 4] => some .chiralR
  | [12, 0, 20] => some .chiralR
  | [12, 1, 4] => some .chiralS
  | [12, 1, 20] => some .chiralS
  | [12, 0, 4, 1] => some .chiralR
  | [12, 0, 4, 6] => some .pseudoR
  | [12, 0, 20, 1] => some .chiralS
  | [12, 0, 20, 22] => some .pseudoS
  | [12, 1, 4, 0] => some .chiralR
  | [12, 1, 4, 6] => some .pseudoR
  | [12, 1, 20, 0] => some .chiralS
  | [12, 1, 20, 22] => some .pseudoS
  | [12, 14, 15, 18] => some .unknown
  | [12, 14, 16, 18] => some .unknown
  | [12, 14, 17, 18] => some .unknown
  | [12, 0, 4, 1, 20] => some .chiralS
  | [12, 0, 20, 1, 4] => some .chiralS
  | [12, 1, 4, 0, 20] => some .chiralR
  | [12, 1, 20, 0, 4] => some .chiralR
  | [12, 0, 4, 1, 20, 22] => some .pseudoS
  | [12, 0, 4, 6, 7, 10] => some .unknown
  | [12, 0, 4, 6, 8, 10] => some .unknown
  | [12, 0, 4, 6, 9, 10] => some .unknown
  | [12, 0, 20, 1, 4, 6] => some .pseudoR
  | [12, 0, 20, 22, 23, 26] => some .unknown
  | [12, 0, 20, 22, 24, 26] => some .unknown
  | [12, 0, 20, 22, 25, 26] => some .unknown
  | [12, 1, 4, 0, 20, 22] => some .pseudoS
  | [12, 1, 4, 6, 7, 10] => some .unknown
  | [12, 1, 4, 6, 8, 10] => some .unknown
  | [12, 1, 4, 6, 9, 10] => some .unknown
  | [12, 1, 20, 0, 4, 6] => some .pseudoR
  | [12, 1, 20, 22, 23, 26] => some .unknown
  | [12, 1, 20, 22, 24, 26] => some .unknown
  | [12, 1, 20, 22, 25, 26] => some .unknown
  | [12, 0, 4, 1, 20, 22, 23, 26] => some .unknown
  | [12, 0, 4, 1, 20, 22, 24, 26] => some .unknown
  | [12, 0, 4, 1, 20, 22, 25, 26] => some .unknown
  | [12, 0, 20, 1, 4, 6, 7, 10] => some .unknown
  | [12, 0, 20, 1, 4, 6, 8, 10] => some .unknown
  | [12, 0, 20, 1, 4, 6, 9, 10] => some .unknown
  | [12, 1, 4, 0, 20, 22, 23, 26] => some .unknown
  | [12, 1, 4, 0, 20, 22, 24, 26] => some .unknown
  | [12, 1, 4, 0, 20, 22, 25, 26] => some .unknown
  | [12, 1, 20, 0, 4, 6, 7, 10] => some .unknown
  | [12, 1, 20, 0, 4, 6, 8, 10] => some .unknown
  | [12, 1, 20, 0, 4, 6, 9, 10] => some .unknown
  | _ => none

def root20ExportedAuxLabel (path : List Nat) : Option ExportedAuxLabel :=
  match path with
  | [20, 0] => some .chiralR
  | [20, 1] => some .chiralS
  | [20, 22] => some .pseudoS
  | [20, 0, 4] => some .chiralR
  | [20, 0, 12] => some .chiralR
  | [20, 1, 4] => some .chiralS
  | [20, 1, 12] => some .chiralS
  | [20, 0, 4, 1] => some .chiralS
  | [20, 0, 4, 6] => some .pseudoR
  | [20, 0, 12, 1] => some .chiralR
  | [20, 0, 12, 14] => some .pseudoS
  | [20, 1, 4, 0] => some .chiralS
  | [20, 1, 4, 6] => some .pseudoR
  | [20, 1, 12, 0] => some .chiralR
  | [20, 1, 12, 14] => some .pseudoS
  | [20, 22, 23, 26] => some .unknown
  | [20, 22, 24, 26] => some .unknown
  | [20, 22, 25, 26] => some .unknown
  | [20, 0, 4, 1, 12] => some .chiralS
  | [20, 0, 12, 1, 4] => some .chiralS
  | [20, 1, 4, 0, 12] => some .chiralR
  | [20, 1, 12, 0, 4] => some .chiralR
  | [20, 0, 4, 1, 12, 14] => some .pseudoS
  | [20, 0, 4, 6, 7, 10] => some .unknown
  | [20, 0, 4, 6, 8, 10] => some .unknown
  | [20, 0, 4, 6, 9, 10] => some .unknown
  | [20, 0, 12, 1, 4, 6] => some .pseudoR
  | [20, 0, 12, 14, 15, 18] => some .unknown
  | [20, 0, 12, 14, 16, 18] => some .unknown
  | [20, 0, 12, 14, 17, 18] => some .unknown
  | [20, 1, 4, 0, 12, 14] => some .pseudoS
  | [20, 1, 4, 6, 7, 10] => some .unknown
  | [20, 1, 4, 6, 8, 10] => some .unknown
  | [20, 1, 4, 6, 9, 10] => some .unknown
  | [20, 1, 12, 0, 4, 6] => some .pseudoR
  | [20, 1, 12, 14, 15, 18] => some .unknown
  | [20, 1, 12, 14, 16, 18] => some .unknown
  | [20, 1, 12, 14, 17, 18] => some .unknown
  | [20, 0, 4, 1, 12, 14, 15, 18] => some .unknown
  | [20, 0, 4, 1, 12, 14, 16, 18] => some .unknown
  | [20, 0, 4, 1, 12, 14, 17, 18] => some .unknown
  | [20, 0, 12, 1, 4, 6, 7, 10] => some .unknown
  | [20, 0, 12, 1, 4, 6, 8, 10] => some .unknown
  | [20, 0, 12, 1, 4, 6, 9, 10] => some .unknown
  | [20, 1, 4, 0, 12, 14, 15, 18] => some .unknown
  | [20, 1, 4, 0, 12, 14, 16, 18] => some .unknown
  | [20, 1, 4, 0, 12, 14, 17, 18] => some .unknown
  | [20, 1, 12, 0, 4, 6, 7, 10] => some .unknown
  | [20, 1, 12, 0, 4, 6, 8, 10] => some .unknown
  | [20, 1, 12, 0, 4, 6, 9, 10] => some .unknown
  | _ => none

/-- Explicit projection to the current comparator language: source `Unknown` remains recorded in
`ExportedAuxLabel` and maps to `none` only at this adapter boundary. This is a projected
comparator probe, not evidence that the production source and Lean assign identical semantics to
Unknown. -/
def toLocalizedAuxLabel : ExportedAuxLabel → Option LocalizedAuxiliaryLabel
  | .unknown => none
  | .chiralR => some (.chiral .R)
  | .chiralS => some (.chiral .S)
  | .pseudoR => some (.pseudoasymmetric .r)
  | .pseudoS => some (.pseudoasymmetric .s)

end TetraStereo.OneCenter.F2SuppliedLabelFixture
