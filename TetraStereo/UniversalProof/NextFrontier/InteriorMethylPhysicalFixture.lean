import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking

set_option autoImplicit false
set_option maxRecDepth 10000

/-! Independent literal physical fixture and genuine ancestry.
The compatibility namespace is retained. Cursor ranking transitively imports runtime
definitions, including SmilesTetrahedral. The runtime diagnostic assertions remain
in the separate InteriorMethylDepthCounterexample facade. -/

namespace TetraStereo.UniversalProof.InteriorMethylDepthCounterexample

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking

def carbon : AtomSpec := { element := .C, explicitHydrogens? := some 0 }
def hydrogen : AtomSpec := { element := .H, explicitHydrogens? := some 0 }
def fluorine : AtomSpec := { element := .F, explicitHydrogens? := some 0 }
def bond (source target : Nat) : RawBond :=
  { source := source, target := target, kind := .single }

def molecule : RawMolecule :=
  { atoms := [{ carbon with tetrahedral? := some .clockwise }, carbon, carbon,
      hydrogen, hydrogen, hydrogen, hydrogen, hydrogen, hydrogen, hydrogen, fluorine]
    bonds := [bond 0 1, bond 0 2, bond 1 3, bond 1 4, bond 1 5,
      bond 2 6, bond 2 7, bond 2 8, bond 0 9, bond 0 10]
    neighborOrder := [[1,2,9,10], [0,3,4,5], [0,6,7,8], [1], [1], [1],
      [2], [2], [2], [0], [0]] }

def tagOccurrence : CanonicalBranchNode := canonicalRoot 1 0
def incoming : CanonicalRerootCursor :=
  { node := canonicalCenterRoot 1, previous? := some tagOccurrence }
def outgoing : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 0, history := [2,0,1], provenance := .realAtom }
    previous? := some tagOccurrence }
def localLeft : CanonicalRerootCursor :=
  { node := canonicalRoot 0 1, previous? := some (canonicalCenterRoot 0) }
def localRight : CanonicalRerootCursor :=
  { node := canonicalRoot 0 2, previous? := some (canonicalCenterRoot 0) }

def swapMethyl : Nat → Nat
  | 1 => 2 | 2 => 1 | 3 => 6 | 6 => 3 | 4 => 7 | 7 => 4 | 5 => 8 | 8 => 5
  | n => n

-- Independent raw constitutional symmetry fixes the tagged center, H and F.
theorem identical_constitution :
    ((List.range 11).all fun a => decide
      (molecule.atomAt? a = molecule.atomAt? (swapMethyl a))) = true ∧
    ((List.range 11).all fun a => (List.range 11).all fun b => decide
      (molecule.bondOrder a b = molecule.bondOrder (swapMethyl a) (swapMethyl b))) = true := by
  decide +kernel

theorem raw_wellFormed : molecule.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide +kernel

theorem raw_valence : molecule.ValenceOK :=
  molecule.valenceOK?_eq_true_iff.mp (by decide +kernel)
theorem raw_saturated :
    (List.range 11).map molecule.usedValenceAt = [4,4,4,1,1,1,1,1,1,1,1] := by
  decide +kernel
theorem exact_written_rows : molecule.writtenNeighborExact? = true := by decide +kernel
theorem actual_tag_generated : CanonicalCenterTreeNode molecule 1 tagOccurrence :=
  .child .root (by decide +kernel)
theorem actual_incoming_generated : CanonicalCenterRerootCursor molecule 1 incoming :=
  .ascending .root (by decide +kernel)
theorem actual_outgoing_generated : CanonicalCenterRerootCursor molecule 1 outgoing :=
  .descending actual_tag_generated (by decide +kernel)
end TetraStereo.UniversalProof.InteriorMethylDepthCounterexample
