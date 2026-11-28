import TetraStereo.Engine.RingLigandTreeComparison

/-! Full constitutional priority on a directed pair of raw atom histories.
Both histories are newest-first on the original rooted occurrence tree. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingDeepHistoryPathOrder
open OneCenter RingRetainedChemicalTrace
open RingConstitutionalTreeInvariant (Shape)

abbrev Edge := List Nat × List Nat

/-- Retracing the original parent removes the head. Every other retained
bond extends the history, including a bond that closes the ring. -/
def advance (h : List Nat) (w : Nat) := if h[1]? = some w then h.tail else w :: h

/-- Remove only the incoming direction. A repeated atom is a terminal duplicate. -/
def children (m : RawMolecule) (e : Edge) : List Edge :=
  let hs := match e.2 with
    | [] => []
    | a :: t => if t.contains a then [] else
        ((m.writtenNeighbors a).filter fun n => e.1.head? != some n).map (advance (a :: t))
  hs.map fun h => (e.2,h)

def observe? (m : RawMolecule) (h : List Nat) (terminal : Bool) : Option Observation := do
  let a ← h.head?
  let recd ← m.atoms[a]?
  let z := recd.element.atomicNumber
  guard (z > 0)
  if h.tail.contains a then
    let origin := h.tail.reverse.idxOf a
    guard (terminal && origin ≤ m.atomCount)
    let mass ← CIPRule2MassData.rule2MassPico? z none
    return ⟨z,duplicateValue m.atomCount (some origin),mass⟩
  else
    let mass ← CIPRule2MassData.rule2MassPico? z recd.isotope?
    return ⟨z,duplicateValue m.atomCount none,mass⟩

def observation? (m : RawMolecule) (e : Edge) :=
  observe? m e.2 (children m e).isEmpty

def tree (m : RawMolecule) : (n : Nat) → Edge → Shape n
  | 0,_ => ()
  | n+1,e => (observation? m e,↑((children m e).map (tree m n)))

/-- The retained-tree depth suffices for both inward and outward directions. -/
def key? (m : RawMolecule) (previous current : List Nat) : Option Key :=
  let n := 2 * (m.atomCount + 1 + 1) + 1
  RingLigandTreeComparison.reconstruct n (tree m n (previous,current))

def word? (m : RawMolecule) (previous current : List Nat) :=
  (key? m previous current).map RingRetainedChemicalPreorder.orderWord

def compare? (m : RawMolecule) (a b : Edge) : Option Ordering := do
  pure (compareKeys (← key? m a.1 a.2) (← key? m b.1 b.2))

end TetraStereo.Engine.RingDeepHistoryPathOrder
