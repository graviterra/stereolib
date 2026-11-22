import TetraStereo.Examples.RingRemoteIsotope
import TetraStereo.Examples.BlueBookRule4aSource

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false

namespace TetraStereo.Examples.RingVerifiedAbsence
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority Recursive

/-- Starting with enantiomorphic isotope-bearing cyclopentyl arms, reflect
the right arm a second time. Both now supply the same hand at their first
carbon without changing any atom, isotope, bond or central coordinate. -/
def sameHandGeometry : Geometry := fun i =>
  if i < 17 then RingRemoteIsotope.pairedGeometry i
  else (RingRemoteIsotope.pairedGeometry i).map fun p => ⟨p.x,p.y,-p.z⟩

private def pairHints (_ : List Nat) : Option Recursive.Frame :=
  some ⟨.five,1,3,17,2,fun i => if i < 3 then i else if i < 17 then i+14 else i-14,false⟩

private def pairedResult (g : Geometry) :=
  (RingAuxiliaryInventory.classify? RingRemoteIsotope.paired g pairHints (fun _ => 1) 2 [1,0]).map
    (·.reading)

/-- F is the original root. Both chemical arms derive the same remote-isotope
R, proving absence at the shared CHF carbon. Replacing the right arm by its
enantiomorph creates a pseudoasymmetric center at the very same occurrence. -/
theorem retained_absence_and_opposed_control :
    pairedResult sameHandGeometry = some none ∧
    pairedResult RingRemoteIsotope.pairedGeometry = some (some ⟨.S,.S⟩) := by
  constructor <;> decide +kernel

private def compactId : Nat → Nat
  | 32 => 19 | 33 => 22 | 34 => 25 | 35 => 28 | i => i

private def sourceId : Nat → Nat
  | 19 => 32 | 22 => 33 | 25 => 34 | 28 => 35 | i => i

/-- Constructed cyclic analogue of the P-92.5.1 control. Joining C1–C9
and C7–C11 closes a five-membered ring on each side of C4. Delete one H
from each newly bonded carbon and compact the remaining hydrogen indices.
All source heavy-atom identifiers and their configurations are retained. -/
def molecule : RawMolecule :=
  let m := BlueBookRule4aSource.molecule
  {m with
    atoms := m.atoms.take 32
    bonds := m.bonds.filterMap (fun b =>
      if ([19,22,25,28] : List Nat).contains b.target then none
      else some {b with source := compactId b.source, target := compactId b.target}) ++
        [⟨1,9,.single⟩,⟨7,11,.single⟩]}

/-- Adjust the four methylene H positions for the newly formed bonds.
Every carbon remains the strict interior centroid of its actual ligands. -/
def geometry : Geometry
  | 18 => some ⟨-9,0,-1⟩ | 21 => some ⟨9,0,-1⟩
  | 24 => some ⟨-6,-4,-1⟩ | 27 => some ⟨6,-4,-1⟩
  | i => BlueBookRule4aSource.geometry (sourceId i)

def hints (path : List Nat) : Option Recursive.Frame := do
  let f ← BlueBookRule4aSource.hints (path.map sourceId)
  return {f with low := compactId f.low, rename := fun i => compactId (f.rename (sourceId i))}

private def classified (g : Geometry) (p : List Nat) (fuel : Nat) :=
  (RingAuxiliaryInventory.classify? molecule g hints (fun _ => 1) fuel p).map (·.reading)

private def c5Children : Option Facts := do
  let c ← Promotion.singlePairAbsenceAt? molecule geometry [4,5] 1
    (Promotion.deriveAt molecule geometry hints (fun _ => 1) 1)
  return c.positiveFacts

/-- Each direction from C5 first presents R and then S. The more distant
occurrence sees the cut copy of C5 in place of the real C5.
Both of these branch inventories survive the proved absence at C5. -/
theorem matched_ring_occurrences :
    c5Children = some [
      ([4,5,6],⟨.R,.S⟩),([4,5,6,7,11,10],⟨.S,.R⟩),
      ([4,5,10],⟨.R,.S⟩),([4,5,10,11,7,6],⟨.S,.R⟩)] ∧
    classified geometry [4,5] 2 = some none := by
  constructor <;> decide +kernel

/-- Rule 4a distinguishes the two cyclopentyl groups at C4 only after
the evaluator certifies both the pseudoasymmetric C3 and the nonstereogenic
C5. The root letter changes on reflection. -/
theorem parent_uses_absence :
    classified geometry [4,3] 2 = some (some ⟨.S,.S⟩) ∧
    classified geometry [4] 3 = some (some ⟨.S,.R⟩) ∧
    classified (mirror geometry) [4] 3 = some (some ⟨.R,.S⟩) := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

end TetraStereo.Examples.RingVerifiedAbsence

assert_kernel_only TetraStereo.Examples.RingVerifiedAbsence.retained_absence_and_opposed_control
assert_kernel_only TetraStereo.Examples.RingVerifiedAbsence.matched_ring_occurrences
assert_kernel_only TetraStereo.Examples.RingVerifiedAbsence.parent_uses_absence
