import TetraStereo.Engine.RingAuxiliaryInventory
import TetraStereo.Engine.RingSignedArm
import TetraStereo.Examples.RingVerifiedAbsence

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false

namespace TetraStereo.Examples.RingNestedAbsence
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority Recursive

/-- A 1-fluorocyclobutyl group, with a specified isotope at each of the two
CH₂ neighbors of the attachment carbon. Its third CH₂ is unlabelled. -/
private def ringAtoms (firstMass : Nat) : List AtomSpec :=
  [.aliphatic .C, {element := .C, isotope? := some firstMass}, .aliphatic .C,
   {element := .C, isotope? := some 12}, .aliphatic .F] ++ List.replicate 6 (.aliphatic .H)

private def ringEdges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,0),(0,4),(1,5),(1,6),(2,7),(2,8),(3,9),(3,10)]

/-- CHF0 bears two cyclobutyl groups at C3 and C14. At mass 12 the groups
are identical. Mass 13 labels just C4 in the left ring. -/
def molecule (mass : Nat) : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .F,.aliphatic .H] ++ ringAtoms mass ++ ringAtoms 12
  bonds := ([(0,1),(0,2)] ++ [3,14].flatMap (fun k =>
    (0,k) :: ringEdges.map (fun (i,j) => (i+k,j+k)))).map (fun (i,j) => ⟨i,j,.single⟩)

private def ringPositions : List CartesianPoint3 :=
  [⟨2,2,0⟩,⟨3,4,-1⟩,⟨4,6,0⟩,⟨3,4,1⟩,⟨2,0,0⟩,
   ⟨4,4,-2⟩,⟨2,4,-2⟩,⟨6,8,0⟩,⟨4,8,0⟩,⟨4,4,2⟩,⟨2,4,2⟩]

/-- The ring frames exchange under reflection in x. Reflection in z exchanges
the two paths within each ring while fixing its attachment carbon and F. -/
def geometry : Geometry := fun i =>
  if i < 3 then ([⟨0,0,0⟩,⟨0,-2,1⟩,⟨0,-2,-1⟩] : List CartesianPoint3)[i]?
  else if i < 14 then ringPositions[i-3]?
  else (ringPositions[i-14]?).map CartesianPoint3.reflectX

def atSite (mass : Nat) (g : Geometry) (p : List Nat) (fuel : Nat) :=
  RingAuxiliaryInventory.classify? (molecule mass) g (fun _ => none) (fun _ => 1) fuel p

def reading (mass : Nat) (g : Geometry) (p : List Nat) (fuel : Nat) :=
  (atSite mass g p fuel).map (·.reading)

private def exchange (i : Nat) : Nat := if i < 3 then i else if i < 14 then i+11 else i-11

/-- At equal masses the entire molecular reflection exchanges the two
cyclobutyl groups while fixing the CHF frame's F and H. -/
theorem equal_mass_reflection : Reflects (molecule 12) geometry exchange := by
  constructor <;> decide +kernel

/-- Exhaustive walks from CHF encounter only the two ring attachment
carbons as candidates. Every other real carbon in these arms has two
identical H ligands, and the copies closing each ring are terminal. -/
theorem candidate_paths :
    ((occurrence? (molecule 12) [0,3]).bind (carbonSites (molecule 12) 26)) =
      some [[0,3]] ∧
    ((occurrence? (molecule 12) [0,14]).bind (carbonSites (molecule 12) 26)) =
      some [[0,14]] ∧ saturatedWithHalogens (molecule 12) = true := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

/-- Each attachment carbon has a pair of identical ring directions; the
common CHF has a pair of identical ring groups. Proving the CHF absence
needs the second level of the search. -/
theorem nested_absences :
    reading 12 geometry [0,3] 1 = some none ∧
    reading 12 geometry [0,14] 1 = some none ∧
    reading 12 geometry [0] 1 = none ∧
    reading 12 geometry [0] 2 = some none ∧
    reading 12 (mirror geometry) [0] 2 = some none := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> decide +kernel

/-- Inspect the returned outer proof. Both inner absences appear at their
actual paths in the two matched ring arms. -/
def nestedEntries : Option InventoryPriority.Entries := do
  match ← atSite 12 geometry [0] 2 with
  | .nested c => some c.pair.required
  | _ => none

theorem nested_children : nestedEntries = some [([0,3],none),([0,14],none)] := by
  decide +kernel

/-- Increasing only C4's mass separates the two ring directions at C3,
and distinguishes the left ring from the right ring at CHF0. -/
theorem isotope_control :
    reading 13 geometry [0,3] 1 = some (some ⟨.S,.R⟩) ∧
    reading 13 geometry [0,14] 1 = some none ∧
    reading 13 geometry [0] 1 = some (some ⟨.S,.R⟩) ∧
    reading 13 (mirror geometry) [0] 1 = some (some ⟨.R,.S⟩) := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide +kernel

/-- The C5 arm in the cyclic Rule 4a control contains a proved absence,
two nearer uppercase hands and two more distant opposite hands. Rule 4b
selects the nearer hands as references and reads all four chiral sites. -/
private def mixedWord (reverse : Bool) (reference : RS) : Bool :=
  (Engine.rankSignedRingArm? RingVerifiedAbsence.molecule RingVerifiedAbsence.geometry
    [4,5] reverse 2 RingVerifiedAbsence.hints (fun _ => 1)).any fun arm =>
    arm.inventory.entries.lookup [4,5] == (some none : Option (Option Reading)) &&
    arm.facts.map Prod.fst == [[4,5,6],[4,5,6,7,11,10],[4,5,10],[4,5,10,11,7,6]] &&
    arm.population.references == [reference] &&
    arm.bounds.low.flatten == [1,1,0,0] && arm.bounds.high.flatten == [1,1,0,0]

theorem signed_arm_on_both_geometries :
    mixedWord false .R = true ∧ mixedWord true .S = true := by
  constructor <;> decide +kernel

private def compareAtFour (g : Geometry) :=
  Engine.compareSignedRingRule4bBoth? BlueBookRule4aSource.molecule g [4]
    ⟨.fourB,0,3,5,31,id,false⟩ 1 2 BlueBookRule4aSource.hints (fun _ => 1)

private def tiedFrame (g : Geometry) : Bool :=
  (compareAtFour g).any fun c =>
    c.frame.left.entries.lookup [4,3] == (some none : Option (Option Reading)) &&
    c.frame.right.entries.lookup [4,5] == (some none : Option (Option Reading)) &&
    c.actual.result == .eq && c.reflected.result == .eq &&
    c.actual.left.population.references == [.R] && c.reflected.left.population.references == [.S]

/-- After only C8 is inverted, both C3 and C5 are nonstereogenic,
with pairs of R chloroethyl children. The frame reaches Rule 4b and both
complete words tie. On the published coordinates the C3/C5 difference
already decides Rule 4a, so this Rule 4b comparison is unavailable. -/
theorem signed_frame_tie_after_inversion :
    tiedFrame (BlueBookRule4aSource.invert 14 34) = true ∧
    (compareAtFour BlueBookRule4aSource.geometry).isNone = true := by
  constructor <;> decide +kernel

end TetraStereo.Examples.RingNestedAbsence

assert_kernel_only TetraStereo.Examples.RingNestedAbsence.candidate_paths
assert_kernel_only TetraStereo.Examples.RingNestedAbsence.equal_mass_reflection
assert_kernel_only TetraStereo.Examples.RingNestedAbsence.nested_absences
assert_kernel_only TetraStereo.Examples.RingNestedAbsence.nested_children
assert_kernel_only TetraStereo.Examples.RingNestedAbsence.isotope_control
assert_kernel_only TetraStereo.Examples.RingNestedAbsence.signed_arm_on_both_geometries
assert_kernel_only TetraStereo.Examples.RingNestedAbsence.signed_frame_tie_after_inversion
