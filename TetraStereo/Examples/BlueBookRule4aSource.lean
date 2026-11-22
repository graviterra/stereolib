import TetraStereo.Engine.RingAuxiliaryInventory

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option Elab.async false

namespace TetraStereo.Examples.BlueBookRule4aSource
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open Engine.RingChemicalPriority

/-- P-92.5.1 acyclic source figure P92510b. Chemical indices C1–C11
match the renumbered drawing. The hydroxyl is O0–H16. Cl12, Cl13, Cl14
and Cl15 are attached to C2, C6, C8 and C10, respectively. -/
def molecule : RawMolecule where
  atoms := [.aliphatic .O] ++ List.replicate 11 (.aliphatic .C) ++
    List.replicate 4 (.aliphatic .Cl) ++ List.replicate 20 (.aliphatic .H)
  bonds := ([(0,4),(0,16),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(3,8),(8,9),
    (5,10),(10,11),(2,12),(6,13),(8,14),(10,15),
    (1,17),(1,18),(1,19),(7,20),(7,21),(7,22),(9,23),(9,24),(9,25),
    (11,26),(11,27),(11,28),(2,29),(3,30),(4,31),(5,32),(6,33),(8,34),(10,35)] :
    List (Nat × Nat)).map (fun (i,j) => ⟨i,j,.single⟩)

/-- Positive z points toward the viewer. The solid wedges in P92510b are
C2–Cl12, C4–O0, C6–H33, C8–Cl14 and C10–Cl15. C3–H30 is dashed.
Each carbon lies at the centroid of its own four ligand positions. -/
def positions : List CartesianPoint3 := [
  ⟨-1,4,4⟩,⟨-6,0,0⟩,⟨-4,2,0⟩,⟨-2,0,-1⟩,⟨0,2,0⟩,⟨2,0,-1⟩,
  ⟨4,2,0⟩,⟨6,0,0⟩,⟨-3,-2,0⟩,⟨-5,-2,0⟩,⟨3,-2,0⟩,⟨5,-2,0⟩,
  ⟨-5,4,3⟩,⟨5,4,-2⟩,⟨-3,-3,3⟩,⟨3,-3,3⟩,⟨-2,5,5⟩,
  ⟨-6,0,1⟩,⟨-6,1,0⟩,⟨-8,-3,-1⟩,⟨6,0,1⟩,⟨6,1,0⟩,⟨8,-3,-1⟩,
  ⟨-5,-2,1⟩,⟨-5,-1,0⟩,⟨-7,-3,-1⟩,⟨5,-2,1⟩,⟨5,-1,0⟩,⟨7,-3,-1⟩,
  ⟨-3,4,-2⟩,⟨-1,-2,-4⟩,⟨1,4,-2⟩,⟨1,-2,-4⟩,⟨3,4,3⟩,⟨-2,-3,-2⟩,⟨2,-3,-2⟩]

def geometry : Geometry := fun i => positions[i]?

/-- Graph automorphism exchanging the two ordinary R substituents at C5. -/
def swapAt5 : Nat → Nat
  | 6 => 10 | 10 => 6 | 7 => 11 | 11 => 7 | 13 => 15 | 15 => 13
  | 20 => 26 | 26 => 20 | 21 => 27 | 27 => 21 | 22 => 28 | 28 => 22
  | 33 => 35 | 35 => 33 | i => i

/-- Constitutional exchange of the opposite-handed ligands at C3. -/
def swapAt3 : Nat → Nat
  | 2 => 8 | 8 => 2 | 1 => 9 | 9 => 1 | 12 => 14 | 14 => 12
  | 17 => 23 | 23 => 17 | 18 => 24 | 24 => 18 | 19 => 25 | 25 => 19
  | 29 => 34 | 34 => 29 | i => i

/-- Constitutional exchange of C3/C5 at C4. This mapping does not preserve
the hands at every corresponding secondary carbon. -/
def swapAt4 : Nat → Nat
  | 3 => 5 | 5 => 3 | 2 => 6 | 6 => 2 | 8 => 10 | 10 => 8
  | 1 => 7 | 7 => 1 | 9 => 11 | 11 => 9 | 12 => 13 | 13 => 12
  | 14 => 15 | 15 => 14 | 17 => 20 | 20 => 17 | 18 => 21 | 21 => 18
  | 19 => 22 | 22 => 19 | 23 => 26 | 26 => 23 | 24 => 27 | 27 => 24
  | 25 => 28 | 28 => 25 | 29 => 33 | 33 => 29 | 30 => 32 | 32 => 30
  | 34 => 35 | 35 => 34 | i => i

def c3Frame : Recursive.Frame := ⟨.five,4,2,8,30,swapAt3,true⟩

def hints (p : List Nat) : Option Recursive.Frame :=
  match p.getLast? with
  | some 3 => some c3Frame
  | some 4 => some ⟨.fourC,0,3,5,31,swapAt4,false⟩
  | some 5 => some ⟨.five,4,6,10,32,swapAt5,true⟩
  | _ => none

/-- The outer option witnesses completion at exactly this occurrence. The
inner option distinguishes a proved absence from a positive reading. -/
def selected (g : Geometry) (p : List Nat) (fuel : Nat) : Option (Option Recursive.Reading) :=
  (RingAuxiliaryInventory.classify? molecule g hints (fun _ => 1) fuel p).map (·.reading)

/-- The center's two carbon arms are still equivalent through isotope mass.
The coordinates and the chiral classifications first enter after this tie. -/
theorem constitution_at_four :
    saturatedWithHalogens molecule = true ∧
    (IsotopePriority.compareIncident? molecule [4] 3 5).map (·.ordering) = some .eq :=
  ⟨by decide +kernel,by decide +kernel⟩

private def retainedSites (g : Geometry) : Option Recursive.Facts := do
  let cert ← Promotion.singlePairAbsenceAt? molecule g [4,5] 1
    (Promotion.deriveAt molecule g hints (fun _ => 1) 1)
  return cert.positiveFacts

/-- Both chloroethyl ligands at C5 have R descriptors. Their own readings
survive the absence of a descriptor at their common parent. -/
theorem retained_at_five :
    retainedSites geometry = some [([4,5,6],⟨.R,.S⟩),([4,5,10],⟨.R,.S⟩)] ∧
    selected geometry [4,5] 2 = some none := by
  constructor <;> decide +kernel

/-- C3 compares two enantiomorphic chloroethyl groups. Geometry reflection
and exchange of the Rule 5 priority cancel, giving lowercase s. -/
theorem retained_at_three : selected geometry [4,3] 2 = some (some ⟨.S,.S⟩) ∧
    (Recursive.Reading.mk .S .S).label = some (.pseudoasymmetric .s) := by
  exact ⟨by decide +kernel,rfl⟩

/-- Rule 4a at C4 places the pseudoasymmetric C3 ahead of nonstereogenic C5.
The order persists on reflection so the source S changes to uppercase R. -/
theorem source_assignment :
    selected geometry [4] 3 = some (some ⟨.S,.R⟩) ∧
    selected (mirror geometry) [4] 3 = some (some ⟨.R,.S⟩) := by
  constructor <;> decide +kernel

/-- Exchange just Cl and H at a chloroethyl center to invert its physical
configuration while preserving every bond and atom specification. -/
def invert (cl h : Nat) : Geometry := fun i =>
  geometry (if i = cl then h else if i = h then cl else i)

/-- Inverting C8 makes the two arms at C3 identical. Inverting C10 instead
makes the two arms at C5 enantiomorphic and gives C5 lowercase r. -/
theorem inversion_controls :
    selected (invert 14 34) [4,3] 2 = some none ∧
    selected (invert 15 35) [4,5] 2 = some (some ⟨.R,.R⟩) ∧
    (Recursive.Reading.mk .R .R).label = some (.pseudoasymmetric .r) := by
  exact ⟨by decide +kernel,by decide +kernel,rfl⟩

/-- Invert C8 and C10 together. C3 loses its stereogenicity, C5 acquires
it, and the Rule 4a priority at C4 reverses on the same central frame. -/
def opposed : Geometry := fun i =>
  (invert 14 34) (if i = 15 then 35 else if i = 35 then 15 else i)

theorem exchanged_classes : selected opposed [4] 3 = some (some ⟨.R,.S⟩) := by
  decide +kernel

end TetraStereo.Examples.BlueBookRule4aSource

assert_kernel_only TetraStereo.Examples.BlueBookRule4aSource.constitution_at_four
assert_kernel_only TetraStereo.Examples.BlueBookRule4aSource.retained_at_five
assert_kernel_only TetraStereo.Examples.BlueBookRule4aSource.retained_at_three
assert_kernel_only TetraStereo.Examples.BlueBookRule4aSource.source_assignment
assert_kernel_only TetraStereo.Examples.BlueBookRule4aSource.inversion_controls
assert_kernel_only TetraStereo.Examples.BlueBookRule4aSource.exchanged_classes
