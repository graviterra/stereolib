import TetraStereo.Engine.RingReferenceDerivation
import TetraStereo.Engine.LocalizedChemicalRingPublic

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 2500000
set_option Elab.async false

namespace TetraStereo.Examples.RingIsotopeSpelling
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation

/-- A cyclopropane bearing ordinary iodine and explicit iodine-127 on
the same carbon. All bonds and hydrogens are explicit. -/
def molecule : RawMolecule where
  atoms := List.replicate 3 (.aliphatic .C) ++
    [.aliphatic .I, {element := .I, isotope? := some 127}] ++ List.replicate 4 (.aliphatic .H)
  bonds := ([(0,1),(0,2),(1,2),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨2,1,0⟩,⟨2,-1,0⟩,⟨-1,0,2⟩,⟨-1,0,-2⟩,
  ⟨3,2,1⟩,⟨3,2,-1⟩,⟨3,-2,1⟩,⟨3,-2,-1⟩]⟩

private def geometry (a : Nat) := spatial.positions[a]?

theorem admitted : saturatedWithHalogens molecule = true ∧
    (LocalizedChemicalRing.admitRawSpatial? molecule spatial).isSome = true ∧
    ∀ a : Fin 3, (readback? geometry (molecule.writtenNeighbors a.val)).isSome = true := by
  decide +kernel

/-- The raw source keeps two distinct isotope spellings. Their actual
terminal occurrences compare equal after Rule 2 in either direction. -/
theorem iodine_pair :
    (molecule.atoms[3]?).bind AtomSpec.isotope? = none ∧
    (molecule.atoms[4]?).bind AtomSpec.isotope? = some 127 ∧
    (IsotopePriority.compareIncident? molecule [0] 3 4).map (·.ordering) = some .eq ∧
    (IsotopePriority.compareIncident? molecule [0] 4 3).map (·.ordering) = some .eq := by
  decide +kernel

/-- Signed recursive derivation yields a certified absence at the fully
positioned geminal center with these two equal Rule 2 ligands. -/
theorem geminal_absence :
    (ReferenceDerivation.derive? molecule geometry 3 molecule.atomCount [0]).map
        (·.verdict) = some none := by decide +kernel

namespace MixedMethyl

/-- The two methyl ligands on carbon 0 are CHD₂ and CH₂D. Fluorine
on carbon 1 differentiates the two arcs of the cyclopropane. -/
def molecule : RawMolecule where
  atoms :=
    let h : AtomSpec := .aliphatic .H
    let d : AtomSpec := {element := .H, isotope? := some 2}
    List.replicate 5 (.aliphatic .C) ++ [.aliphatic .F,h,h,h,d,d,h,d,h,h]
  bonds := ([(0,1),(0,2),(1,2),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8),
    (3,9),(3,10),(3,11),(4,12),(4,13),(4,14)] : List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def spatial : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨2,1,0⟩,⟨2,-1,0⟩,⟨-1,0,2⟩,⟨-1,0,-2⟩,
  ⟨3,2,1⟩,⟨3,2,-1⟩,⟨3,-2,1⟩,⟨3,-2,-1⟩,⟨-2,1,3⟩,⟨-2,-1,3⟩,⟨0,0,4⟩,
  ⟨-2,1,-3⟩,⟨-2,-1,-3⟩,⟨0,0,-4⟩]⟩

private def geometry : Geometry := fun i => spatial.positions[i]?

theorem admitted : saturatedWithHalogens molecule = true ∧
    (LocalizedChemicalRing.admitRawSpatial? molecule spatial).isSome = true ∧
    ∀ a : Fin 5, (readback? geometry (molecule.writtenNeighbors a.val)).isSome = true := by
  decide +kernel

private def comparison (i j : Nat) :=
  (IsotopePriority.compareIncident? molecule [0] i j).map fun c => (c.ordering,c.rule?)

theorem sphere_two : comparison 3 4 = some (.gt,some (.isotopeMass 2)) ∧
    comparison 4 3 = some (.lt,some (.isotopeMass 2)) := by decide +kernel

/-- All four priorities are strict before stereochemical rules. The actual
geometry gives uppercase R and reflection gives uppercase S. -/
theorem ranked_root :
    (IsotopePriority.rank? molecule [0]).map (·.order) = some [1,2,3,4] ∧
    (ReferenceDerivation.derive? molecule geometry 3 molecule.atomCount [0]).map (·.verdict) =
      some (some ⟨.R,.S⟩) ∧
    (ReferenceDerivation.derive? molecule (mirror geometry) 3 molecule.atomCount [0]).map (·.verdict) =
      some (some ⟨.S,.R⟩) := by decide +kernel

end MixedMethyl

end TetraStereo.Examples.RingIsotopeSpelling

assert_kernel_only TetraStereo.Examples.RingIsotopeSpelling.admitted
assert_kernel_only TetraStereo.Examples.RingIsotopeSpelling.iodine_pair
assert_kernel_only TetraStereo.Examples.RingIsotopeSpelling.geminal_absence

assert_kernel_only TetraStereo.Examples.RingIsotopeSpelling.MixedMethyl.admitted
assert_kernel_only TetraStereo.Examples.RingIsotopeSpelling.MixedMethyl.sphere_two
assert_kernel_only TetraStereo.Examples.RingIsotopeSpelling.MixedMethyl.ranked_root
