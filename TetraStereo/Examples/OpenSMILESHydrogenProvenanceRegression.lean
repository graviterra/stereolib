import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

namespace TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression

open OneCenter
open RawMolecule

private def marker (clockwise : Bool) : String := if clockwise then "@@" else "@"

private def expandedRow? (input : String) (center : Nat) : Option (List Nat) :=
  match parseOpenSMILES input with
  | .error _ => none
  | .ok molecule => some (molecule.withExplicitHydrogens.writtenNeighbors center)

/-- A ring opened in a later branch may arrive at the root before its global outgoing bonds.
That incoming ring is not a source predecessor; the bracket H remains first. -/
theorem root_late_ring (clockwise : Bool) :
    expandedRow? ("[C" ++ marker clockwise ++ "H](F)(C(Cl)C1)1") 0 =
      some [5, 1, 2, 4] := by cases clockwise <;> decide +kernel

/-- Every disconnected component root follows the same rule, not just atom zero. -/
theorem later_component_root (clockwise : Bool) :
    expandedRow? ("C.[C" ++ marker clockwise ++ "H](F)(C(Cl)C1)1") 1 =
      some [10, 2, 3, 5] := by cases clockwise <;> decide +kernel

/-- Identical graph neighborhoods reached across a dot or a chain have different source frames.
The incoming ring edge on the disconnected root is not its introduction edge. -/
theorem cross_dot_root (clockwise : Bool) :
    expandedRow? ("C1.[C" ++ marker clockwise ++ "H]1(F)Cl") 1 =
      some [7, 0, 2, 3] := by cases clockwise <;> decide +kernel

theorem ordinary_chain_predecessor (clockwise : Bool) :
    expandedRow? ("C[C" ++ marker clockwise ++ "H](F)Cl") 1 =
      some [0, 7, 2, 3] := by cases clockwise <;> decide +kernel

/-- For a nonroot ring center, H follows the actual introduction neighbor even when another
incoming ring bond occurs earlier in the global bond list. -/
theorem nonroot_ring_predecessor (clockwise : Bool) :
    expandedRow? ("C1C(Cl)C[C" ++ marker clockwise ++ "H]1F") 4 =
      some [3, 11, 0, 5] := by cases clockwise <;> decide +kernel

private def expansionStable? (input : String) : Bool :=
  match parseOpenSMILES input with
  | .error _ => false
  | .ok molecule =>
      let once := molecule.withExplicitHydrogens
      let twice := once.withExplicitHydrogens
      (twice.atomCount, twice.bonds, twice.neighborOrder, twice.introductionPredecessors) ==
        (once.atomCount, once.bonds, once.neighborOrder, once.introductionPredecessors)

/-- Repeat materialization preserves the expanded graph, source rows and original provenance
prefix for all repaired root/nonroot cases and both written parities. This does not equate raw atom
metadata: the pre-existing materializer consumes the generated H atoms' default count on a second
pass, changing their count spelling from `none` to `some 0` without adding atoms or bonds. -/
theorem repeated_expansion_stable (clockwise : Bool) :
    (["[C" ++ marker clockwise ++ "H](F)(C(Cl)C1)1",
      "C.[C" ++ marker clockwise ++ "H](F)(C(Cl)C1)1",
      "C1.[C" ++ marker clockwise ++ "H]1(F)Cl",
      "C[C" ++ marker clockwise ++ "H](F)Cl",
      "C1C(Cl)C[C" ++ marker clockwise ++ "H]1F"] : List String).all
      expansionStable? = true := by cases clockwise <;> decide +kernel

/-- The low-level splice preserves all bonds in every metadata case, independently of parser
admission and independently of the particular finite regressions above. -/
example (predecessor : Option (Option Nat)) (bonds extra : List RawBond) (index : Nat) :
    (spliceHydrogenBondsWithPredecessor predecessor bonds index extra).Perm (bonds ++ extra) :=
  spliceHydrogenBondsWithPredecessor_perm predecessor bonds index extra

end TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression

assert_kernel_only TetraStereo.OneCenter.RawMolecule.spliceHydrogenBondsWithPredecessor_perm
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_introductionPredecessors
assert_kernel_only TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression.root_late_ring
assert_kernel_only TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression.later_component_root
assert_kernel_only TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression.cross_dot_root
assert_kernel_only TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression.ordinary_chain_predecessor
assert_kernel_only TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression.nonroot_ring_predecessor
assert_kernel_only TetraStereo.Examples.OpenSMILESHydrogenProvenanceRegression.repeated_expansion_stable
