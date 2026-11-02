import TetraStereo.OneCenter.CIPP93TrigonalPyramidalIntegration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

namespace TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression

open OneCenter

/-!
These regressions cover the repository's existing convention that a written lone pair occupies
the implicit-H position. They establish parser-history consistency, not an externally settled
OpenSMILES lone-pair rule, a chemical R/S assignment, or human approval.
-/

private def marker (clockwise : Bool) : String := if clockwise then "@@" else "@"

private def frame? (input : String) (center : Nat) : Option (List Nat) :=
  match parseOpenSMILES input with
  | .error _ => none
  | .ok molecule => some (molecule.ligandsWithLonePair center)

/-- A late incoming ring closure does not turn a component root into a preceded atom. -/
theorem root_late_ring (clockwise : Bool) :
    frame? ("[P" ++ marker clockwise ++ "](F)(C(Cl)C1)1") 0 =
      some [5, 1, 2, 4] := by cases clockwise <;> decide +kernel

/-- The same convention applies to roots after a component separator. -/
theorem later_component_root (clockwise : Bool) :
    frame? ("C.[P" ++ marker clockwise ++ "](F)(C(Cl)C1)1") 1 =
      some [6, 2, 3, 5] := by cases clockwise <;> decide +kernel

/-- An ordinary introduction edge keeps the phantom after its actual predecessor. -/
theorem ordinary_chain_predecessor (clockwise : Bool) :
    frame? ("F[P" ++ marker clockwise ++ "](Cl)Br") 1 =
      some [0, 4, 2, 3] := by cases clockwise <;> decide +kernel

/-- A nonroot ring center uses its true predecessor, even with an earlier incoming ring record. -/
theorem nonroot_ring_predecessor (clockwise : Bool) :
    frame? ("C1C(Cl)C[P" ++ marker clockwise ++ "]1F") 4 =
      some [3, 6, 0, 5] := by cases clockwise <;> decide +kernel

private def legacyFrame? (input : String) (center : Nat) : Option (List Nat) :=
  match parseOpenSMILES input with
  | .error _ => none
  | .ok molecule =>
      let legacy : RawMolecule := { molecule with introductionPredecessors := [] }
      some (legacy.ligandsWithLonePair center)

/-- Unknown history deliberately retains the legacy incoming-bond fallback. -/
theorem unknown_history_compatible (clockwise : Bool) :
    legacyFrame? ("[P" ++ marker clockwise ++ "](F)(C(Cl)C1)1") 0 =
      some [1, 5, 2, 4] := by cases clockwise <;> decide +kernel

/-- Ordinary and P-93 normalization retain the full source introduction prefix for every raw
input. The production hydrogen materializer has its own independently asserted preservation law. -/
theorem normalization_preserves_history (molecule : RawMolecule) :
    (normalizeRawMolecule molecule).parsed.introductionPredecessors =
        molecule.introductionPredecessors ∧
      (BlueBookP93.NoncarbonTetrahedra.Production.normalizeRawMoleculeP93 molecule).parsed.introductionPredecessors =
        molecule.introductionPredecessors := by
  exact ⟨rfl, rfl⟩

private def normalizedFrames? (input : String) : Option (List Nat × List Nat) :=
  match parseOpenSMILES input with
  | .error _ => none
  | .ok molecule =>
      let ordinary := (normalizeRawMolecule molecule).parsed
      let p93 :=
        (BlueBookP93.NoncarbonTetrahedra.Production.normalizeRawMoleculeP93 molecule).parsed
      some (ordinary.ligandsWithLonePair 0, BlueBookP93.TrigonalPyramidal.writtenPhantomFrame p93 0)

/-- Both the ordinary production route and the P-93 written frame retain the repaired root row. -/
theorem normalized_root_frame (clockwise : Bool) :
    normalizedFrames? ("[P" ++ marker clockwise ++ "](F)(C(Cl)C1)1") =
      some ([5, 1, 2, 4], [5, 1, 2, 4]) := by cases clockwise <;> decide +kernel

end TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression

assert_kernel_only TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression.root_late_ring
assert_kernel_only TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression.later_component_root
assert_kernel_only TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression.ordinary_chain_predecessor
assert_kernel_only TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression.nonroot_ring_predecessor
assert_kernel_only TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression.unknown_history_compatible
assert_kernel_only TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression.normalization_preserves_history
assert_kernel_only TetraStereo.Examples.OpenSMILESLonePairProvenanceRegression.normalized_root_frame
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_introductionPredecessors
