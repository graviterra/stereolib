import TetraStereo.Engine.LocalizedChemicalRingFrozenExecution
import TetraStereo.Examples.LocalizedChemicalRingPropellaneLifetime
import TetraStereo.OneCenter.LocalizedChemicalRingScalarSymmetry

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedChemicalRingFrozenPropellane

open OneCenter Engine.LocalizedChemicalRing LocalizedChemicalRingPropellaneLifetime
open LocalizedChemicalRingPreparedContextRecursion LocalizedChemicalRingNestedLifetime

theorem replacement_frozen_eq (ops : LocalizedChemicalRingMultiMarkRecursion.MultiOperations)
    (mol : RawMolecule) (depth : Nat) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (st : OccurrenceAuxState) (n : Node) :
    descriptorOfStep (freezeChildren (replacement ops)) mol depth g st [] n =
    descriptorOfStep (freezeChildren (rawStepPrepared? ops)) mol depth g st [] n :=
  frozen_outcome_congr _ _ mol [] (fun geo state node obs =>
    first_promotion ops mol geo state node (fun _ => obs)) depth g st n

/-- Swap two complete methylene bridges, carrying both of their hydrogens. -/
private def swapBridges (a b ha hb : Fin 11) : Equiv.Perm (Fin 11) :=
  ((Equiv.swap a b).trans (Equiv.swap ha hb)).trans (Equiv.swap (ha+1) (hb+1))

private def witness (mark : Fin 11) : Fin 11 × Fin 11 × Equiv.Perm (Fin 11) :=
  if mark ∈ ([2,5,6] : List (Fin 11)) then (3,4,swapBridges 3 4 7 9)
  else if mark ∈ ([3,7,8] : List (Fin 11)) then (2,4,swapBridges 2 4 5 9)
  else (2,3,swapBridges 2 3 5 7)

private theorem graph_swaps :
    PreservesGraph (swapBridges 3 4 7 9) ∧ PreservesGraph (swapBridges 2 4 5 9) ∧
      PreservesGraph (swapBridges 2 3 5 7) := by
  unfold PreservesGraph
  decide +kernel

/-- At either bridgehead, even allowing the scalar reference to be *any* of the
eleven atoms, a molecular symmetry still exchanges two ligands and fixes that atom. -/
theorem every_scalar_has_exchange (focus mark : Fin 11) (bridgehead : focus = 0 ∨ focus = 1) :
    LocalizedChemicalRingScalarSymmetry.HasExchange PreservesGraph focus mark
      (fun a => parsedMol.bondOrder focus a ≠ 0) := by
  let w := witness mark
  refine ⟨w.2.2,w.1,w.2.1,?_,?_⟩
  · dsimp only [w,witness]
    split
    · exact graph_swaps.1
    · split
      · exact graph_swaps.2.1
      · exact graph_swaps.2.2
  · have allMarks : ∀ f m : Fin 11, (f = 0 ∨ f = 1) →
        let x := witness m
        x.2.2 f = f ∧ x.2.2 m = m ∧ parsedMol.bondOrder f x.1 ≠ 0 ∧
        parsedMol.bondOrder f x.2.1 ≠ 0 ∧ x.1 ≠ x.2.1 ∧
        x.2.2 x.1 = x.2.1 ∧ x.2.2 x.2.1 = x.1 := by decide +kernel
    exact allMarks focus mark bridgehead

def checkFrozen : IO Unit := do
  let input ← match admitSmilesSpatial? smiles LocalizedChemicalRingPropellaneLifetime.spatial with
    | .ok (some input) => pure input
    | _ => throw (IO.userError "propellane admission")
  let entries := input.certified.canonicalTetrahedralCenters.map
    (fun c => (c.1.val, frozenCenterOutcome input c))
  IO.println s!"Frozen propellane report: {repr entries}"
  unless entries == [0,1,2,3,4].map (fun i => (i,none)) do
    throw (IO.userError s!"Unexpected frozen propellane report {repr entries}")

#eval checkFrozen
end TetraStereo.Examples.LocalizedChemicalRingFrozenPropellane
assert_kernel_only TetraStereo.Examples.LocalizedChemicalRingFrozenPropellane.replacement_frozen_eq
assert_kernel_only TetraStereo.Examples.LocalizedChemicalRingFrozenPropellane.every_scalar_has_exchange
