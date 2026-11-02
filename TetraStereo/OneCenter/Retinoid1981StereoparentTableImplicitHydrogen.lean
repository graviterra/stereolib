import TetraStereo.OneCenter.Retinoid1981StereoparentTableAuthorityInput
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace StereoparentTableImplicitHydrogen

open FigureGraphTranscription
open FigureAuthorityInput
open StereoparentTableAuthorityInput

/-- Neutral valence model scoped to the atom vocabulary used by the Ret-2 graphs. A generic
substituent has no admissible valence because it lacks a chemical identity. -/
def neutralValence : AtomElement → Option Nat
  | .carbon => some 4
  | .nitrogen => some 3
  | .oxygen => some 2
  | .fluorine => some 1
  | .genericSubstituent => none

@[simp] theorem neutral_valence_exact :
    neutralValence .carbon = some 4 ∧
      neutralValence .nitrogen = some 3 ∧
        neutralValence .oxygen = some 2 ∧
          neutralValence .fluorine = some 1 ∧
            neutralValence .genericSubstituent = none := by
  decide

def incidentBondOrderSum (graph : HeavyAtomGraph) (atomId : Nat) : Nat :=
  graph.bonds.foldl
    (fun total bond =>
      if bond.low = atomId ∨ bond.high = atomId then
        total + bondOrderToNat bond.order
      else total)
    0

/-- Complete one heavy atom exactly when its incident bond-order sum does not exceed the scoped
neutral valence. -/
def implicitHydrogenCount? (graph : HeavyAtomGraph) (node : AtomNode) : Option Nat := do
  let valence ← neutralValence node.element
  let usedValence := incidentBondOrderSum graph node.locant
  if usedValence ≤ valence then some (valence - usedValence)
  else none

def implicitHydrogenCounts? (graph : HeavyAtomGraph) : Option (List Nat) :=
  graph.nodes.mapM (implicitHydrogenCount? graph)

structure MolecularFormula where
  carbon : Nat
  hydrogen : Nat
  nitrogen : Nat
  oxygen : Nat
  fluorine : Nat
  deriving DecidableEq, Repr

namespace MolecularFormula

def heavyAtomCount (formula : MolecularFormula) : Nat :=
  formula.carbon + formula.nitrogen + formula.oxygen + formula.fluorine

end MolecularFormula

private def elementCount (graph : HeavyAtomGraph) (element : AtomElement) : Nat :=
  (graph.nodes.filter fun node => node.element == element).length

def formulaFromImplicitHydrogens
    (graph : HeavyAtomGraph) (implicitHydrogens : List Nat) : MolecularFormula :=
  { carbon := elementCount graph .carbon
    hydrogen := implicitHydrogens.sum
    nitrogen := elementCount graph .nitrogen
    oxygen := elementCount graph .oxygen
    fluorine := elementCount graph .fluorine }

def molecularFormula? (graph : HeavyAtomGraph) : Option MolecularFormula := do
  let implicitHydrogens ← implicitHydrogenCounts? graph
  pure (formulaFromImplicitHydrogens graph implicitHydrogens)

/-! ## Exact local and molecular results -/

def lysylIminomethylAddedImplicitHydrogens : List (Nat × Nat) :=
  (lysylIminomethylGraph.nodes.drop 20).filterMap fun node =>
    (implicitHydrogenCount? lysylIminomethylGraph node).map fun hydrogenCount =>
      (node.locant, hydrogenCount)

@[simp] theorem lysyl_iminomethyl_added_implicit_hydrogens_exact :
    lysylIminomethylAddedImplicitHydrogens =
      [ (21, 0), (22, 2), (23, 2), (24, 2), (25, 2)
      , (26, 1), (27, 2), (28, 0), (29, 0), (30, 1) ] := by
  decide

def stereoparentTableMolecularFormulas : List (Nat × MolecularFormula) :=
  stereoparentTableGraphEntries.filterMap fun entry => do
    let formula ← molecularFormula? entry.graph
    pure (entry.row.structureNumber, formula)

@[simp] theorem stereoparent_table_molecular_formulas_exact :
    stereoparentTableMolecularFormulas =
      [ (1, ⟨20, 30, 0, 1, 0⟩)
      , (2, ⟨20, 28, 0, 1, 0⟩)
      , (3, ⟨20, 28, 0, 2, 0⟩)
      , (4, ⟨20, 30, 0, 0, 0⟩)
      , (5, ⟨22, 32, 0, 2, 0⟩)
      , (6, ⟨20, 31, 1, 0, 0⟩)
      , (7, ⟨20, 29, 1, 1, 0⟩)
      , (8, ⟨26, 40, 2, 2, 0⟩)
      , (9, ⟨22, 32, 0, 2, 0⟩)
      , (10, ⟨26, 36, 0, 8, 0⟩) ] := by
  decide

/-! ## Proof-carrying completion batch -/

structure CompletedStereoparentTableImplicitHydrogen where
  candidate : StereoparentTableGraphEntry
  implicitHydrogens : List Nat
  formula : MolecularFormula
  implicitHydrogensExact :
    implicitHydrogenCounts? candidate.graph = some implicitHydrogens
  formulaExact :
    formula = formulaFromImplicitHydrogens candidate.graph implicitHydrogens
  atomCoverageExact :
    implicitHydrogens.length = candidate.graph.nodes.length
  heavyAtomCountExact :
    formula.heavyAtomCount = candidate.graph.nodes.length

def completeImplicitHydrogens?
    (candidate : StereoparentTableGraphEntry) :
    Option CompletedStereoparentTableImplicitHydrogen :=
  match observed : implicitHydrogenCounts? candidate.graph with
  | none => none
  | some implicitHydrogens =>
      let formula := formulaFromImplicitHydrogens candidate.graph implicitHydrogens
      if atomCoverageExact :
          implicitHydrogens.length = candidate.graph.nodes.length then
        if heavyAtomCountExact :
            formula.heavyAtomCount = candidate.graph.nodes.length then
          some
            { candidate := candidate
              implicitHydrogens := implicitHydrogens
              formula := formula
              implicitHydrogensExact := observed
              formulaExact := rfl
              atomCoverageExact := atomCoverageExact
              heavyAtomCountExact := heavyAtomCountExact }
        else none
      else none

def completedStereoparentTableImplicitHydrogens :
    List CompletedStereoparentTableImplicitHydrogen :=
  stereoparentTableGraphEntries.filterMap
    completeImplicitHydrogens?

def unresolvedStereoparentTableImplicitHydrogens :
    List StereoparentTableGraphEntry :=
  stereoparentTableGraphEntries.filter fun candidate =>
    (completeImplicitHydrogens? candidate).isNone

@[simp] theorem completed_stereoparent_table_implicit_hydrogen_count :
    completedStereoparentTableImplicitHydrogens.length = 10 := by
  decide

@[simp] theorem unresolved_stereoparent_table_implicit_hydrogens_empty :
    unresolvedStereoparentTableImplicitHydrogens = [] := by
  decide

@[simp] theorem completed_hydrogen_count_covers_every_atom
    (entry : CompletedStereoparentTableImplicitHydrogen) :
    entry.implicitHydrogens.length = entry.candidate.graph.nodes.length :=
  entry.atomCoverageExact

@[simp] theorem completed_formula_heavy_atom_count_exact
    (entry : CompletedStereoparentTableImplicitHydrogen) :
    entry.formula.heavyAtomCount = entry.candidate.graph.nodes.length :=
  entry.heavyAtomCountExact

end StereoparentTableImplicitHydrogen
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableImplicitHydrogen.neutral_valence_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableImplicitHydrogen.lysyl_iminomethyl_added_implicit_hydrogens_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableImplicitHydrogen.stereoparent_table_molecular_formulas_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableImplicitHydrogen.completed_stereoparent_table_implicit_hydrogen_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableImplicitHydrogen.unresolved_stereoparent_table_implicit_hydrogens_empty
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableImplicitHydrogen.completed_hydrogen_count_covers_every_atom
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTableImplicitHydrogen.completed_formula_heavy_atom_count_exact
