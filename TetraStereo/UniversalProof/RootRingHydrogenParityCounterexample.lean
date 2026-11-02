import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false
set_option maxRecDepth 10000

/-!
Successor regressions for the October 4 parser diagnostics. The historical module path is
retained for compatibility. The accepted counterexample source and the pre-repair October 9
reproduction remain preserved in their evidence packages; the live statements below specify
the corrected parser and hydrogen ordering.
-/
namespace TetraStereo.UniversalProof.RootRingHydrogenParityCounterexample

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

/-- Valid first-atom tagged ring closure; the two ring paths differ at chlorine. -/
def input : String := "[C@H](F)(C(Cl)C1)1"

def expectedParsed : RawMolecule :=
  { atoms := [{ AtomSpec.aliphatic .C with explicitHydrogens? := some 1, tetrahedral? := some .anticlockwise },
              AtomSpec.aliphatic .F, AtomSpec.aliphatic .C,
              AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .C]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨2, 3, .single⟩,
              ⟨2, 4, .single⟩, ⟨4, 0, .single⟩]
    neighborOrder := [[1, 2, 4], [0], [0, 3, 4], [2], [2, 0]]
    introductionPredecessors := [none, some 0, some 0, some 2, some 2] }

theorem actual_parse : parseOpenSMILES input = .ok expectedParsed := by rfl

theorem actual_normalized_parsed :
    (parseAndNormalizeOpenSMILES input).map (fun result => result.parsed) =
      .ok expectedParsed := by rfl

theorem actual_certified_intake_accepts :
    (parseAndNormalizeOpenSMILESCertified input).isOk = true := by decide +kernel

theorem original_valid_chemistry_checks :
    expectedParsed.stereochemicalAdmissible? = true ∧
      expectedParsed.valenceOK? = true ∧ expectedParsed.rule2MassesKnown? = true := by
  decide +kernel

/-- The first atom was introduced without any predecessor; ring closure adds the later 4→0 edge. -/
theorem first_atom_introduction :
    (ParseState.addAtom {} ({ AtomSpec.aliphatic .C with explicitHydrogens? := some 1, tetrahedral? := some .anticlockwise })).bonds = [] := rfl

theorem incoming_ring_does_not_change_introduction :
    expectedParsed.bonds.any (fun bond => bond.target == 0) = true ∧
      expectedParsed.bonds.filter (fun bond => bond.target == 0) = [⟨4, 0, .single⟩] ∧
      expectedParsed.introductionPredecessors[0]? = some none := by
  decide +kernel

theorem actual_expansion_row :
    expectedParsed.withExplicitHydrogens.writtenNeighbors 0 = [5, 1, 2, 4] := by
  decide +kernel

theorem actual_STRING_expansion_row :
    (parseAndNormalizeOpenSMILES input).map
      (fun result => result.parsed.withExplicitHydrogens.writtenNeighbors 0) =
      .ok [5, 1, 2, 4] := by rfl

/-- Existing production helper's first-atom convention puts the virtual H before all written neighbors. -/
theorem first_atom_source_order :
    insertHydrogenInOrder (expectedParsed.writtenNeighbors 0) false [5] = [5, 1, 2, 4] := rfl

theorem actual_row_matches_first_atom_convention :
    expectedParsed.withExplicitHydrogens.writtenNeighbors 0 =
      insertHydrogenInOrder (expectedParsed.writtenNeighbors 0) false [5] := by
  decide +kernel

/-- For the physical role order F > chlorine-bearing ring path > other ring path > H,
the former wrong virtual-H placement reverses the existing parity interpreter.
This checks parity sensitivity, not an assumed or computed whole classifier ranking. -/
theorem source_order_transposition_reverses_interpreter :
    descriptorOfParity .anticlockwise (permutationIsEven [0, 2, 3, 1]) ≠
      descriptorOfParity .anticlockwise (permutationIsEven [1, 2, 3, 0]) := by
  decide +kernel

/-- A later disconnected-component root receives the same corrected first-atom convention. -/
theorem disconnected_component_actual_row :
    (parseAndNormalizeOpenSMILES "C.[C@H](F)(C(Cl)C1)1").map
      (fun result => result.parsed.withExplicitHydrogens.writtenNeighbors 1) =
      .ok [10, 2, 3, 5] := by rfl

theorem disconnected_component_first_atom_convention :
    (parseAndNormalizeOpenSMILES "C.[C@H](F)(C(Cl)C1)1").map
      (fun result => insertHydrogenInOrder (result.parsed.writtenNeighbors 1) false [10]) =
      .ok [10, 2, 3, 5] := by rfl

/-- Syntax-introduction context distinguishes chain arrival from a component-root ring closure. -/
theorem different_introduction_contexts_distinct_raw :
    parseOpenSMILES "C1.[C@H]1(F)Cl" ≠ parseOpenSMILES "C[C@H](F)Cl" := by
  intro same
  have histories := congrArg
    (fun result : Except ParserError RawMolecule =>
      result.map fun raw => raw.introductionPredecessors) same
  change (Except.ok [none, none, some 1, some 1] :
      Except ParserError (List (Option Nat))) =
    Except.ok [none, some 0, some 1, some 1] at histories
  cases histories

theorem both_introduction_contexts_certified :
    (parseAndNormalizeOpenSMILESCertified "C1.[C@H]1(F)Cl").isOk = true ∧
      (parseAndNormalizeOpenSMILESCertified "C[C@H](F)Cl").isOk = true := by
  decide +kernel

/-- Empty bond-only branches are rejected without losing the valid double-bond input. -/
theorem empty_bond_branch_distinct_from_valid_double_bond :
    (parseOpenSMILES "C(=)O").isOk = false ∧
      (parseOpenSMILES "C=O").isOk = true := by decide +kernel

theorem malformed_empty_bond_branch_rejected :
    (parseAndNormalizeOpenSMILESCertified "C(=)O").isOk = false := by decide +kernel

end TetraStereo.UniversalProof.RootRingHydrogenParityCounterexample
