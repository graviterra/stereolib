import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

namespace TetraStereo.Examples.OpenSMILESParserBoundaryRegression

open OneCenter

/-- Malformed token placements cannot be silently erased or moved to a later bond. -/
theorem malformed_rejected :
    (["C()O", "C(=)O", "C(-)O", "C((O))", "C(1)CC1", "C(-1)CC1",
      "=CO", "-C", "C==O", "C-=O", "C=(O)", "C(=O=)N", "C(=O).", "C=",
      ".C", "C.", "C..O", "C=.O", "C(C.)N", "C.(O)", "C(.(O))"] : List String).all
      (fun input => !(parseOpenSMILES input).isOk) = true := by decide +kernel

/-- Preserve supported syntax, including branch-dot chains, late ring digits, ring pairs across
components, empty input and the intentionally narrow legacy charged-parity bracket form. -/
theorem supported_preserved :
    (["", "C", "C(=O)O", "C(.O)N", "C(.O.N)C", "C1.C1", "C=1CCCCC1",
      "C(Cl)1CCCCC1", "C%12CCCCC%12", "C(/F)=C/F", "[S+@@]",
      "[C@H](F)(C(Cl)C1)1", "C.[C@@H](F)(C(Cl)C1)1",
      "C1.[C@H]1(F)Cl", "C1C(Cl)C[C@@H]1F"] : List String).all
      (fun input => (parseOpenSMILES input).isOk) = true := by decide +kernel

private def chain : RawMolecule where
  atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .C]
  bonds := [{ source := 0, target := 1, kind := .single }]
  neighborOrder := [[1], [0]]
  introductionPredecessors := [none, some 0]

/-- Valid explicit history and legacy absence both remain accepted. -/
theorem valid_and_legacy_metadata :
    (normalizeRawMoleculeCertified? chain).isSome = true ∧
      (normalizeRawMoleculeCertified? { chain with introductionPredecessors := [] }).isSome = true :=
  by decide +kernel

/-- Out-of-range, nonchronological, missing-edge and excess-prefix metadata cannot pass checked
chemistry intake. A source-root claim itself still requires the actual source for authentication. -/
theorem invalid_metadata_rejected :
    ([{ chain with introductionPredecessors := [none, some 99] },
      { chain with introductionPredecessors := [none, some 1] },
      { chain with bonds := [], neighborOrder := [[], []] },
      { chain with introductionPredecessors := [none, some 0, none] }] : List RawMolecule).all
      (fun molecule => !(normalizeRawMoleculeCertified? molecule).isSome) = true := by decide +kernel

private def misorderedTriangle : RawMolecule where
  atoms := List.replicate 3 (AtomSpec.aliphatic .C)
  bonds := [{ source := 0, target := 2, kind := .single },
    { source := 0, target := 1, kind := .single },
    { source := 1, target := 2, kind := .single }]
  neighborOrder := [[2, 1], [0, 2], [0, 1]]
  introductionPredecessors := [none, some 0, some 1]

/-- Exact neighbor membership is insufficient: a known introduction predecessor must occupy the
first source-neighbor slot before its bracket H is inserted. -/
theorem predecessor_must_be_first :
    misorderedTriangle.stereochemicalAdmissible? = true ∧
      (normalizeRawMoleculeCertified? misorderedTriangle).isSome = false := by decide +kernel

/-- Generic parser-state helpers preserve honest unknown/partial prefixes, while a total source
history receives its new child's actual predecessor at the correct index. -/
theorem append_preserves_partial_history :
    let legacy : ParseState :=
      { atoms := [AtomSpec.aliphatic .C], current? := some 0, order := [[]] }
    let partialState : ParseState :=
      { atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .C], current? := some 1,
        order := [[1], [0]], introductionPredecessors := [none] }
    (legacy.addAtom (AtomSpec.aliphatic .F)).introductionPredecessors = [] ∧
      (partialState.addAtom (AtomSpec.aliphatic .F)).introductionPredecessors = [none] ∧
      (({ legacy with introductionPredecessors := [none] }).addAtom
        (AtomSpec.aliphatic .F)).introductionPredecessors = [none, some 0] := by
  decide +kernel

end TetraStereo.Examples.OpenSMILESParserBoundaryRegression

assert_kernel_only TetraStereo.OneCenter.parseOpenSMILES_introduction_valid
assert_kernel_only TetraStereo.OneCenter.ChemistryNormalizationResult.certify?_introduction_valid
assert_kernel_only TetraStereo.Examples.OpenSMILESParserBoundaryRegression.malformed_rejected
assert_kernel_only TetraStereo.Examples.OpenSMILESParserBoundaryRegression.supported_preserved
assert_kernel_only TetraStereo.Examples.OpenSMILESParserBoundaryRegression.valid_and_legacy_metadata
assert_kernel_only TetraStereo.Examples.OpenSMILESParserBoundaryRegression.invalid_metadata_rejected
assert_kernel_only TetraStereo.Examples.OpenSMILESParserBoundaryRegression.predecessor_must_be_first

assert_kernel_only TetraStereo.Examples.OpenSMILESParserBoundaryRegression.append_preserves_partial_history
