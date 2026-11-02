import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedUniversalDeepDescriptorProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Full-budget universal descriptor on a deep twelve-atom triple-bond ligand comparison

This is a *scoped runtime regression probe* for the actual universal tetrahedral descriptor
`CertifiedLocalizedCIPInput.universalDescriptorOutcome` / `descriptorAt?` (from
`TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation`) on one small but genuinely deep
fixture:

```
F[C@](Cl)(C#CC#N)C#CC#C[H]
```

The fixture is supplied as an explicit `AuthoritativeChemicalInput` (twelve semantic atoms,
eleven localized pair bonds, exact rational coordinates) and admitted through the actual
`LocalizedUniversalReference.admitSource?` intake.  Atom `1` is the central carbon; its four
neighbours are, in ascending semantic index order, `F 0`, `Cl 2`, `C 3` and `C 7`.  The two carbon
branches are the two deepest ligands:

* left  `C3 # C4 - C5 # N6`;
* right `C7 # C8 - C9 # C10 - H11`.

Both carbon branches are identical through three Rule-1a spheres (carbon root, three multiple-bond
carbon copies, one carbon child).  The first difference is at Rule-1a layer 3, where the left
branch exposes the three `N` copies (atomic number 7) and the right branch the three carbon copies
(atomic number 6).  The fixture therefore exercises the actual multiple-bond duplicate expansion:
each triple bond contributes three addressed copy entries in the Rule-1a projection.

## Executed scope

`main` performs exactly one direct full-target probe at the automatic carrier budget
`LocalizedUniversalReference.carrierFuel input = atomCount + 1 = 13`:

* admission and structural assertions (twelve explicit atoms, four triple bonds, canonical
  tetrahedral centres exactly `[1]`, four-ligand base cursor order `[F 0, Cl 2, C 3, C 7]`);
* one materialized `universalDescriptorOutcome` at atom `1` with the explicit empty supplied
  dependency view;
* one `descriptorAt?` call at the computed bound;
* one Rule-3 frame evaluation at that same bound, from which the actual Rule-1a/Rule-3 key layers
  of the two carbon ligands are inspected: the number of leading equal Rule-1a layers, the first
  differing layer, and the actual `compareLocalizedRerootRecursiveRule3SpatialKeys` result.

The coordinate assignment is the rank-ordered tetrahedral point set of the established
`R` halomethane fixture: rank 1 `Cl` at `(1,1,1)`, rank 2 `F` at `(1,-1,-1)`, rank 3 `C3` at
`(-1,1,-1)`, rank 4 `C7` at `(-1,-1,1)`, centre at the origin.  The descriptor label is therefore
asserted as `R` on an explicit geometric ground, not as an external normative claim.

There is no carrier-wide descriptor production or certificate replay; one final-centre target is evaluated.
A `none` outcome would be an operational refusal of the executable pipeline, never a chemical
nonexistence claim.  This module is a formal regression on these fixture data, not an independent
IUPAC applicability decision.
-/

/-! ## IO helpers -/

private def flushOut : IO Unit := do
  (← IO.getStdout).flush

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then do
    IO.println ("ok: " ++ name)
    flushOut
  else throw (IO.userError ("failed: " ++ name))

private def note (message : String) : IO Unit := do
  IO.println message
  flushOut

/-! ## Fixture data -/

private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def nitrogen : PeriodicElement := ⟨7, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩

private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

/-- `F[C@](Cl)(C#CC#N)C#CC#C[H]` with the terminal hydrogen explicit.  Atom indices:
`0 F`, `1 C` (centre), `2 Cl`, `3 C`, `4 C`, `5 C`, `6 N`, `7 C`, `8 C`, `9 C`, `10 C`,
`11 H`.  Every atom is closed shell; the four triple bonds are `3-4`, `5-6`, `7-8` and `9-10`. -/
def deepSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [fluorine, carbon, chlorine, carbon, carbon, carbon, nitrogen,
            carbon, carbon, carbon, carbon, hydrogen].map fun element => { element }
        interactions :=
          [ bond 0 1 1, bond 1 2 1, bond 1 3 1, bond 3 4 3,
            bond 4 5 1, bond 5 6 3,
            bond 1 7 1, bond 7 8 3, bond 8 9 1, bond 9 10 3, bond 10 11 1 ] }
    spatial? := some
      { positions :=
          [ { x := 1, y := -1, z := -1 },   -- 0 F   (priority rank 2)
            { x := 0, y := 0, z := 0 },     -- 1 C   (centre)
            { x := 1, y := 1, z := 1 },     -- 2 Cl  (priority rank 1)
            { x := -1, y := 1, z := -1 },   -- 3 C   (priority rank 3, N branch)
            { x := 2, y := 0, z := 0 },     -- 4 C
            { x := 2, y := 1, z := 1 },     -- 5 C
            { x := 2, y := 2, z := 2 },     -- 6 N
            { x := -1, y := -1, z := 1 },   -- 7 C   (priority rank 4, C branch)
            { x := -2, y := 0, z := 0 },    -- 8 C
            { x := -2, y := -1, z := 1 },   -- 9 C
            { x := -2, y := -2, z := 2 },   -- 10 C
            { x := -3, y := -2, z := 2 } ] } } -- 11 H

/-! ## Small accessors -/

private def admitOrFail (name : String) (source : AuthoritativeChemicalInput) :
    IO TetraStereo.OneCenter.LocalizedUniversalReference.Input := do
  match TetraStereo.OneCenter.LocalizedUniversalReference.admitSource? source with
  | some input => pure input
  | none => throw (IO.userError (name ++ ": admission returned none"))

private def labelText : Option LocalizedAuxiliaryLabel → String
  | none => "none"
  | some (.chiral .R) => "R"
  | some (.chiral .S) => "S"
  | some (.pseudoasymmetric .r) => "r"
  | some (.pseudoasymmetric .s) => "s"

private def centerAt?
    (input : TetraStereo.OneCenter.LocalizedUniversalReference.Input) (atom : Nat) :
    Option input.certified.TetrahedralCenter :=
  input.certified.canonicalTetrahedralCenters.find? fun center =>
    center.val.val == atom

private def cursorAtom?
    (_input : TetraStereo.OneCenter.LocalizedUniversalReference.Input) {fuel : Nat}
    (cursor : _input.certified.LocalizedRerootCursor fuel) : Option Nat :=
  cursor.occurrence.1.node.current?.map fun atom => atom.val

private def nth? {α : Type*} : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, n + 1 => nth? tail n

private def layerLengths (layers : List (List (OfficialSparseEntry ℕ))) : List Nat :=
  layers.map List.length

private def layerValues (layer : List (OfficialSparseEntry ℕ)) : List Nat :=
  layer.map Prod.snd

/-- Number of leading Rule-1a layers on which the two projections agree. -/
private def leadingEqualRule1aLayers
    (left right : List (List (OfficialSparseEntry ℕ))) : Nat :=
  match left, right with
  | leftLayer :: leftRest, rightLayer :: rightRest =>
      match OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
          leftLayer rightLayer with
      | .eq => 1 + leadingEqualRule1aLayers leftRest rightRest
      | _ => 0
  | _, _ => 0

/-! ## The single full-target probe -/

def main : IO Unit := do
  let start ← IO.monoMsNow
  let name := "deep-triple"
  note "== universal deep descriptor probe: 12-atom N-versus-C triple-bond comparison =="
  let input ← admitOrFail name deepSource
  let admittedAt ← IO.monoMsNow
  note s!"ADMIT {name}: atoms={input.certified.certified.input.molecule.atomCount}, \
{admittedAt - start}ms"
  checkTest s!"{name}: admission preserves the explicit source molecule"
    (decide (input.certified.certified.input = deepSource))
  checkTest s!"{name}: the molecule has twelve explicit atoms"
    (input.certified.certified.input.molecule.atomCount == 12)
  checkTest s!"{name}: the spatial configuration has twelve explicit positions"
    (match input.certified.certified.input.spatial? with
     | some spatial => spatial.positions.length == 12
     | none => false)
  checkTest s!"{name}: the fixture carries four triple bonds"
    ((deepSource.molecule.interactions.filter
        (fun interaction => decide (interaction.kind = .covalent 3))).length == 4)
  let fuel := TetraStereo.OneCenter.LocalizedUniversalReference.carrierFuel input
  checkTest s!"{name}: the automatic carrier fuel is atomCount + 1 = 13"
    (fuel == 13)
  let centers := input.certified.canonicalTetrahedralCenters
  note s!"CENTRES {name}: {repr (centers.map fun center => center.val.val)}"
  checkTest s!"{name}: the canonical tetrahedral centre set is exactly atom 1"
    (decide (centers.map (fun center => center.val.val) = [1]))
  let some center := centerAt? input 1
    | throw (IO.userError (name ++ ": atom 1 is not a canonical tetrahedral centre"))
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  checkTest s!"{name}: the final occurrence is the atom-1 root occurrence"
    (target.1.address.isEmpty && target.1.root.val == 1)
  let view : input.certified.LocalizedDependencyView target := fun _ _ => none
  checkTest s!"{name}: the final occurrence stores its descriptor centre"
    (match input.certified.localizedOccurrenceDescriptorCenter? target with
     | some stored => decide (stored = center)
     | none => false)
  let some base := input.certified.localizedNoDoubleFourLigandFrameExec? target
    | throw (IO.userError (name ++ ": the final occurrence has no four-ligand base"))
  checkTest s!"{name}: the four-ligand base has four cursors"
    (decide (base.cursors.length = 4))
  let cursorAtoms := base.cursors.map (fun cursor => cursorAtom? input cursor)
  note s!"BASE {name}: cursor atoms={repr cursorAtoms}"
  checkTest s!"{name}: the base cursor order is [F 0, Cl 2, C 3, C 7]"
    (decide (cursorAtoms = [some 0, some 2, some 3, some 7]))

  -- One materialized universal outcome at the automatic full carrier fuel.  The bound and the
  -- descriptor are projected from the same preparation pass (no per-stage duplication).
  let universalStart ← IO.monoMsNow
  let outcome := input.certified.universalDescriptorOutcome target view
  let universalAt ← IO.monoMsNow
  let universalMs := universalAt - universalStart
  note s!"UNIVERSAL {name}: atom=1, bound={outcome.1}, descriptor={labelText outcome.2}, \
{universalMs}ms"
  checkTest s!"{name}: the universal outcome has a positive computed bound"
    (decide (0 < outcome.1))
  checkTest s!"{name}: the universal outcome assigns a descriptor"
    outcome.2.isSome
  checkTest s!"{name}: the descriptor is the geometrically grounded R label"
    (decide (outcome.2 = some (.chiral .R)))

  do
    -- The actual parameterized descriptor at exactly the computed bound.
    let atStart ← IO.monoMsNow
    let atBound := input.certified.descriptorAt? target view outcome.1
    let atBoundAt ← IO.monoMsNow
    note s!"DESCRIPTOR-AT {name}: bound={outcome.1}, result={labelText atBound}, \
{atBoundAt - atStart}ms"
    checkTest s!"{name}: descriptorAt? at the computed bound equals the universal descriptor"
      (decide (atBound = outcome.2))

    -- The prepared Rule-3 frame itself, at the same computed bound, for direct key inspection.
    let frameStart ← IO.monoMsNow
    let frame? := input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view outcome.1 base.cursors
    let frameAt ← IO.monoMsNow
    note s!"FRAME {name}: present={frame?.isSome}, {frameAt - frameStart}ms"
    match frame? with
    | none =>
        throw (IO.userError (name ++ ": the Rule-3 frame at the computed bound is absent"))
    | some frame =>
        checkTest s!"{name}: the prepared Rule-3 frame has four raw keys"
          (decide (frame.rawKeys.length = 4))
        checkTest s!"{name}: the prepared Rule-3 frame has four keys"
          (decide (frame.keys.length = 4))
        note s!"FRAME {name}: coupled={frame.coupled}, excluded={frame.excluded.length}"
        checkTest s!"{name}: the acyclic fixture has no coupled physical-unit topology"
          (decide (frame.coupled = false))
        match nth? frame.keys 2, nth? frame.keys 3 with
        | some left, some right =>
            let tied := leadingEqualRule1aLayers left.constitutional.rule1a
              right.constitutional.rule1a
            note s!"KEYS {name}: tiedLayers={tied}, \
leftLengths={repr (layerLengths left.constitutional.rule1a)}, \
rightLengths={repr (layerLengths right.constitutional.rule1a)}"
            note s!"LAYERS {name}: left={repr left.constitutional.rule1a}, \
right={repr right.constitutional.rule1a}"
            checkTest s!"{name}: the two carbon ligand keys are tied through at least two \
earlier Rule-1a layers" (decide (2 ≤ tied))
            checkTest s!"{name}: the first differing Rule-1a layer is layer 3"
              (decide (tied = 3))
            checkTest s!"{name}: the first sphere exposes the three multiple-bond copies on both sides"
              (decide (nth? (layerLengths left.constitutional.rule1a) 1 = some 3) &&
               decide (nth? (layerLengths right.constitutional.rule1a) 1 = some 3))
            let leftDiffering := nth? left.constitutional.rule1a tied
            let rightDiffering := nth? right.constitutional.rule1a tied
            checkTest s!"{name}: the first differing layer is the strict N-versus-C win"
              (match leftDiffering, rightDiffering with
               | some leftLayer, some rightLayer =>
                   decide (layerValues leftLayer = [7, 7, 7]) &&
                   decide (layerValues rightLayer = [6, 6, 6]) &&
                   decide (OfficialRuleMajorKey.compareSparseLayer
                     OfficialRuleMajorKey.compareNat leftLayer rightLayer = Ordering.gt)
               | _, _ => false)
            checkTest s!"{name}: the full Rule-1a projection comparison is decisive"
              (decide (OfficialRuleMajorKey.compareSparseLayers
                OfficialRuleMajorKey.compareNat
                left.constitutional.rule1a right.constitutional.rule1a = Ordering.gt))
            checkTest s!"{name}: the constitutional key comparison is decisive"
              (decide (OfficialRuleMajorKey.compare
                left.constitutional right.constitutional = Ordering.gt))
            checkTest s!"{name}: the actual Rule-3 spatial key comparison resolves the two ligands"
              (decide (input.certified.compareLocalizedRerootRecursiveRule3SpatialKeys
                left right = Ordering.gt))
            note s!"RESOLVE {name}: rule1a={repr (OfficialRuleMajorKey.compareSparseLayers
                OfficialRuleMajorKey.compareNat
                left.constitutional.rule1a right.constitutional.rule1a)}, \
constitutional={repr (OfficialRuleMajorKey.compare
                left.constitutional right.constitutional)}, \
rule3Key={repr (input.certified.compareLocalizedRerootRecursiveRule3SpatialKeys
                left right)}"
        | _, _ =>
            throw (IO.userError (name ++ ": missing carbon ligand key at index 2 or 3"))

  let finish ← IO.monoMsNow
  note s!"TIMING {name}: admission={admittedAt - start}ms, universal={universalMs}ms, \
total={finish - start}ms"
  note "SCOPE deep-triple: one direct final-centre target at the automatic carrier fuel only; \
no carrier-wide descriptor production or certificate replay. The R label is \
grounded in the established rank-ordered halomethane coordinate fixture, not in an external \
normative decision."
  IO.println "universal deep descriptor probe complete"

#eval main

end TetraStereo.Examples.LocalizedUniversalDeepDescriptorProbe
