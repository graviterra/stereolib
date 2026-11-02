import TetraStereo.OneCenter.LocalizedNoDoubleReferenceInput

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

open OneCenter
open OneCenter.LocalizedNoDoubleReference

/-!
# Data fixtures for the localized no-double-bond reference evaluation

This module holds *data only*: source records, SMILES texts, and exact rational coordinates.  Every
fixture is admitted through the executable, fail-closed intake of `LocalizedNoDoubleReferenceInput`
(`admitSource?` for format-neutral source records, `admitSmilesSpatial?` for OpenSMILES text).  No
per-molecule `.get` certificate, no handwritten admission proof and no family theorem appears here,
so a fixture can only claim what admission actually returns.

The module is deliberately independent of any descriptor pipeline: it imports the checked intake
only, and its `#eval` block prints an admission summary per fixture.

## Geometry

The baseline halomethane copies the five-atom source record and the five rational positions of
`Examples/AuthoritativeLocalizedCIPAnalysis`.  Every other fixture uses synthetic coordinates
`(i, i², i³)` on the moment curve, one point per *hydrogen-expanded* atom, with the count read from
the actual parse.  This is a synthetic nondegenerate geometry, not a physical conformer: distinct
indices on the moment curve give affinely independent point sets, so no centre and three of its
neighbours are ever coplanar.  Branch `@`/`@@` annotations are topology fixtures only; they fix the
written neighbour order, not the coordinates.  Spatial outcomes are determined solely by the
supplied coordinates.

## Residual work

Nothing here evaluates a descriptor, and nothing here claims that a fixture's annotation agrees
with its coordinates.  The descriptor-level regression lives in a separate module.
-/

/-! ## Element spellings -/

/-- Checked periodic-table element spelling. -/
def periodicElement (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

abbrev carbon : PeriodicElement := periodicElement 6 (by decide) (by decide)
abbrev nitrogen : PeriodicElement := periodicElement 7 (by decide) (by decide)
abbrev fluorine : PeriodicElement := periodicElement 9 (by decide) (by decide)
abbrev chlorine : PeriodicElement := periodicElement 17 (by decide) (by decide)
abbrev bromine : PeriodicElement := periodicElement 35 (by decide) (by decide)
abbrev iodine : PeriodicElement := periodicElement 53 (by decide) (by decide)

/-- A neutral, unlabelled atom of one element. -/
def atom (element : PeriodicElement) : SemanticAtom := { element := element }

/-! ## The moment curve -/

/-- The `index`-th moment-curve point `(i, i², i³)`, exactly in `ℚ`. -/
def momentCurvePoint (index : ℕ) : CartesianPoint3 :=
  { x := (index : ℚ)
    y := (index : ℚ) * (index : ℚ)
    z := (index : ℚ) * (index : ℚ) * (index : ℚ) }

/-- `count` exact moment-curve points, indexed by atom index. -/
def momentCurve (count : ℕ) : SpatialConfiguration :=
  { positions := (List.range count).map momentCurvePoint }

/-- The hydrogen-expanded molecule of a SMILES fixture, when the certified parse succeeds. -/
def expandedMolecule? (text : String) : Option RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified text with
  | Except.error _ => none
  | Except.ok certified => some certified.result.parsed.withExplicitHydrogens

/-- Synthetic geometry with exactly one moment-curve point per hydrogen-expanded atom.  The count is
read from the actual certified parse, so the coordinate list indices the expanded atom list by
construction; a parse failure yields the empty configuration, which cannot be admitted. -/
def syntheticSpatial (text : String) : SpatialConfiguration :=
  match expandedMolecule? text with
  | none => { positions := [] }
  | some molecule => momentCurve molecule.atomCount

/-- Exchange two positions, preserving the coordinate count and every other entry. -/
def swapPositions (spatial : SpatialConfiguration) (first second : ℕ) : SpatialConfiguration :=
  { positions :=
      (List.range spatial.positions.length).map fun index =>
        let source := if index = first then second else if index = second then first else index
        match spatial.positions[source]? with
        | some point => point
        | none => { x := 0, y := 0, z := 0 } }

/-! ## The baseline five-atom halomethane

Source record and rational positions copied from `Examples/AuthoritativeLocalizedCIPAnalysis`
(nothing else is copied: admission runs through the executable intake rather than a stored
certificate). -/

def halomethaneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [{ element := carbon }, { element := fluorine }, { element := chlorine },
           { element := bromine }, { element := iodine }]
        interactions :=
          [{ participants := [0, 1], kind := .covalent 1 },
           { participants := [0, 2], kind := .covalent 1 },
           { participants := [0, 3], kind := .covalent 1 },
           { participants := [0, 4], kind := .covalent 1 }] }
    spatial? := some
      { positions :=
          [{ x := 0, y := 0, z := 0 },
           { x := -1, y := -1, z := 1 },
           { x := -1, y := 1, z := -1 },
           { x := 1, y := -1, z := -1 },
           { x := 1, y := 1, z := 1 }] } }

/-- Executable admission of the baseline. -/
def halomethane : Option Input := admitSource? halomethaneSource

/-- The same constitution with no spatial evidence channel at all.  Intake imposes no coordinate
obligation when the channel is absent, so this is expected to be admitted; whether a descriptor can
be produced without coordinates is a separate, downstream question. -/
def halomethaneWithoutSpatialSource : AuthoritativeChemicalInput :=
  { halomethaneSource with spatial? := none }

/-- Executable admission of the coordinate-free baseline. -/
def halomethaneWithoutSpatial : Option Input := admitSource? halomethaneWithoutSpatialSource

/-! ## Negative data fixtures -/

/-- A genuine double bond between two carbons: the source-record restriction must reject it. -/
def etheneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [atom carbon, atom carbon]
        interactions := [{ participants := [0, 1], kind := .covalent 2 }] }
    spatial? := some (momentCurve 2) }

/-- Executable admission of the double-bond source. -/
def ethene : Option Input := admitSource? etheneSource

/-- The baseline source with one position too few: the structural index agreement must reject it. -/
def shortSpatialHalomethaneSource : AuthoritativeChemicalInput :=
  { halomethaneSource with
      spatial? :=
        some { positions :=
          (halomethaneSource.spatial?.getD { positions := [] }).positions.drop 1 } }

/-- Executable admission of the truncated-configuration baseline. -/
def shortSpatialHalomethane : Option Input := admitSource? shortSpatialHalomethaneSource

/-! ## SMILES fixtures -/

/-- One SMILES fixture: the source text and the exact coordinates handed to intake. -/
structure Fixture where
  name : String
  smiles : String
  spatial : SpatialConfiguration

/-- Executable admission of one fixture. -/
def Fixture.admitted (fixture : Fixture) : Except ParserError (Option Input) :=
  admitSmilesSpatial? fixture.smiles fixture.spatial

/-- A three-membered ring: the annotated carbon keeps one written hydrogen, so the certified
hydrogen-expanded atom list is longer than the parsed one. -/
def ringSmiles : String := "[C@H]([F])([CH]([Cl])[CH2]1)1"

def ringSpatial : SpatialConfiguration := syntheticSpatial ringSmiles

def ring : Fixture := { name := "ring", smiles := ringSmiles, spatial := ringSpatial }

/-- A nitrile: the restriction excludes bond order two and permits order three. -/
def nitrileSmiles : String := "[C@H]([F])([C]#[N])[CH]([NH2])[CH3]"

def nitrileSpatial : SpatialConfiguration := syntheticSpatial nitrileSmiles

def nitrile : Fixture :=
  { name := "nitrile", smiles := nitrileSmiles, spatial := nitrileSpatial }

/-- An acyclic centre whose two branches are constitutionally distinct only far from the centre. -/
def deepSmiles : String := "F[C@H](CCCCl)CCCBr"

def deepSpatial : SpatialConfiguration := syntheticSpatial deepSmiles

def deep : Fixture := { name := "deep", smiles := deepSmiles, spatial := deepSpatial }

/-- Two constitutionally identical `CH(F)(Cl)` branches around a central carbon, all atoms written
explicitly.  Written atom order: `0` H, `1` C (central), `2` C (first branch), `3` H, `4` F, `5` Cl,
`6` Br, `7` C (second branch), `8` H, `9` F, `10` Cl.  Because the two carbon branches share a
constitution, only auxiliary/spatial evidence can separate them. -/
def interactingSmiles : String := "[H][C@]([C@]([H])([F])[Cl])([Br])[C@@]([H])([F])[Cl]"

def interactingSpatial : SpatialConfiguration := syntheticSpatial interactingSmiles

def interacting : Fixture :=
  { name := "interacting", smiles := interactingSmiles, spatial := interactingSpatial }

/-- The same fixture with the fluorine and chlorine coordinates of the first branch exchanged
(positions `4` and `5`).  Every other coordinate is untouched, so any output difference is produced
by that exchange alone. -/
def interactingVariationSpatial : SpatialConfiguration :=
  swapPositions interactingSpatial 4 5

def interactingVariation : Fixture :=
  { name := "interacting-variation", smiles := interactingSmiles,
    spatial := interactingVariationSpatial }

/-! ## Executable reporting -/

/-- Total one-line summary of one admission outcome: parse failures, fail-closed rejections and
admissions are all reported, never filtered. -/
def admitSummary (name : String) (outcome : Except ParserError (Option Input)) : String :=
  match outcome with
  | Except.error message => name ++ ": parse/normalization error: " ++ message
  | Except.ok none => name ++ ": not admitted (checked intake returned none)"
  | Except.ok (some input) =>
      name ++ ": admitted; hydrogen-expanded atoms = " ++ toString (Input.molecule input).atomCount ++
        "; spatial evidence present = " ++
          toString (Input.authority input).input.spatial?.isSome ++
        "; localized source records = " ++
          toString (Input.molecule input).localizedCovalentRecords.length

/-- Element spelling of one hydrogen-expanded atom of a SMILES fixture, for index diagnostics. -/
def expandedElement? (text : String) (index : ℕ) : Option Element :=
  match expandedMolecule? text with
  | none => none
  | some molecule => (molecule.atomAt? index).map AtomSpec.element

/-- Expanded atom-indexed element spellings of the interacting fixture. -/
def interactingElements : List (Option ℕ) :=
  (List.range 11).map fun index => (expandedElement? interactingSmiles index).map Element.atomicNumber

end TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures
