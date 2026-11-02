import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace Rule3NormalizedHierarchyFidelity

open ChemistryNormalizationResult












































/-! ## The two enumerations of one molecular bond multiset -/

/-- Atom list shared by both molecules.

```
        1 --- 2                 ring through the (non-tetrahedral) centre 0
         \   /
           0
          / \
         3   12          branch roots P and Q (P = 3, Q = 12)
         |    |
        ...  ...
```

Branch `P` carries two independent alkene units, `4=5` and `8=9`; branch `Q` carries the
isomorphic pair `13=14` and `17=18`.  The alkene carbon substituents are fluorines,
which are the CIP-senior substituent at both ends of every unit (`F > C` at the near end
where the other substituent is the branch carbon, `F > H` at the far end). -/
def atoms : List AtomSpec :=
  [ { element := Element.C },  -- 0  centre (no tetrahedral annotation)
    { element := Element.C },  -- 1  ring
    { element := Element.C },  -- 2  ring
    { element := Element.C },  -- 3  branch root P
    { element := Element.C },  -- 4  P alkene endpoint, near
    { element := Element.C },  -- 5  P alkene endpoint, far
    { element := Element.F },  -- 6  substituent on 4 (CIP senior)
    { element := Element.F },  -- 7  substituent on 5 (CIP senior)
    { element := Element.C },  -- 8  P second alkene endpoint, near
    { element := Element.C },  -- 9  P second alkene endpoint, far
    { element := Element.F },  -- 10 substituent on 8 (CIP senior)
    { element := Element.F },  -- 11 substituent on 9 (CIP senior)
    { element := Element.C },  -- 12 branch root Q
    { element := Element.C },  -- 13 Q alkene endpoint, near
    { element := Element.C },  -- 14 Q alkene endpoint, far
    { element := Element.F },  -- 15 substituent on 13 (CIP senior)
    { element := Element.F },  -- 16 substituent on 14 (CIP senior)
    { element := Element.C },  -- 17 Q second alkene endpoint, near
    { element := Element.C },  -- 18 Q second alkene endpoint, far
    { element := Element.F },  -- 19 substituent on 17 (CIP senior)
    { element := Element.F } ] -- 20 substituent on 18 (CIP senior)

/-- One raw bond record. -/
def bond (source target : ℕ) (kind : ParsedBondKind) : RawBond :=
  { source := source, target := target, kind := kind }

/-- Bond enumeration A.

The two bonds out of `P` are listed `3-4` then `3-8`, and the two bonds out of `Q` are listed
`12-17` then `12-13`.  The breadth-first walk of `reachableAvoiding` follows exactly this list
order inside each layer.

The F substituent edges are genuine directional raw records:
`4-6 up`, `5-7 up` (Z); `8-10 up`, `9-11 down` (E); `13-15 up`, `14-16 up` (Z);
`17-19 up`, `18-20 down` (E). -/
def bondsA : List RawBond :=
  [ bond 0 1 ParsedBondKind.single,
    bond 1 2 ParsedBondKind.single,
    bond 2 0 ParsedBondKind.single,
    bond 0 3 ParsedBondKind.single,
    bond 0 12 ParsedBondKind.single,
    bond 3 4 ParsedBondKind.single,
    bond 3 8 ParsedBondKind.single,
    bond 4 5 ParsedBondKind.double,
    bond 4 6 ParsedBondKind.up,
    bond 5 7 ParsedBondKind.up,
    bond 8 9 ParsedBondKind.double,
    bond 8 10 ParsedBondKind.up,
    bond 9 11 ParsedBondKind.down,
    bond 12 17 ParsedBondKind.single,
    bond 12 13 ParsedBondKind.single,
    bond 13 14 ParsedBondKind.double,
    bond 13 15 ParsedBondKind.up,
    bond 14 16 ParsedBondKind.up,
    bond 17 18 ParsedBondKind.double,
    bond 17 19 ParsedBondKind.up,
    bond 18 20 ParsedBondKind.down ]

/-- Bond enumeration B.

This is literally the same list of raw bond records as `bondsA`; only the positions of the
parent-edge records `3-4` / `3-8` and `12-13` / `12-17` are exchanged.  Every atom, bond
kind, directional marker and endpoint is unchanged. -/
def bondsB : List RawBond :=
  [ bond 0 1 ParsedBondKind.single,
    bond 1 2 ParsedBondKind.single,
    bond 2 0 ParsedBondKind.single,
    bond 0 3 ParsedBondKind.single,
    bond 0 12 ParsedBondKind.single,
    bond 3 8 ParsedBondKind.single,
    bond 3 4 ParsedBondKind.single,
    bond 4 5 ParsedBondKind.double,
    bond 4 6 ParsedBondKind.up,
    bond 5 7 ParsedBondKind.up,
    bond 8 9 ParsedBondKind.double,
    bond 8 10 ParsedBondKind.up,
    bond 9 11 ParsedBondKind.down,
    bond 12 13 ParsedBondKind.single,
    bond 12 17 ParsedBondKind.single,
    bond 13 14 ParsedBondKind.double,
    bond 13 15 ParsedBondKind.up,
    bond 14 16 ParsedBondKind.up,
    bond 17 18 ParsedBondKind.double,
    bond 17 19 ParsedBondKind.up,
    bond 18 20 ParsedBondKind.down ]

/-- Molecule A: atom list `atoms`, bond enumeration `bondsA`. -/
def molA : RawMolecule := { atoms := atoms, bonds := bondsA }

/-- Molecule B: the same atom list, bond enumeration `bondsB`. -/
def molB : RawMolecule := { atoms := atoms, bonds := bondsB }

/-- The production normalization of A.  There is no `stereobonds` override anywhere. -/
def resultA : ChemistryNormalizationResult := normalizeRawMolecule molA

/-- The production normalization of B. -/
def resultB : ChemistryNormalizationResult := normalizeRawMolecule molB

/-- Hydrogen-materialized A, as used internally by `seniorSideAt?`. -/
def expandedA : RawMolecule := resultA.parsed.withExplicitHydrogens

/-- Hydrogen-materialized B. -/
def expandedB : RawMolecule := resultB.parsed.withExplicitHydrogens

/-- The exact internal fuel of `seniorSideAt?` on A. -/
def expandedFuelA : ℕ := 2 * expandedA.atomCount + 2

/-- The exact internal fuel of `seniorSideAt?` on B. -/
def expandedFuelB : ℕ := 2 * expandedB.atomCount + 2

/-- Production analysis fuel for both molecules (identical atom counts). -/
def fuel : ℕ := analysisFuel molA

/-! ## Parent-dominance regression input

Constitutionally different branch roots at the same depth: atom 12 is nitrogen instead of
carbon.  The Rule-3 arrangements are still the opposite ones of A and B, but the ancestor
ranking must decide before Rule 3 is consulted. -/
def atomsParent : List AtomSpec :=
  [ { element := Element.C },
    { element := Element.C },
    { element := Element.C },
    { element := Element.C },
    { element := Element.C },
    { element := Element.C },
    { element := Element.F },
    { element := Element.F },
    { element := Element.C },
    { element := Element.C },
    { element := Element.F },
    { element := Element.F },
    { element := Element.N },
    { element := Element.C },
    { element := Element.C },
    { element := Element.F },
    { element := Element.F },
    { element := Element.C },
    { element := Element.C },
    { element := Element.F },
    { element := Element.F } ]

/-- Parent-dominance molecule with bond enumeration A. -/
def molPA : RawMolecule := { atoms := atomsParent, bonds := bondsA }

/-- Parent-dominance molecule with bond enumeration B. -/
def molPB : RawMolecule := { atoms := atomsParent, bonds := bondsB }

/-- Production normalization of the A-ordered parent-dominance input. -/
def resultPA : ChemistryNormalizationResult := normalizeRawMolecule molPA

/-- Production normalization of the B-ordered parent-dominance input. -/
def resultPB : ChemistryNormalizationResult := normalizeRawMolecule molPB

/-- Production analysis fuel for the parent-dominance inputs. -/
def parentFuel : ℕ := analysisFuel molPA

/-! ## Positive unequal-geometry control

Same atoms and parent-edge ordering as A, but the second Q unit `17=18` is Z (its terminal
marker `18-20` is `up` instead of `down`).  Branch P therefore carries the geometry sequence
Z, E while branch Q carries Z, Z.  A strict, non-refusal comparison must exist here. -/
def bondsControl : List RawBond :=
  [ bond 0 1 ParsedBondKind.single,
    bond 1 2 ParsedBondKind.single,
    bond 2 0 ParsedBondKind.single,
    bond 0 3 ParsedBondKind.single,
    bond 0 12 ParsedBondKind.single,
    bond 3 4 ParsedBondKind.single,
    bond 3 8 ParsedBondKind.single,
    bond 4 5 ParsedBondKind.double,
    bond 4 6 ParsedBondKind.up,
    bond 5 7 ParsedBondKind.up,
    bond 8 9 ParsedBondKind.double,
    bond 8 10 ParsedBondKind.up,
    bond 9 11 ParsedBondKind.down,
    bond 12 17 ParsedBondKind.single,
    bond 12 13 ParsedBondKind.single,
    bond 13 14 ParsedBondKind.double,
    bond 13 15 ParsedBondKind.up,
    bond 14 16 ParsedBondKind.up,
    bond 17 18 ParsedBondKind.double,
    bond 17 19 ParsedBondKind.up,
    bond 18 20 ParsedBondKind.up ]

/-- Positive unequal-geometry control molecule. -/
def molControl : RawMolecule := { atoms := atoms, bonds := bondsControl }

/-- Production normalization of the positive control. -/
def resultControl : ChemistryNormalizationResult := normalizeRawMolecule molControl

/-! ## Inputs are admitted and the stereo is actually derived -/

theorem atoms_agree : molA.atoms = molB.atoms := rfl

theorem atomCount_agree : molA.atomCount = molB.atomCount := rfl

theorem bonds_perm : molA.bonds.Perm molB.bonds := by decide

theorem bonds_same_entries :
    molA.bonds.length = molB.bonds.length ∧
      molA.bonds.all (fun b => molB.bonds.contains b) = true ∧
      molB.bonds.all (fun b => molA.bonds.contains b) = true := by
  decide

theorem molA_admissible : molA.admissible? = true := by decide

theorem molB_admissible : molB.admissible? = true := by decide

theorem molA_stereochemicalAdmissible : molA.stereochemicalAdmissible? = true := by decide

theorem molB_stereochemicalAdmissible : molB.stereochemicalAdmissible? = true := by decide

theorem parsedA_admissible : resultA.parsed.admissible? = true := by decide

theorem parsedB_admissible : resultB.parsed.admissible? = true := by decide

theorem parsedA_stereochemicalAdmissible :
    resultA.parsed.stereochemicalAdmissible? = true := by decide

theorem parsedB_stereochemicalAdmissible :
    resultB.parsed.stereochemicalAdmissible? = true := by decide

/-- Published-API name for the admission fact (same statement as `parsedA_admissible`). -/
theorem resultA_admissible : resultA.parsed.admissible? = true := parsedA_admissible

/-- Published-API name for the admission fact (same statement as `parsedB_admissible`). -/
theorem resultB_admissible : resultB.parsed.admissible? = true := parsedB_admissible

/-- Published-API name for the stereochemical admission fact. -/
theorem resultA_stereochemicalAdmissible :
    resultA.parsed.stereochemicalAdmissible? = true :=
  parsedA_stereochemicalAdmissible

/-- Published-API name for the stereochemical admission fact. -/
theorem resultB_stereochemicalAdmissible :
    resultB.parsed.stereochemicalAdmissible? = true :=
  parsedB_stereochemicalAdmissible

theorem parsedA_atomCount : resultA.parsed.atomCount = 21 := by decide

theorem parsedB_atomCount : resultB.parsed.atomCount = 21 := by decide

theorem expandedA_atomCount : expandedA.atomCount = 31 := by decide

theorem expandedB_atomCount : expandedB.atomCount = 31 := by decide

theorem fuel_eq : fuel = analysisFuel molB := rfl

/-- The result handed to the Rule-3 layer is literally the production normalization. -/
theorem resultA_eq_normalized : resultA = normalizeRawMolecule molA := rfl

/-- The result handed to the Rule-3 layer is literally the production normalization. -/
theorem resultB_eq_normalized : resultB = normalizeRawMolecule molB := rfl

/-- The stereo record consumed by Rule 3 is exactly the one extracted from the raw bonds. -/
theorem stereobondsA_derived : resultA.stereobonds = stereobondSemantics molA := by decide

/-- The stereo record consumed by Rule 3 is exactly the one extracted from the raw bonds. -/
theorem stereobondsB_derived : resultB.stereobonds = stereobondSemantics molB := by decide

/-! ## Marker orientation and derived geometry -/

/-- The directional annotations extracted from A (reading order preserved). -/
theorem directionalBondsA :
    resultA.stereobonds.directionalBonds =
      [ { source := 4, target := 6, marker := DirectionalBondMarker.up },
        { source := 5, target := 7, marker := DirectionalBondMarker.up },
        { source := 8, target := 10, marker := DirectionalBondMarker.up },
        { source := 9, target := 11, marker := DirectionalBondMarker.down },
        { source := 13, target := 15, marker := DirectionalBondMarker.up },
        { source := 14, target := 16, marker := DirectionalBondMarker.up },
        { source := 17, target := 19, marker := DirectionalBondMarker.up },
        { source := 18, target := 20, marker := DirectionalBondMarker.down } ] := by
  decide

/-- The directional annotations extracted from B are the same records. -/
theorem directionalBondsB : resultB.stereobonds.directionalBonds =
    resultA.stereobonds.directionalBonds := by decide

/-- Every double bond has an `unspecified` stored assignment: no stereo was injected. -/
theorem assignmentsA :
    resultA.stereobonds.doubleBondAssignments =
      [ (4, 5, DoubleBondStereo.unspecified),
        (8, 9, DoubleBondStereo.unspecified),
        (13, 14, DoubleBondStereo.unspecified),
        (17, 18, DoubleBondStereo.unspecified) ] := by
  decide

/-- B derives the same four `unspecified` assignments (the double-bond records did not move
relative to one another). -/
theorem assignmentsB :
    resultB.stereobonds.doubleBondAssignments =
      [ (4, 5, DoubleBondStereo.unspecified),
        (8, 9, DoubleBondStereo.unspecified),
        (13, 14, DoubleBondStereo.unspecified),
        (17, 18, DoubleBondStereo.unspecified) ] := by
  decide

/-- The stored-assignment branch of `perceivedDoubleBondStereo?` is empty on every unit of A. -/
theorem storedA_none :
    [ resultA.stereobonds.storedDoubleBondStereo? 4 5,
      resultA.stereobonds.storedDoubleBondStereo? 8 9,
      resultA.stereobonds.storedDoubleBondStereo? 13 14,
      resultA.stereobonds.storedDoubleBondStereo? 17 18 ] =
      [ none, none, none, none ] := by
  decide

/-- The stored-assignment branch is empty on every unit of B as well. -/
theorem storedB_none :
    [ resultB.stereobonds.storedDoubleBondStereo? 4 5,
      resultB.stereobonds.storedDoubleBondStereo? 8 9,
      resultB.stereobonds.storedDoubleBondStereo? 13 14,
      resultB.stereobonds.storedDoubleBondStereo? 17 18 ] =
      [ none, none, none, none ] := by
  decide

/-- Reoriented marker values on both sides of every unit of A (near end first, far end second):
up/up, up/down, up/up, up/down. -/
theorem markersA :
    [ resultA.stereobonds.directionalMarkersAtSide 4 5,
      resultA.stereobonds.directionalMarkersAtSide 5 4,
      resultA.stereobonds.directionalMarkersAtSide 8 9,
      resultA.stereobonds.directionalMarkersAtSide 9 8,
      resultA.stereobonds.directionalMarkersAtSide 13 14,
      resultA.stereobonds.directionalMarkersAtSide 14 13,
      resultA.stereobonds.directionalMarkersAtSide 17 18,
      resultA.stereobonds.directionalMarkersAtSide 18 17 ] =
      [ [DirectionalBondMarker.up], [DirectionalBondMarker.up],
        [DirectionalBondMarker.up], [DirectionalBondMarker.down],
        [DirectionalBondMarker.up], [DirectionalBondMarker.up],
        [DirectionalBondMarker.up], [DirectionalBondMarker.down] ] := by
  decide

/-- The same reoriented marker values on B. -/
theorem markersB :
    [ resultB.stereobonds.directionalMarkersAtSide 4 5,
      resultB.stereobonds.directionalMarkersAtSide 5 4,
      resultB.stereobonds.directionalMarkersAtSide 8 9,
      resultB.stereobonds.directionalMarkersAtSide 9 8,
      resultB.stereobonds.directionalMarkersAtSide 13 14,
      resultB.stereobonds.directionalMarkersAtSide 14 13,
      resultB.stereobonds.directionalMarkersAtSide 17 18,
      resultB.stereobonds.directionalMarkersAtSide 18 17 ] =
      [ [DirectionalBondMarker.up], [DirectionalBondMarker.up],
        [DirectionalBondMarker.up], [DirectionalBondMarker.down],
        [DirectionalBondMarker.up], [DirectionalBondMarker.up],
        [DirectionalBondMarker.up], [DirectionalBondMarker.down] ] := by
  decide

/-- The CIP-senior substituent at both ends of every unit of A is the fluorine:
`6,7,10,11,15,16,19,20`.  This is computed on the hydrogen-materialized molecule with the
same fuel `seniorSideAt?` uses. -/
theorem seniorA :
    [ expandedA.seniorAlkeneSubstituent? expandedFuelA 4 5,
      expandedA.seniorAlkeneSubstituent? expandedFuelA 5 4,
      expandedA.seniorAlkeneSubstituent? expandedFuelA 8 9,
      expandedA.seniorAlkeneSubstituent? expandedFuelA 9 8,
      expandedA.seniorAlkeneSubstituent? expandedFuelA 13 14,
      expandedA.seniorAlkeneSubstituent? expandedFuelA 14 13,
      expandedA.seniorAlkeneSubstituent? expandedFuelA 17 18,
      expandedA.seniorAlkeneSubstituent? expandedFuelA 18 17 ] =
      [ some 6, some 7, some 10, some 11, some 15, some 16, some 19, some 20 ] := by
  decide

/-- The same senior selection on B. -/
theorem seniorB :
    [ expandedB.seniorAlkeneSubstituent? expandedFuelB 4 5,
      expandedB.seniorAlkeneSubstituent? expandedFuelB 5 4,
      expandedB.seniorAlkeneSubstituent? expandedFuelB 8 9,
      expandedB.seniorAlkeneSubstituent? expandedFuelB 9 8,
      expandedB.seniorAlkeneSubstituent? expandedFuelB 13 14,
      expandedB.seniorAlkeneSubstituent? expandedFuelB 14 13,
      expandedB.seniorAlkeneSubstituent? expandedFuelB 17 18,
      expandedB.seniorAlkeneSubstituent? expandedFuelB 18 17 ] =
      [ some 6, some 7, some 10, some 11, some 15, some 16, some 19, some 20 ] := by
  decide

/-- The senior side at both ends of every unit of A: up/up, up/down, up/up, up/down. -/
theorem seniorSidesA :
    [ resultA.seniorSideAt? 4 5,
      resultA.seniorSideAt? 5 4,
      resultA.seniorSideAt? 8 9,
      resultA.seniorSideAt? 9 8,
      resultA.seniorSideAt? 13 14,
      resultA.seniorSideAt? 14 13,
      resultA.seniorSideAt? 17 18,
      resultA.seniorSideAt? 18 17 ] =
      [ some DirectionalBondMarker.up, some DirectionalBondMarker.up,
        some DirectionalBondMarker.up, some DirectionalBondMarker.down,
        some DirectionalBondMarker.up, some DirectionalBondMarker.up,
        some DirectionalBondMarker.up, some DirectionalBondMarker.down ] := by
  decide

/-- The same senior sides on B. -/
theorem seniorSidesB :
    [ resultB.seniorSideAt? 4 5,
      resultB.seniorSideAt? 5 4,
      resultB.seniorSideAt? 8 9,
      resultB.seniorSideAt? 9 8,
      resultB.seniorSideAt? 13 14,
      resultB.seniorSideAt? 14 13,
      resultB.seniorSideAt? 17 18,
      resultB.seniorSideAt? 18 17 ] =
      [ some DirectionalBondMarker.up, some DirectionalBondMarker.up,
        some DirectionalBondMarker.up, some DirectionalBondMarker.down,
        some DirectionalBondMarker.up, some DirectionalBondMarker.up,
        some DirectionalBondMarker.up, some DirectionalBondMarker.down ] := by
  decide

/-- CIP `E/Z` derived from the senior fluorine sides in A: Z, E, Z, E. -/
theorem cipA :
    [ resultA.cipDoubleBondStereo? 4 5,
      resultA.cipDoubleBondStereo? 8 9,
      resultA.cipDoubleBondStereo? 13 14,
      resultA.cipDoubleBondStereo? 17 18 ] =
      [ some DoubleBondStereo.Z, some DoubleBondStereo.E,
        some DoubleBondStereo.Z, some DoubleBondStereo.E ] := by
  decide

/-- CIP `E/Z` derived from the senior fluorine sides in B is the same per unit. -/
theorem cipB :
    [ resultB.cipDoubleBondStereo? 4 5,
      resultB.cipDoubleBondStereo? 8 9,
      resultB.cipDoubleBondStereo? 13 14,
      resultB.cipDoubleBondStereo? 17 18 ] =
      [ some DoubleBondStereo.Z, some DoubleBondStereo.E,
        some DoubleBondStereo.Z, some DoubleBondStereo.E ] := by
  decide

/-- The production `perceivedDoubleBondStereo?` on A: Z, E, Z, E. -/
theorem perceivedA :
    [ resultA.perceivedDoubleBondStereo? 4 5,
      resultA.perceivedDoubleBondStereo? 8 9,
      resultA.perceivedDoubleBondStereo? 13 14,
      resultA.perceivedDoubleBondStereo? 17 18 ] =
      [ some DoubleBondStereo.Z, some DoubleBondStereo.E,
        some DoubleBondStereo.Z, some DoubleBondStereo.E ] := by
  decide

/-- The production `perceivedDoubleBondStereo?` on B: Z, E, Z, E. -/
theorem perceivedB :
    [ resultB.perceivedDoubleBondStereo? 4 5,
      resultB.perceivedDoubleBondStereo? 8 9,
      resultB.perceivedDoubleBondStereo? 13 14,
      resultB.perceivedDoubleBondStereo? 17 18 ] =
      [ some DoubleBondStereo.Z, some DoubleBondStereo.E,
        some DoubleBondStereo.Z, some DoubleBondStereo.E ] := by
  decide

/-- Same physical geometry per unit, compared by per-unit lookup only (the assignment list
order is not assumed to match). -/
theorem geometry_agree_per_unit :
    [ resultA.perceivedDoubleBondStereo? 4 5,
      resultA.perceivedDoubleBondStereo? 8 9,
      resultA.perceivedDoubleBondStereo? 13 14,
      resultA.perceivedDoubleBondStereo? 17 18 ] =
    [ resultB.perceivedDoubleBondStereo? 4 5,
      resultB.perceivedDoubleBondStereo? 8 9,
      resultB.perceivedDoubleBondStereo? 13 14,
      resultB.perceivedDoubleBondStereo? 17 18 ] := by
  decide

/-! ## The predecessor flat Rule-3 diagnostic outputs change

The occurrence / signature facts below are retained diagnostics of the flat predecessor layer
(unchanged by the repair; their only live caller is now
`compareBranchesThroughRule3Legacy?`). -/

/-- Canonical Rule-3 occurrences of branch P in A.  The two units sit in the same
breadth-first layer; the `distance` fields are the raw list indices (`4` before `8`), so the
ascending sort places the Z unit before the E unit. -/
theorem occurrencesA_P :
    canonicalRule3OccurrencesOnBranch resultA molA fuel 0 3 =
      [ { left := 4, right := 5, near := 4, distance := 1,
          geometry := OfficialRule3Geometry.seqcis },
        { left := 8, right := 9, near := 8, distance := 2,
          geometry := OfficialRule3Geometry.seqtrans } ] := by
  decide

/-- The same branch in B: only the parent-edge enumeration changed, yet the near endpoint
`8` now has the smaller list index and the sequence is reversed. -/
theorem occurrencesB_P :
    canonicalRule3OccurrencesOnBranch resultB molB fuel 0 3 =
      [ { left := 8, right := 9, near := 8, distance := 1,
          geometry := OfficialRule3Geometry.seqtrans },
        { left := 4, right := 5, near := 4, distance := 2,
          geometry := OfficialRule3Geometry.seqcis } ] := by
  decide

theorem canonicalOccurrences_differ :
    canonicalRule3OccurrencesOnBranch resultA molA fuel 0 3 ≠
      canonicalRule3OccurrencesOnBranch resultB molB fuel 0 3 := by
  decide

/-- Branch Q of A retains the opposite sequence (its parent edges were listed in the other
relative order). -/
theorem occurrencesA_Q :
    canonicalRule3OccurrencesOnBranch resultA molA fuel 0 12 =
      [ { left := 17, right := 18, near := 17, distance := 1,
          geometry := OfficialRule3Geometry.seqtrans },
        { left := 13, right := 14, near := 13, distance := 2,
          geometry := OfficialRule3Geometry.seqcis } ] := by
  decide

/-- Branch Q of B is reversed relative to A. -/
theorem occurrencesB_Q :
    canonicalRule3OccurrencesOnBranch resultB molB fuel 0 12 =
      [ { left := 13, right := 14, near := 13, distance := 1,
          geometry := OfficialRule3Geometry.seqcis },
        { left := 17, right := 18, near := 17, distance := 2,
          geometry := OfficialRule3Geometry.seqtrans } ] := by
  decide

theorem signatureA_P : rule3CanonicalSignature resultA molA fuel 0 3 = [2, 1] := by
  decide

theorem signatureB_P : rule3CanonicalSignature resultB molB fuel 0 3 = [1, 2] := by
  decide

theorem signatureA_Q : rule3CanonicalSignature resultA molA fuel 0 12 = [1, 2] := by
  decide

theorem signatureB_Q : rule3CanonicalSignature resultB molB fuel 0 12 = [2, 1] := by
  decide

theorem signature_depends_on_bond_order :
    rule3CanonicalSignature resultA molA fuel 0 3 ≠
      rule3CanonicalSignature resultB molB fuel 0 3 := by
  decide

/-! ## Predecessor `compareBranchesThroughRule3Legacy?` outcomes (historical)

These `gt` / `lt` facts are scoped **only** to the explicitly named legacy comparator; the
corrected public gate is handled in the next section. -/

/-- Legacy predecessor: in A the two constitutionally identical branches P and Q are ranked P
above Q by the old flat Rule-3 gate. -/
theorem legacy_comparisonA_P_Q :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 = some Ordering.gt := by
  decide

/-- Historical name preserved as a legacy-scoped alias. -/
theorem comparisonA_P_Q :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 = some Ordering.gt :=
  legacy_comparisonA_P_Q

/-- Legacy predecessor: in B the same pair is ranked the other way round by the old flat gate. -/
theorem legacy_comparisonB_P_Q :
    compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 = some Ordering.lt := by
  decide

/-- Historical name preserved as a legacy-scoped alias. -/
theorem comparisonB_P_Q :
    compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 = some Ordering.lt :=
  legacy_comparisonB_P_Q

/-- Hence the predecessor flat Rule-3 comparison is not invariant under permutation of the
parent edge records, although atoms, bond multiset, raw markers and the derived geometry are
unchanged.  This is the historical defect, asserted about the legacy comparator only. -/
theorem legacy_comparison_depends_on_bond_order :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 ≠
      compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 := by
  decide

/-- Historical name preserved as a legacy-scoped alias. -/
theorem comparison_depends_on_bond_order :
    compareBranchesThroughRule3Legacy? resultA molA fuel 0 3 12 ≠
      compareBranchesThroughRule3Legacy? resultB molB fuel 0 3 12 :=
  legacy_comparison_depends_on_bond_order

/-! ## Corrected public Rule-3 successor on the same production-normalized input

Same `resultA`, `resultB`, `molA`, `molB`, `fuel` as above.  There is no stereo override: the
geometry was derived from the raw directional markers.  The corrected public comparator is
source-bound (path-indexed canonical branch keys), so the bond-record permutation no longer
changes its outcome.  Branch P and branch Q are physically isomorphic, hence the required
outcome is a genuine tie, not a refusal (`none`) and not a strict order. -/

/-- Successor: the corrected public Rule-3 gate returns a genuine tie for branches P and Q of
the production-normalized molecule A. -/
theorem publicComparisonA_P_Q :
    compareBranchesThroughRule3? resultA molA fuel 0 3 12 = some Ordering.eq := by
  decide +kernel

/-- Successor: the same genuine tie in the production-normalized molecule B, whose parent-edge
records are permuted. -/
theorem publicComparisonB_P_Q :
    compareBranchesThroughRule3? resultB molB fuel 0 3 12 = some Ordering.eq := by
  decide +kernel

/-- Successor: the corrected public Rule-3 outcome is invariant under the parent-edge
permutation.  Derived from the two exact outcomes, not re-decided. -/
theorem public_comparison_bond_order_invariant :
    compareBranchesThroughRule3? resultA molA fuel 0 3 12 =
      compareBranchesThroughRule3? resultB molB fuel 0 3 12 := by
  rw [publicComparisonA_P_Q, publicComparisonB_P_Q]

/-- Successor: the corrected public gate neither refuses nor orders the isomorphic pair. -/
theorem publicComparisonA_not_refused :
    compareBranchesThroughRule3? resultA molA fuel 0 3 12 ≠ none := by
  rw [publicComparisonA_P_Q]
  decide

/-! ## The two branches are physically isomorphic

Branch `P` (root 3) and branch `Q` (root 12) are exchanged by the index relabeling
`3↔12, 4↔13, 5↔14, 6↔15, 7↔16, 8↔17, 9↔18, 10↔19, 11↔20`, with the ring atoms fixed.
The relabeling is a graph and marker automorphism of each input, and it maps every alkene
unit of P onto the corresponding unit of Q with the same perceived geometry.  Consequently
the two branches are physically indistinguishable at the Rule-3 layer: any comparator that
is invariant under this relabeling must return a genuine tie for them.  The predecessor flat
comparator instead returns `gt` in A and `lt` in B (see above); the corrected public successor
returns `some eq` in both. -/
def swapBranches (n : ℕ) : ℕ :=
  match n with
  | 3 => 12 | 12 => 3
  | 4 => 13 | 13 => 4
  | 5 => 14 | 14 => 5
  | 6 => 15 | 15 => 6
  | 7 => 16 | 16 => 7
  | 8 => 17 | 17 => 8
  | 9 => 18 | 18 => 9
  | 10 => 19 | 19 => 10
  | 11 => 20 | 20 => 11
  | n => n

def renameBond (b : RawBond) : RawBond :=
  { b with source := swapBranches b.source, target := swapBranches b.target }

theorem swap_involution : (List.range 21).all (fun i => decide (swapBranches (swapBranches i) = i)) = true := by
  decide

theorem swap_atoms :
    (List.range 21).all (fun i => decide (atoms[swapBranches i]? = atoms[i]?)) = true := by
  decide

theorem swap_bondsA : (bondsA.map renameBond).Perm bondsA := by decide

theorem swap_bondsB : (bondsB.map renameBond).Perm bondsB := by decide

theorem swap_markersA :
    (resultA.stereobonds.directionalBonds.map fun a =>
        { a with source := swapBranches a.source, target := swapBranches a.target }).Perm
      resultA.stereobonds.directionalBonds := by
  decide

theorem swap_markersB :
    (resultB.stereobonds.directionalBonds.map fun a =>
        { a with source := swapBranches a.source, target := swapBranches a.target }).Perm
      resultB.stereobonds.directionalBonds := by
  decide

/-- Corresponding alkene units of P and Q carry identical perceived geometry in A. -/
theorem swap_geometryA :
    [ resultA.perceivedDoubleBondStereo? 4 5,
      resultA.perceivedDoubleBondStereo? 8 9 ] =
    [ resultA.perceivedDoubleBondStereo? 13 14,
      resultA.perceivedDoubleBondStereo? 17 18 ] := by
  decide

/-- Corresponding alkene units of P and Q carry identical perceived geometry in B. -/
theorem swap_geometryB :
    [ resultB.perceivedDoubleBondStereo? 4 5,
      resultB.perceivedDoubleBondStereo? 8 9 ] =
    [ resultB.perceivedDoubleBondStereo? 13 14,
      resultB.perceivedDoubleBondStereo? 17 18 ] := by
  decide

/-- The swap maps the P parent edge `0-3` to the Q parent edge `0-12` and conversely. -/
theorem swap_parentEdges :
    renameBond (bond 0 3 ParsedBondKind.single) = bond 0 12 ParsedBondKind.single ∧
      renameBond (bond 0 12 ParsedBondKind.single) = bond 0 3 ParsedBondKind.single := by
  decide

/-! ## Parent dominance: constitution at the ancestor decides before Rule 3

The constitutional outcome is preserved by the repair (the corrected public gate keeps the
same `compareBranchesStatus` / `compareBranchesAuthoritativeStatus` skeleton).  It is asserted
on the corrected public gate below, and the predecessor outcome is retained as an explicitly
named legacy theorem. -/

/-- Atom 12 is nitrogen in the parent-dominance inputs. -/
theorem parent_atom12 : atomsParent[12]? = some { element := Element.N } := by decide

theorem parentA_admissible : resultPA.parsed.admissible? = true := by decide

theorem parentB_admissible : resultPB.parsed.admissible? = true := by decide

/-- The same-depth Rule-3 arrangements remain the opposite ones of A and B. -/
theorem parentSignatureA_P : rule3CanonicalSignature resultPA molPA parentFuel 0 3 = [2, 1] := by
  decide

theorem parentSignatureB_P : rule3CanonicalSignature resultPB molPB parentFuel 0 3 = [1, 2] := by
  decide

theorem parentSignatureA_Q : rule3CanonicalSignature resultPA molPA parentFuel 0 12 = [1, 2] := by
  decide

theorem parentSignatureB_Q : rule3CanonicalSignature resultPB molPB parentFuel 0 12 = [2, 1] := by
  decide

/-- In A the sibling signatures still differ, so Rule 3 is non-trivial on this shape. -/
theorem parentRule3ArrangementsDifferA :
    rule3CanonicalSignature resultPA molPA parentFuel 0 3 ≠
      rule3CanonicalSignature resultPA molPA parentFuel 0 12 := by
  decide

/-- In B they differ in the opposite direction. -/
theorem parentRule3ArrangementsDifferB :
    rule3CanonicalSignature resultPB molPB parentFuel 0 3 ≠
      rule3CanonicalSignature resultPB molPB parentFuel 0 12 := by
  decide

/-- The ancestor constitution (`3` carbon versus `12` nitrogen) makes branch 3 lower. -/
theorem parentStatusA : molPA.compareBranchesStatus parentFuel 0 3 12 =
    RawMolecule.BranchComparisonStatus.lower := by
  decide

theorem parentAuthoritativeStatusA : molPA.compareBranchesAuthoritativeStatus 0 3 12 =
    RawMolecule.BranchComparisonStatus.lower := by
  decide

/-- The same ancestor result under the opposite parent-edge enumeration. -/
theorem parentStatusB : molPB.compareBranchesStatus parentFuel 0 3 12 =
    RawMolecule.BranchComparisonStatus.lower := by
  decide

theorem parentAuthoritativeStatusB : molPB.compareBranchesAuthoritativeStatus 0 3 12 =
    RawMolecule.BranchComparisonStatus.lower := by
  decide

/-- Predecessor flat gate: `some lt` in A even though the same-depth Rule-3 arrangement alone
would rank P above Q. -/
theorem legacy_parentDominanceA :
    compareBranchesThroughRule3Legacy? resultPA molPA parentFuel 0 3 12 =
      some Ordering.lt := by
  decide

/-- Predecessor flat gate under the opposite enumeration: unchanged `lt`. -/
theorem legacy_parentDominanceB :
    compareBranchesThroughRule3Legacy? resultPB molPB parentFuel 0 3 12 =
      some Ordering.lt := by
  decide

/-- The predecessor ancestor ranking is retained under the parent-edge permutation. -/
theorem legacy_parentDominance_same :
    compareBranchesThroughRule3Legacy? resultPA molPA parentFuel 0 3 12 =
      compareBranchesThroughRule3Legacy? resultPB molPB parentFuel 0 3 12 := by
  decide

/-- Successor: the corrected public gate still returns `lt` in A; the ancestor constitution
decides before Rule 3 is consulted. -/
theorem parentDominanceA :
    compareBranchesThroughRule3? resultPA molPA parentFuel 0 3 12 = some Ordering.lt := by
  decide

/-- Successor: unchanged `lt` under the opposite enumeration. -/
theorem parentDominanceB :
    compareBranchesThroughRule3? resultPB molPB parentFuel 0 3 12 = some Ordering.lt := by
  decide

/-- Successor: the corrected public gate's parent-dominance outcome is invariant under the
parent-edge permutation. -/
theorem parentDominance_same :
    compareBranchesThroughRule3? resultPA molPA parentFuel 0 3 12 =
      compareBranchesThroughRule3? resultPB molPB parentFuel 0 3 12 := by
  rw [parentDominanceA, parentDominanceB]

/-! ## Positive unequal-geometry control

Genuinely unequal geometry must remain strictly ordered after the repair.  The predecessor
flat outcome is retained as `legacy_controlComparison`; the successor assertion
`controlComparison` is the corrected public gate. -/

/-- Branch P of the control carries Z, E (flat diagnostic). -/
theorem controlSignature_P :
    rule3CanonicalSignature resultControl molControl fuel 0 3 = [2, 1] := by
  decide

/-- Branch Q of the control carries Z, Z (flat diagnostic). -/
theorem controlSignature_Q :
    rule3CanonicalSignature resultControl molControl fuel 0 12 = [2, 2] := by
  decide

theorem controlSignatures_differ :
    rule3CanonicalSignature resultControl molControl fuel 0 3 ≠
      rule3CanonicalSignature resultControl molControl fuel 0 12 := by
  decide

/-- Predecessor flat gate on the positive control: strictly ordered. -/
theorem legacy_controlComparison :
    compareBranchesThroughRule3Legacy? resultControl molControl fuel 0 3 12 =
      some Ordering.lt := by
  decide

theorem legacy_controlComparison_not_refused :
    compareBranchesThroughRule3Legacy? resultControl molControl fuel 0 3 12 ≠ none := by
  decide

theorem legacy_controlComparison_not_tied :
    compareBranchesThroughRule3Legacy? resultControl molControl fuel 0 3 12
      ≠ some Ordering.eq := by
  decide

/-- Successor: genuinely unequal geometry is strictly ordered by the corrected public gate:
not a refusal (`none`) and not a tie (`some eq`).  Any repair that blanket-refuses or ties all
pairs fails this control. -/
theorem controlComparison :
    compareBranchesThroughRule3? resultControl molControl fuel 0 3 12 = some Ordering.lt := by
  decide +kernel

theorem controlComparison_not_refused :
    compareBranchesThroughRule3? resultControl molControl fuel 0 3 12 ≠ none := by
  rw [controlComparison]
  decide

theorem controlComparison_not_tied :
    compareBranchesThroughRule3? resultControl molControl fuel 0 3 12
      ≠ some Ordering.eq := by
  rw [controlComparison]
  decide

/-! ## Kernel-authority guards -/

assert_kernel_only atoms_agree
assert_kernel_only atomCount_agree
assert_kernel_only bonds_perm
assert_kernel_only bonds_same_entries
assert_kernel_only molA_admissible
assert_kernel_only molB_admissible
assert_kernel_only molA_stereochemicalAdmissible
assert_kernel_only molB_stereochemicalAdmissible
assert_kernel_only parsedA_admissible
assert_kernel_only parsedB_admissible
assert_kernel_only parsedA_stereochemicalAdmissible
assert_kernel_only parsedB_stereochemicalAdmissible
assert_kernel_only resultA_admissible
assert_kernel_only resultB_admissible
assert_kernel_only resultA_stereochemicalAdmissible
assert_kernel_only resultB_stereochemicalAdmissible
assert_kernel_only parsedA_atomCount
assert_kernel_only parsedB_atomCount
assert_kernel_only expandedA_atomCount
assert_kernel_only expandedB_atomCount
assert_kernel_only fuel_eq
assert_kernel_only resultA_eq_normalized
assert_kernel_only resultB_eq_normalized
assert_kernel_only stereobondsA_derived
assert_kernel_only stereobondsB_derived
assert_kernel_only directionalBondsA
assert_kernel_only directionalBondsB
assert_kernel_only assignmentsA
assert_kernel_only assignmentsB
assert_kernel_only storedA_none
assert_kernel_only storedB_none
assert_kernel_only markersA
assert_kernel_only markersB
assert_kernel_only seniorA
assert_kernel_only seniorB
assert_kernel_only seniorSidesA
assert_kernel_only seniorSidesB
assert_kernel_only cipA
assert_kernel_only cipB
assert_kernel_only perceivedA
assert_kernel_only perceivedB
assert_kernel_only geometry_agree_per_unit
assert_kernel_only occurrencesA_P
assert_kernel_only occurrencesB_P
assert_kernel_only canonicalOccurrences_differ
assert_kernel_only occurrencesA_Q
assert_kernel_only occurrencesB_Q
assert_kernel_only signatureA_P
assert_kernel_only signatureB_P
assert_kernel_only signatureA_Q
assert_kernel_only signatureB_Q
assert_kernel_only signature_depends_on_bond_order
assert_kernel_only legacy_comparisonA_P_Q
assert_kernel_only comparisonA_P_Q
assert_kernel_only legacy_comparisonB_P_Q
assert_kernel_only comparisonB_P_Q
assert_kernel_only legacy_comparison_depends_on_bond_order
assert_kernel_only comparison_depends_on_bond_order
assert_kernel_only publicComparisonA_P_Q
assert_kernel_only publicComparisonB_P_Q
assert_kernel_only public_comparison_bond_order_invariant
assert_kernel_only publicComparisonA_not_refused
assert_kernel_only swap_involution
assert_kernel_only swap_atoms
assert_kernel_only swap_bondsA
assert_kernel_only swap_bondsB
assert_kernel_only swap_markersA
assert_kernel_only swap_markersB
assert_kernel_only swap_geometryA
assert_kernel_only swap_geometryB
assert_kernel_only swap_parentEdges
assert_kernel_only parent_atom12
assert_kernel_only parentA_admissible
assert_kernel_only parentB_admissible
assert_kernel_only parentSignatureA_P
assert_kernel_only parentSignatureB_P
assert_kernel_only parentSignatureA_Q
assert_kernel_only parentSignatureB_Q
assert_kernel_only parentRule3ArrangementsDifferA
assert_kernel_only parentRule3ArrangementsDifferB
assert_kernel_only parentStatusA
assert_kernel_only parentAuthoritativeStatusA
assert_kernel_only parentStatusB
assert_kernel_only parentAuthoritativeStatusB
assert_kernel_only legacy_parentDominanceA
assert_kernel_only legacy_parentDominanceB
assert_kernel_only legacy_parentDominance_same
assert_kernel_only parentDominanceA
assert_kernel_only parentDominanceB
assert_kernel_only parentDominance_same
assert_kernel_only controlSignature_P
assert_kernel_only controlSignature_Q
assert_kernel_only controlSignatures_differ
assert_kernel_only legacy_controlComparison
assert_kernel_only legacy_controlComparison_not_refused
assert_kernel_only legacy_controlComparison_not_tied
assert_kernel_only controlComparison
assert_kernel_only controlComparison_not_refused
assert_kernel_only controlComparison_not_tied

end Rule3NormalizedHierarchyFidelity
end OneCenter
end TetraStereo
