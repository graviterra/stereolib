import TetraStereo.OneCenter.CIPP93NoncarbonTetrahedralNormalization
import TetraStereo.OneCenter.RawSourceHydrogenPolicy
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace TetraStereo
namespace OneCenter
namespace P93SourceHydrogenFidelity

open RawMolecule
open TetraStereo.OneCenter.BlueBookP93.NoncarbonTetrahedra.Production

/-!
# Source-hydrogen fidelity of the repaired P-93.2 production entry point

## Target

This module is written against the production repair in which `normalizeRawMoleculeP93` freezes the
*source* hydrogen counts before applying the P-93.2 quotient:

`normalizeRawMoleculeP93 mol cycles =
  normalizeRawMolecule (normalize (freezeSourceHydrogenCounts mol)) cycles`.

It deliberately does **not** compile against the pre-repair body
`normalizeRawMolecule (normalize mol) cycles`: the theorem below is false for that body, and the
`Legacy` diagnostics at the end of this file exhibit the failure.  The file is therefore delivered
for integration together with the production repair, not as a drop-in for the old module.

## Main result

`normalizeRawMoleculeP93_hydrogenCountAt` states, for every raw molecule, every cycle list and every
atom index,

`(normalizeRawMoleculeP93 mol cycles).parsed.hydrogenCountAt index = mol.hydrogenCountAt index`.

No hypothesis on the molecule and no supplied pointwise equality is used.  The proof follows the
actual definitions:

* `freezeSourceHydrogenCounts` writes `mol.hydrogenCountAt index` into every atom's
  `explicitHydrogens?` policy (`freezeSourceHydrogenCounts_atomAt?`);
* the P-93.2 atom map `normalizeAtom` preserves the stored policy, so the quotient cannot lose the
  frozen count (`normalizeAtom_frozen_explicitHydrogens?_eq`, `normalize_atomAt?`);
* `normalizeUnspecifiedBonds` preserves the implied count
  (`normalizeUnspecifiedBonds_hydrogenCountAt`).

Since the statement is fully general it covers N/P/S oxo centers, the Se/Te analogues named by
P-93.2.4--.5, bracket atoms with an explicit count, and hand-built raw records alike.  No
element-specific chalcogen fixtures are duplicated here.

`normalizeRawMoleculeP93_expanded_atomCount` lifts the pointwise result to the graph consumed by
descriptor ranking: the hydrogen-expanded atom count is the source atom count plus the sum of the
source hydrogen counts.

## Concrete source regressions

`phosphoricAcidSource` and `sulfuricAcidSource` are the parser images of `P(=O)(O)(O)O` and
`S(=O)(O)(O)O`.  Their source hydrogen vectors are `[0,0,1,1,1]` and `[1,0,1,1,1]`.  The bracket
controls `[S](=O)(O)(O)O`, `[SH](=O)(O)(O)O` and `P(=O)(O)(O)[O]` show that a written `some n`
policy is respected rather than refilled from the lowered bond order.

## Diagnostic boundary

`normalizeRawMoleculeP93Legacy` reproduces the pre-repair pipeline under a new, local name.  It is
**diagnostic only** and must not be used by authority-facing code.  Its theorems record the defect
the repair removes: for `S(=O)(O)(O)O` the legacy pipeline moves sulfur's source hydrogen onto the
oxo oxygen, and for `P(=O)(O)(O)O` it invents two hydrogens that the written source does not carry.
-/

/-! ## Atom count of the hydrogen-expanded graph

The expansion `RawMolecule.withExplicitHydrogens` appends `mol.hydrogenCountAt index` fresh hydrogen
atoms at every source index.  The lemmas below record that fact for the production definition; they
are the expansion side used by `normalizeRawMoleculeP93_expanded_atomCount`. -/

/-- One materialization step appends exactly `mol.hydrogenCountAt index` fresh atoms. -/
theorem withExplicitHydrogensStep_atoms_length (mol : RawMolecule)
    (state : HydrogenExpansionState) (index : Nat) :
    (withExplicitHydrogensStep mol state index).1.length =
      state.1.length + mol.hydrogenCountAt index := by
  by_cases zero : mol.hydrogenCountAt index == 0
  · have countZero : mol.hydrogenCountAt index = 0 := by simpa using zero
    simp [withExplicitHydrogensStep, countZero]
  · simp only [withExplicitHydrogensStep, if_neg zero]
    simp [List.length_append, List.length_replicate]

/-- The atom-list length of an expansion fold accumulates the hydrogen counts of the visited
indices. -/
theorem fold_withExplicitHydrogensStep_atoms_length (mol : RawMolecule)
    (indices : List Nat) (state : HydrogenExpansionState) :
    (indices.foldl (withExplicitHydrogensStep mol) state).1.length =
      state.1.length + (indices.map mol.hydrogenCountAt).sum := by
  induction indices generalizing state with
  | nil => simp
  | cons index rest inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis (withExplicitHydrogensStep mol state index)]
      simp only [List.map_cons, List.sum_cons]
      rw [withExplicitHydrogensStep_atoms_length]
      omega

/-- The expanded molecule's atom count is the accumulator's: finalization canonicalizes only the
written-neighbour table. -/
theorem withExplicitHydrogens_atomCount_fold (mol : RawMolecule) :
    mol.withExplicitHydrogens.atomCount =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomCount := by
  simp [withExplicitHydrogens, withExactWrittenNeighbors, atomCount]

/-- The accumulator carries the source atom count plus the sum of the source hydrogen counts. -/
theorem hydrogenExpansionFold_atomCount_eq (mol : RawMolecule) :
    ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomCount =
      mol.atomCount + ((List.range mol.atomCount).map mol.hydrogenCountAt).sum := by
  have lengthForm := fold_withExplicitHydrogensStep_atoms_length mol (List.range mol.atomCount)
    (initialHydrogenExpansionState mol)
  simpa [atomCount, HydrogenExpansionState.toRawMolecule, initialHydrogenExpansionState,
    List.length_map] using lengthForm

/-- The hydrogen-expanded graph has exactly `mol.atomCount` source atoms plus the source hydrogen
counts summed over all source indices. -/
theorem withExplicitHydrogens_atomCount (mol : RawMolecule) :
    mol.withExplicitHydrogens.atomCount =
      mol.atomCount + ((List.range mol.atomCount).map mol.hydrogenCountAt).sum := by
  rw [withExplicitHydrogens_atomCount_fold, hydrogenExpansionFold_atomCount_eq]

/-! ## The repaired P-93.2 entry point preserves every source hydrogen count -/

/-- The P-93.2 atom map never rewrites the stored hydrogen policy.  This is the only atom field the
P-93.2 quotient could otherwise have used to change the count. -/
theorem normalizeAtom_frozen_explicitHydrogens?_eq (mol : RawMolecule) (index : Nat)
    (atom : AtomSpec) (count : Nat) :
    (normalizeAtom mol index { atom with explicitHydrogens? := some count }).explicitHydrogens? =
      some count := by
  by_cases insensitive : chargeInsensitiveAtom? mol index = true <;>
    by_cases eligible : chargeNormalizedElement atom.element = true <;>
      simp [normalizeAtom, insensitive, eligible]

/-- The P-93.2 quotient applied to a source-hydrogen-frozen graph keeps the exact source count at
every index.  This is the interior step of the repaired pipeline; it is stated locally so that the
present module compiles independently of where the shared equivalence packet is inserted. -/
theorem normalize_frozen_hydrogenCountAt (mol : RawMolecule) (index : Nat) :
    (normalize (freezeSourceHydrogenCounts mol)).hydrogenCountAt index =
      mol.hydrogenCountAt index := by
  cases sourceLookup : mol.atomAt? index with
  | none =>
      have frozenNone : (freezeSourceHydrogenCounts mol).atomAt? index = none := by
        rw [freezeSourceHydrogenCounts_atomAt?, sourceLookup]
        rfl
      have normalizedNone : (normalize (freezeSourceHydrogenCounts mol)).atomAt? index = none := by
        rw [normalize_atomAt?, frozenNone]
        rfl
      simp [RawMolecule.hydrogenCountAt, sourceLookup, normalizedNone]
  | some atom =>
      have frozenSome : (freezeSourceHydrogenCounts mol).atomAt? index =
          some { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) } := by
        rw [freezeSourceHydrogenCounts_atomAt?, sourceLookup]
        rfl
      have normalizedSome : (normalize (freezeSourceHydrogenCounts mol)).atomAt? index =
          some (normalizeAtom (freezeSourceHydrogenCounts mol) index
            { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) }) := by
        rw [normalize_atomAt?, frozenSome]
        rfl
      exact hydrogenCountAt_of_explicitHydrogens?_some
        (normalize (freezeSourceHydrogenCounts mol)) index (mol.hydrogenCountAt index)
        (normalizeAtom (freezeSourceHydrogenCounts mol) index
          { atom with explicitHydrogens? := some (mol.hydrogenCountAt index) })
        normalizedSome
        (normalizeAtom_frozen_explicitHydrogens?_eq (freezeSourceHydrogenCounts mol) index atom
          (mol.hydrogenCountAt index))

/-- The `.parsed` component of the repaired entry point is the default-bond normalization of the
source-hydrogen-frozen P-93.2 quotient.  The proof is `rfl`: it unfolds the production wrapper and
the `parsed` projection of `normalizeRawMolecule`. -/
theorem normalizeRawMoleculeP93_parsed_frozen (mol : RawMolecule)
    (cycles : List AromaticCycle) :
    (normalizeRawMoleculeP93 mol cycles).parsed =
      (normalize (freezeSourceHydrogenCounts mol)).normalizeUnspecifiedBonds := rfl

/-- **Source-hydrogen fidelity of the repaired P-93.2 production entry point.**

For every raw molecule, every candidate aromatic-cycle list and every atom index, the parsed
molecule handed to the analyzer reports exactly the hydrogen count of the written source.  The count
is read after the P-93.2 quotient and after `normalizeUnspecifiedBonds`, so this is a statement about
the actual future wrapper, not about the freezing step alone. -/
theorem normalizeRawMoleculeP93_hydrogenCountAt (mol : RawMolecule)
    (cycles : List AromaticCycle) (index : Nat) :
    (normalizeRawMoleculeP93 mol cycles).parsed.hydrogenCountAt index =
      mol.hydrogenCountAt index := by
  rw [normalizeRawMoleculeP93_parsed_frozen,
    RawMolecule.normalizeUnspecifiedBonds_hydrogenCountAt,
    normalize_frozen_hydrogenCountAt]

/-- The repaired entry point keeps the source atom count; freezing, the P-93.2 quotient and
default-bond normalization are all atom-preserving. -/
theorem normalizeRawMoleculeP93_parsed_atomCount (mol : RawMolecule)
    (cycles : List AromaticCycle) :
    (normalizeRawMoleculeP93 mol cycles).parsed.atomCount = mol.atomCount := by
  rw [normalizeRawMoleculeP93_parsed_frozen]
  change (normalize (freezeSourceHydrogenCounts mol)).atomCount = mol.atomCount
  rw [normalize_atomCount, freezeSourceHydrogenCounts_atomCount]

/-- **Expanded atom count of the repaired pipeline.**

The hydrogen-materialized graph consumed by branch ranking has exactly the source atom count plus
the sum of the source hydrogen counts.  No source count is lost and none is invented. -/
theorem normalizeRawMoleculeP93_expanded_atomCount (mol : RawMolecule)
    (cycles : List AromaticCycle) :
    (normalizeRawMoleculeP93 mol cycles).parsed.withExplicitHydrogens.atomCount =
      mol.atomCount + ((List.range mol.atomCount).map mol.hydrogenCountAt).sum := by
  rw [withExplicitHydrogens_atomCount, normalizeRawMoleculeP93_parsed_atomCount]
  have mapEq : (List.range mol.atomCount).map
        (normalizeRawMoleculeP93 mol cycles).parsed.hydrogenCountAt =
      (List.range mol.atomCount).map mol.hydrogenCountAt := by
    apply List.map_congr_left
    intro index member
    exact normalizeRawMoleculeP93_hydrogenCountAt mol cycles index
  rw [mapEq]

/-! ## Concrete P and S sources

The fixtures below are the exact parser images of the written sources (the `_parse` theorems are
kernel computations over `parseOpenSMILES`).  Atom `0` is the oxo center, atom `1` the oxo oxygen,
and atoms `2`--`4` the three remaining single-bonded oxygens. -/

/-- Parser image of `P(=O)(O)(O)O`. -/
def phosphoricAcidSource : RawMolecule where
  atoms :=
    [AtomSpec.aliphatic .P, AtomSpec.aliphatic .O, AtomSpec.aliphatic .O,
     AtomSpec.aliphatic .O, AtomSpec.aliphatic .O]
  bonds :=
    [{ source := 0, target := 1, kind := ParsedBondKind.double },
     { source := 0, target := 2, kind := ParsedBondKind.single },
     { source := 0, target := 3, kind := ParsedBondKind.single },
     { source := 0, target := 4, kind := ParsedBondKind.single }]
  neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]]
  introductionPredecessors := [none, some 0, some 0, some 0, some 0]

/-- Parser image of `S(=O)(O)(O)O`. -/
def sulfuricAcidSource : RawMolecule where
  atoms :=
    [AtomSpec.aliphatic .S, AtomSpec.aliphatic .O, AtomSpec.aliphatic .O,
     AtomSpec.aliphatic .O, AtomSpec.aliphatic .O]
  bonds :=
    [{ source := 0, target := 1, kind := ParsedBondKind.double },
     { source := 0, target := 2, kind := ParsedBondKind.single },
     { source := 0, target := 3, kind := ParsedBondKind.single },
     { source := 0, target := 4, kind := ParsedBondKind.single }]
  neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]]
  introductionPredecessors := [none, some 0, some 0, some 0, some 0]

/-- Bracket control `[S](=O)(O)(O)O`: sulfur carries `some 0`, so no implicit hydrogen is filled. -/
def bracketedSulfurSource : RawMolecule where
  atoms :=
    [{ element := Element.S, explicitHydrogens? := some 0 },
     AtomSpec.aliphatic .O, AtomSpec.aliphatic .O,
     AtomSpec.aliphatic .O, AtomSpec.aliphatic .O]
  bonds :=
    [{ source := 0, target := 1, kind := ParsedBondKind.double },
     { source := 0, target := 2, kind := ParsedBondKind.single },
     { source := 0, target := 3, kind := ParsedBondKind.single },
     { source := 0, target := 4, kind := ParsedBondKind.single }]
  neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]]
  introductionPredecessors := [none, some 0, some 0, some 0, some 0]

/-- Bracket control `[SH](=O)(O)(O)O`: the written count `some 1` is the source datum. -/
def hydrogenBracketedSulfurSource : RawMolecule where
  atoms :=
    [{ element := Element.S, explicitHydrogens? := some 1 },
     AtomSpec.aliphatic .O, AtomSpec.aliphatic .O,
     AtomSpec.aliphatic .O, AtomSpec.aliphatic .O]
  bonds :=
    [{ source := 0, target := 1, kind := ParsedBondKind.double },
     { source := 0, target := 2, kind := ParsedBondKind.single },
     { source := 0, target := 3, kind := ParsedBondKind.single },
     { source := 0, target := 4, kind := ParsedBondKind.single }]
  neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]]
  introductionPredecessors := [none, some 0, some 0, some 0, some 0]

/-- Bracket-oxygen control `P(=O)(O)(O)[O]`: the terminal oxygen is written `some 0`, while the
other two hydroxyl oxygens remain unbracketed. -/
def bracketedOxygenControlSource : RawMolecule where
  atoms :=
    [AtomSpec.aliphatic .P, AtomSpec.aliphatic .O, AtomSpec.aliphatic .O,
     AtomSpec.aliphatic .O, { element := Element.O, explicitHydrogens? := some 0 }]
  bonds :=
    [{ source := 0, target := 1, kind := ParsedBondKind.double },
     { source := 0, target := 2, kind := ParsedBondKind.single },
     { source := 0, target := 3, kind := ParsedBondKind.single },
     { source := 0, target := 4, kind := ParsedBondKind.single }]
  neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]]
  introductionPredecessors := [none, some 0, some 0, some 0, some 0]

/-! ### Parser provenance -/

theorem phosphoricAcidSource_parse :
    parseOpenSMILES "P(=O)(O)(O)O" = .ok phosphoricAcidSource := by
  rfl

theorem sulfuricAcidSource_parse :
    parseOpenSMILES "S(=O)(O)(O)O" = .ok sulfuricAcidSource := by
  rfl

theorem bracketedSulfurSource_parse :
    parseOpenSMILES "[S](=O)(O)(O)O" = .ok bracketedSulfurSource := by
  rfl

theorem hydrogenBracketedSulfurSource_parse :
    parseOpenSMILES "[SH](=O)(O)(O)O" = .ok hydrogenBracketedSulfurSource := by
  rfl

theorem bracketedOxygenControlSource_parse :
    parseOpenSMILES "P(=O)(O)(O)[O]" = .ok bracketedOxygenControlSource := by
  rfl

/-! ### Phosphoric acid `P(=O)(O)(O)O`

The written source has hydrogen vector `[0,0,1,1,1]`: phosphorus uses all five bond orders, the oxo
oxygen has none, and each hydroxyl oxygen has one. -/

theorem phosphoricAcidSource_hydrogenCount_vector :
    (List.range 5).map phosphoricAcidSource.hydrogenCountAt = [0, 0, 1, 1, 1] := by
  decide

/-- The repaired entry point reports exactly the source vector. -/
theorem phosphoricAcid_repaired_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93 phosphoricAcidSource []).parsed.hydrogenCountAt =
      [0, 0, 1, 1, 1] := by
  have mapEq : (List.range 5).map
        (normalizeRawMoleculeP93 phosphoricAcidSource []).parsed.hydrogenCountAt =
      (List.range 5).map phosphoricAcidSource.hydrogenCountAt := by
    apply List.map_congr_left
    intro index member
    exact normalizeRawMoleculeP93_hydrogenCountAt phosphoricAcidSource [] index
  rw [mapEq]
  exact phosphoricAcidSource_hydrogenCount_vector

/-- Five source atoms plus three source hydrogens. -/
theorem phosphoricAcid_repaired_expanded_atomCount :
    (normalizeRawMoleculeP93 phosphoricAcidSource []).parsed.withExplicitHydrogens.atomCount =
      8 := by
  rw [normalizeRawMoleculeP93_expanded_atomCount]
  decide

/-! ### Sulfur oxo source `S(=O)(O)(O)O`

The written source has hydrogen vector `[1,0,1,1,1]`: sulfur fills to its standard valence six
from the five written bond orders. -/

theorem sulfuricAcidSource_hydrogenCount_vector :
    (List.range 5).map sulfuricAcidSource.hydrogenCountAt = [1, 0, 1, 1, 1] := by
  decide

/-- The repaired entry point reports exactly the source vector, including sulfur's hydrogen. -/
theorem sulfuricAcid_repaired_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93 sulfuricAcidSource []).parsed.hydrogenCountAt =
      [1, 0, 1, 1, 1] := by
  have mapEq : (List.range 5).map
        (normalizeRawMoleculeP93 sulfuricAcidSource []).parsed.hydrogenCountAt =
      (List.range 5).map sulfuricAcidSource.hydrogenCountAt := by
    apply List.map_congr_left
    intro index member
    exact normalizeRawMoleculeP93_hydrogenCountAt sulfuricAcidSource [] index
  rw [mapEq]
  exact sulfuricAcidSource_hydrogenCount_vector

/-- Five source atoms plus four source hydrogens. -/
theorem sulfuricAcid_repaired_expanded_atomCount :
    (normalizeRawMoleculeP93 sulfuricAcidSource []).parsed.withExplicitHydrogens.atomCount =
      9 := by
  rw [normalizeRawMoleculeP93_expanded_atomCount]
  decide

/-! ### Bracket controls -/

theorem bracketedSulfurSource_hydrogenCount_vector :
    (List.range 5).map bracketedSulfurSource.hydrogenCountAt = [0, 0, 1, 1, 1] := by
  decide

/-- A written `some 0` at sulfur suppresses the implicit fill and survives the repair. -/
theorem bracketedSulfur_repaired_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93 bracketedSulfurSource []).parsed.hydrogenCountAt =
      [0, 0, 1, 1, 1] := by
  have mapEq : (List.range 5).map
        (normalizeRawMoleculeP93 bracketedSulfurSource []).parsed.hydrogenCountAt =
      (List.range 5).map bracketedSulfurSource.hydrogenCountAt := by
    apply List.map_congr_left
    intro index member
    exact normalizeRawMoleculeP93_hydrogenCountAt bracketedSulfurSource [] index
  rw [mapEq]
  exact bracketedSulfurSource_hydrogenCount_vector

theorem bracketedSulfur_repaired_expanded_atomCount :
    (normalizeRawMoleculeP93 bracketedSulfurSource []).parsed.withExplicitHydrogens.atomCount =
      8 := by
  rw [normalizeRawMoleculeP93_expanded_atomCount]
  decide

theorem hydrogenBracketedSulfurSource_hydrogenCount_vector :
    (List.range 5).map hydrogenBracketedSulfurSource.hydrogenCountAt = [1, 0, 1, 1, 1] := by
  decide

/-- The explicitly written bracket hydrogen is preserved exactly. -/
theorem hydrogenBracketedSulfur_repaired_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93 hydrogenBracketedSulfurSource []).parsed.hydrogenCountAt =
      [1, 0, 1, 1, 1] := by
  have mapEq : (List.range 5).map
        (normalizeRawMoleculeP93 hydrogenBracketedSulfurSource []).parsed.hydrogenCountAt =
      (List.range 5).map hydrogenBracketedSulfurSource.hydrogenCountAt := by
    apply List.map_congr_left
    intro index member
    exact normalizeRawMoleculeP93_hydrogenCountAt hydrogenBracketedSulfurSource [] index
  rw [mapEq]
  exact hydrogenBracketedSulfurSource_hydrogenCount_vector

theorem hydrogenBracketedSulfur_repaired_expanded_atomCount :
    (normalizeRawMoleculeP93 hydrogenBracketedSulfurSource []).parsed.withExplicitHydrogens.atomCount =
      9 := by
  rw [normalizeRawMoleculeP93_expanded_atomCount]
  decide

theorem bracketedOxygenControlSource_hydrogenCount_vector :
    (List.range 5).map bracketedOxygenControlSource.hydrogenCountAt = [0, 0, 1, 1, 0] := by
  decide

/-- A bracket oxygen written `[O]` keeps zero hydrogens even though the two unbracketed hydroxyls
keep one each. -/
theorem bracketedOxygenControl_repaired_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93 bracketedOxygenControlSource []).parsed.hydrogenCountAt =
      [0, 0, 1, 1, 0] := by
  have mapEq : (List.range 5).map
        (normalizeRawMoleculeP93 bracketedOxygenControlSource []).parsed.hydrogenCountAt =
      (List.range 5).map bracketedOxygenControlSource.hydrogenCountAt := by
    apply List.map_congr_left
    intro index member
    exact normalizeRawMoleculeP93_hydrogenCountAt bracketedOxygenControlSource [] index
  rw [mapEq]
  exact bracketedOxygenControlSource_hydrogenCount_vector

theorem bracketedOxygenControl_repaired_expanded_atomCount :
    (normalizeRawMoleculeP93 bracketedOxygenControlSource []).parsed.withExplicitHydrogens.atomCount =
      7 := by
  rw [normalizeRawMoleculeP93_expanded_atomCount]
  decide

/-! ## Diagnostic: the pre-repair pipeline

`normalizeRawMoleculeP93Legacy` is the **old** body under a local name.  It exists only so that the
defect repaired above is recorded as a kernel-checked statement rather than a claim in prose.  It is
not a production entry point and must not be called from authority-facing code. -/

/-- **Diagnostic only.** The pre-repair P-93.2 wrapper: freeze nothing, quotient, then run the
ordinary normalizer. -/
def normalizeRawMoleculeP93Legacy (mol : RawMolecule) (cycles : List AromaticCycle := []) :
    ChemistryNormalizationResult :=
  normalizeRawMolecule (normalize mol) cycles

/-- Diagnostic: on `P(=O)(O)(O)O` the legacy pipeline reports `[1,1,1,1,1]` instead of the written
`[0,0,1,1,1]`.  Lowering the oxo bond raises phosphorus's fill to five and protonates the oxo
oxygen. -/
theorem phosphoricAcid_legacy_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93Legacy phosphoricAcidSource []).parsed.hydrogenCountAt =
      [1, 1, 1, 1, 1] := by
  decide

/-- Diagnostic: the legacy pipeline expands phosphoric acid to ten atoms rather than the eight of
the written source (five atoms plus three hydrogens). -/
theorem phosphoricAcid_legacy_expanded_atomCount :
    (normalizeRawMoleculeP93Legacy phosphoricAcidSource []).parsed.withExplicitHydrogens.atomCount =
      10 := by
  decide

/-- Diagnostic: on `S(=O)(O)(O)O` the legacy pipeline reports `[0,1,1,1,1]` instead of the written
`[1,0,1,1,1]`. -/
theorem sulfuricAcid_legacy_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93Legacy sulfuricAcidSource []).parsed.hydrogenCountAt =
      [0, 1, 1, 1, 1] := by
  decide

/-- Diagnostic: the legacy pipeline moves sulfur's written hydrogen onto the oxo oxygen.  The total
hydrogen count is unchanged, so an atom count alone cannot detect this defect. -/
theorem sulfuricAcid_legacy_moves_source_hydrogen_to_oxo_oxygen :
    sulfuricAcidSource.hydrogenCountAt 0 = 1 ∧
      sulfuricAcidSource.hydrogenCountAt 1 = 0 ∧
      (normalizeRawMoleculeP93Legacy sulfuricAcidSource []).parsed.hydrogenCountAt 0 = 0 ∧
      (normalizeRawMoleculeP93Legacy sulfuricAcidSource []).parsed.hydrogenCountAt 1 = 1 := by
  decide

/-- Diagnostic: the legacy pipeline expands the terminal bracket oxygen of
`P(=O)(O)(O)[O]` from zero to one, while the other bracketed/unbracketed policies are unchanged. -/
theorem bracketedOxygenControl_legacy_hydrogenCount_vector :
    (List.range 5).map
        (normalizeRawMoleculeP93Legacy bracketedOxygenControlSource []).parsed.hydrogenCountAt =
      [1, 1, 1, 1, 0] := by
  decide

/-! ## Kernel-authority certificates -/

assert_kernel_only withExplicitHydrogensStep_atoms_length
assert_kernel_only fold_withExplicitHydrogensStep_atoms_length
assert_kernel_only withExplicitHydrogens_atomCount_fold
assert_kernel_only hydrogenExpansionFold_atomCount_eq
assert_kernel_only withExplicitHydrogens_atomCount
assert_kernel_only normalizeAtom_frozen_explicitHydrogens?_eq
assert_kernel_only normalize_frozen_hydrogenCountAt
assert_kernel_only normalizeRawMoleculeP93_parsed_frozen
assert_kernel_only normalizeRawMoleculeP93_hydrogenCountAt
assert_kernel_only normalizeRawMoleculeP93_parsed_atomCount
assert_kernel_only normalizeRawMoleculeP93_expanded_atomCount
assert_kernel_only phosphoricAcidSource_parse
assert_kernel_only sulfuricAcidSource_parse
assert_kernel_only bracketedSulfurSource_parse
assert_kernel_only hydrogenBracketedSulfurSource_parse
assert_kernel_only bracketedOxygenControlSource_parse
assert_kernel_only phosphoricAcidSource_hydrogenCount_vector
assert_kernel_only phosphoricAcid_repaired_hydrogenCount_vector
assert_kernel_only phosphoricAcid_repaired_expanded_atomCount
assert_kernel_only sulfuricAcidSource_hydrogenCount_vector
assert_kernel_only sulfuricAcid_repaired_hydrogenCount_vector
assert_kernel_only sulfuricAcid_repaired_expanded_atomCount
assert_kernel_only bracketedSulfurSource_hydrogenCount_vector
assert_kernel_only bracketedSulfur_repaired_hydrogenCount_vector
assert_kernel_only bracketedSulfur_repaired_expanded_atomCount
assert_kernel_only hydrogenBracketedSulfurSource_hydrogenCount_vector
assert_kernel_only hydrogenBracketedSulfur_repaired_hydrogenCount_vector
assert_kernel_only hydrogenBracketedSulfur_repaired_expanded_atomCount
assert_kernel_only bracketedOxygenControlSource_hydrogenCount_vector
assert_kernel_only bracketedOxygenControl_repaired_hydrogenCount_vector
assert_kernel_only bracketedOxygenControl_repaired_expanded_atomCount
assert_kernel_only phosphoricAcid_legacy_hydrogenCount_vector
assert_kernel_only phosphoricAcid_legacy_expanded_atomCount
assert_kernel_only sulfuricAcid_legacy_hydrogenCount_vector
assert_kernel_only sulfuricAcid_legacy_moves_source_hydrogen_to_oxo_oxygen
assert_kernel_only bracketedOxygenControl_legacy_hydrogenCount_vector

end P93SourceHydrogenFidelity
end OneCenter
end TetraStereo
