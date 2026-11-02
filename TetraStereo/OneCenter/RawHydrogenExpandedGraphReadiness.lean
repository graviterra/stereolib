import TetraStereo.OneCenter.RawIntakeMaterializationFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Readiness of the hydrogen-expanded raw graph

`LocalizedRawGraphReadiness.RawLocalizedGraphSourceReady` is a transparent gate on a parsed raw
molecule: structural admission, non-aromatic atom spellings, frozen Rule-2 mass data, and localized
covalent bond spellings.  The runtime pipeline does not consume the parsed graph; it consumes
`parsed.withExplicitHydrogens`.

`RawIntakeMaterializationFidelity` transports the gate across `withExplicitHydrogens` only on
`RawMolecule.HydrogenClosed`, i.e. only when materialization inserts no atom.  That is the wrong
domain for the runtime path: the whole point of expansion is to insert the implied hydrogens.

This module proves the gate on the *general* domain, with no `HydrogenClosed` hypothesis:

* `RawMolecule.withExplicitHydrogens_admissible_of_admissible` derives structural admission of the
  expanded graph from the source `Admissible` alone.  The initial expansion accumulator is admitted
  because its bonds are the source bonds and its atoms are the same-length materialized image; the
  existing fold invariant `fold_withExplicitHydrogensStep_preserves_admissible` then transports
  this through the actual fold, and the final written-neighbour canonicalization leaves the graph
  unchanged.  `WrittenNeighborExact` of the *source* is not required.
* `RawMolecule.withExplicitHydrogens_allAtomsNonAromatic` and
  `RawMolecule.withExplicitHydrogens_allBondsLocalizedCovalent` are one-step and fold invariants
  for the accumulator.  The atom invariant is preserved because the only appended atoms are
  ordinary aliphatic hydrogens and materialization preserves the aromatic flag of source atoms.
  The bond invariant is preserved because `spliceHydrogenBondsWithPredecessor` only permutes the
  old bonds together with freshly generated `single` bonds
  (`spliceHydrogenBondsWithPredecessor_perm`), and `single` is localized covalent.
* `RawMolecule.withExplicitHydrogens_preserves_rule2MassesKnown` already exists and is applied
  directly.

The resulting headline theorem
`RawHydrogenExpandedGraphReadiness.rawLocalizedGraphSourceReady_withExplicitHydrogens` therefore
proves

`RawLocalizedGraphSourceReady mol → RawLocalizedGraphSourceReady mol.withExplicitHydrogens`

with no extra hypothesis.  The concise closure endpoint
`admitRawSpatial?_of_raw_withExplicitHydrogens` feeds that gate and the caller's *actual* supplied
spatial configuration (whose length is required to be `mol.withExplicitHydrogens.atomCount`) into
the existing admission theorem, producing a real `LocalizedReference.Input` that carries exactly
the supplied spatial configuration and whose semantic molecule is the conversion of the expanded
graph.  No hydrogen coordinates are invented.

Pointwise structure preservation over the source atom prefix is recorded separately: for every
source index the expanded atom is the materialized source atom and its semantic conversion is
unchanged.
-/

namespace RawMolecule

namespace HydrogenExpansionState

/-- Accumulator-side non-aromaticity invariant.  The final `withExplicitHydrogens` graph inherits
exactly the accumulated atom list. -/
def AllAtomsNonAromatic (state : HydrogenExpansionState) : Prop :=
  ∀ atom, atom ∈ state.1 → atom.aromatic = false

/-- Accumulator-side localized-covalent bond invariant.  The final `withExplicitHydrogens` graph
inherits exactly the accumulated bond list. -/
def AllBondsLocalizedCovalent (state : HydrogenExpansionState) : Prop :=
  ∀ bond, bond ∈ state.2.1 → bond.kind.IsLocalizedCovalent

end HydrogenExpansionState

/-! ## The initial accumulator -/

/-- Mapping the materialized atom specification only consumes the inline hydrogen count; the
aromatic flag is a source fact and survives. -/
theorem initialHydrogenExpansionState_allAtomsNonAromatic (mol : RawMolecule)
    (nonAromatic : ∀ atom, atom ∈ mol.atoms → atom.aromatic = false) :
    (initialHydrogenExpansionState mol).AllAtomsNonAromatic := by
  intro atom member
  rcases List.mem_map.mp (by
    simpa [initialHydrogenExpansionState] using member) with ⟨source, sourceMember, rfl⟩
  simpa using nonAromatic source sourceMember

/-- The initial accumulator keeps the source bond list literally. -/
theorem initialHydrogenExpansionState_allBondsLocalizedCovalent (mol : RawMolecule)
    (localized : ∀ bond, bond ∈ mol.bonds → bond.kind.IsLocalizedCovalent) :
    (initialHydrogenExpansionState mol).AllBondsLocalizedCovalent := by
  change ∀ bond, bond ∈ mol.bonds → bond.kind.IsLocalizedCovalent
  exact localized

/-- **The initial accumulator is structurally admitted.**  Its bonds are the source bonds, and its
atoms are the materialized source atoms, whose length is unchanged.  No written-neighbour
certificate of the source is used. -/
theorem initialHydrogenExpansionState_admissible (mol : RawMolecule)
    (admitted : mol.Admissible) :
    (initialHydrogenExpansionState mol).toRawMolecule.Admissible := by
  refine ⟨?_, ?_⟩
  · intro bond member
    have sourceMember : bond ∈ mol.bonds := by
      simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule] using member
    have endpoints := admitted.1 bond sourceMember
    change bond.source < (mol.atoms.map materializedAtomSpec).length ∧
      bond.target < (mol.atoms.map materializedAtomSpec).length ∧ bond.source ≠ bond.target
    simpa using endpoints
  · simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule,
      BondRecordsUnique] using admitted.2

/-! ## One-step invariants -/

/-- One expansion step preserves non-aromaticity: appended hydrogens are ordinary aliphatic atoms
and old atoms are untouched. -/
theorem withExplicitHydrogensStep_preserves_allAtomsNonAromatic
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (invariant : state.AllAtomsNonAromatic) :
    (withExplicitHydrogensStep mol state idx).AllAtomsNonAromatic := by
  unfold withExplicitHydrogensStep
  by_cases zero : (mol.hydrogenCountAt idx == 0) = true
  · rw [if_pos zero]
    exact invariant
  · rw [if_neg zero]
    intro atom membership
    change atom ∈ state.1 ++
      List.replicate (mol.hydrogenCountAt idx) (AtomSpec.aliphatic Element.H) at membership
    rcases List.mem_append.mp membership with original | added
    · exact invariant atom original
    · have atomIdentity : atom = AtomSpec.aliphatic Element.H :=
        (List.mem_replicate.mp added).2
      subst atom
      rfl

/-- One expansion step preserves localized covalent bond spellings.  The predecessor-aware splice
is a permutation of the old bonds together with the freshly generated hydrogen bonds, and every
fresh hydrogen bond is a `single` bond, which is localized covalent. -/
theorem withExplicitHydrogensStep_preserves_allBondsLocalizedCovalent
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (invariant : state.AllBondsLocalizedCovalent) :
    (withExplicitHydrogensStep mol state idx).AllBondsLocalizedCovalent := by
  simp only [withExplicitHydrogensStep]
  split
  · exact invariant
  · intro bond member
    let count := mol.hydrogenCountAt idx
    let base := state.1.length
    let hydrogenIds := (List.range count).map fun offset => base + offset
    let newBonds := hydrogenIds.map fun target =>
      { source := idx, target := target, kind := ParsedBondKind.single : RawBond }
    have permuted :
        (spliceHydrogenBondsWithPredecessor (mol.introductionPredecessors[idx]?)
          state.2.1 idx newBonds).Perm (state.2.1 ++ newBonds) :=
      spliceHydrogenBondsWithPredecessor_perm _ _ _ _
    have appended : bond ∈ state.2.1 ++ newBonds := permuted.mem_iff.mp member
    rcases List.mem_append.mp appended with old | fresh
    · exact invariant bond old
    · rcases List.mem_map.mp fresh with ⟨hydrogen, _hydrogenMember, rfl⟩
      exact ⟨1, rfl⟩

/-! ## Fold invariants -/

theorem fold_withExplicitHydrogensStep_preserves_allAtomsNonAromatic
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (invariant : state.AllAtomsNonAromatic) :
    (indices.foldl (withExplicitHydrogensStep mol) state).AllAtomsNonAromatic := by
  induction indices generalizing state with
  | nil => exact invariant
  | cons idx rest inductionHypothesis =>
      exact inductionHypothesis (withExplicitHydrogensStep mol state idx)
        (withExplicitHydrogensStep_preserves_allAtomsNonAromatic mol state idx invariant)

theorem fold_withExplicitHydrogensStep_preserves_allBondsLocalizedCovalent
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (invariant : state.AllBondsLocalizedCovalent) :
    (indices.foldl (withExplicitHydrogensStep mol) state).AllBondsLocalizedCovalent := by
  induction indices generalizing state with
  | nil => exact invariant
  | cons idx rest inductionHypothesis =>
      exact inductionHypothesis (withExplicitHydrogensStep mol state idx)
        (withExplicitHydrogensStep_preserves_allBondsLocalizedCovalent mol state idx invariant)

/-! ## Transport to the expanded graph -/

/-- **Structural admission of the expanded graph from source admission alone.**  This is the
`Admissible` component of the main transport theorem and deliberately does not require
`WrittenNeighborExact` on the source or `HydrogenClosed` on the expansion domain. -/
theorem withExplicitHydrogens_admissible_of_admissible (mol : RawMolecule)
    (admitted : mol.Admissible) :
    mol.withExplicitHydrogens.Admissible := by
  unfold withExplicitHydrogens
  apply (withExactWrittenNeighbors_admissible_iff _).mpr
  exact fold_withExplicitHydrogensStep_preserves_admissible mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (by intro idx member; exact List.mem_range.mp member)
    (initialHydrogenExpansionState_shapeInvariant mol)
    (initialHydrogenExpansionState_admissible mol admitted)

/-- Every atom of the expanded graph is non-aromatic whenever every source atom is. -/
theorem withExplicitHydrogens_allAtomsNonAromatic (mol : RawMolecule)
    (nonAromatic : ∀ atom, atom ∈ mol.atoms → atom.aromatic = false) :
    ∀ atom, atom ∈ mol.withExplicitHydrogens.atoms → atom.aromatic = false := by
  intro atom member
  rw [withExplicitHydrogens_atoms_eq_fold] at member
  exact fold_withExplicitHydrogensStep_preserves_allAtomsNonAromatic mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (initialHydrogenExpansionState_allAtomsNonAromatic mol nonAromatic) atom member

/-- Every bond of the expanded graph is localized covalent whenever every source bond is.  Double
and triple bonds remain permitted: their source spellings already carry a positive localized
order. -/
theorem withExplicitHydrogens_allBondsLocalizedCovalent (mol : RawMolecule)
    (localized : ∀ bond, bond ∈ mol.bonds → bond.kind.IsLocalizedCovalent) :
    ∀ bond, bond ∈ mol.withExplicitHydrogens.bonds → bond.kind.IsLocalizedCovalent := by
  intro bond member
  rw [withExplicitHydrogens_bonds_eq_fold] at member
  exact fold_withExplicitHydrogensStep_preserves_allBondsLocalizedCovalent mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (initialHydrogenExpansionState_allBondsLocalizedCovalent mol localized) bond member

/-! ## Pointwise preservation over the source atom prefix -/

/-- Lookup of the expanded graph is lookup of the expansion fold result: the final
written-neighbour canonicalization never touches atoms. -/
theorem withExplicitHydrogens_atomAt?_eq_fold (mol : RawMolecule) (index : ℕ) :
    mol.withExplicitHydrogens.atomAt? index =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomAt? index := rfl

/-- One step leaves every already-present atom index untouched: fresh hydrogen atoms are appended
at the end of the accumulator. -/
theorem withExplicitHydrogensStep_atomAt?_of_lt
    (mol : RawMolecule) (state : HydrogenExpansionState) (index idx : ℕ)
    (bound : index < state.1.length) :
    (withExplicitHydrogensStep mol state idx).toRawMolecule.atomAt? index =
      state.toRawMolecule.atomAt? index := by
  unfold withExplicitHydrogensStep
  by_cases zero : (mol.hydrogenCountAt idx == 0) = true
  · rw [if_pos zero]
  · rw [if_neg zero]
    change listGet?
        (state.1 ++ List.replicate (mol.hydrogenCountAt idx) (AtomSpec.aliphatic Element.H))
        index =
      listGet? state.1 index
    exact listGet?_append_left_of_lt state.1 _ index bound

theorem fold_withExplicitHydrogensStep_atomAt?_of_lt
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (index : ℕ) (bound : index < state.1.length) :
    (indices.foldl (withExplicitHydrogensStep mol) state).toRawMolecule.atomAt? index =
      state.toRawMolecule.atomAt? index := by
  induction indices generalizing state with
  | nil => rfl
  | cons idx rest inductionHypothesis =>
      rw [List.foldl_cons]
      have nextBound : index < (withExplicitHydrogensStep mol state idx).1.length := by
        simp only [withExplicitHydrogensStep]
        split
        · exact bound
        · simp only [List.length_append, List.length_replicate]
          omega
      exact (inductionHypothesis (withExplicitHydrogensStep mol state idx) nextBound).trans
        (withExplicitHydrogensStep_atomAt?_of_lt mol state index idx bound)

/-- At every source atom index, the expanded atom is exactly the materialized source atom. -/
theorem withExplicitHydrogens_atomAt?_of_lt (mol : RawMolecule) (index : ℕ) (spec : AtomSpec)
    (source : mol.atomAt? index = some spec) :
    mol.withExplicitHydrogens.atomAt? index = some (materializedAtomSpec spec) := by
  have bound : index < mol.atomCount :=
    listGet?_eq_some_implies_lt mol.atoms index spec (by simpa [atomAt?] using source)
  have sourceLookup : listGet? mol.atoms index = some spec := by
    simpa [atomAt?] using source
  have initialLookup :
      (initialHydrogenExpansionState mol).toRawMolecule.atomAt? index =
        some (materializedAtomSpec spec) := by
    unfold initialHydrogenExpansionState HydrogenExpansionState.toRawMolecule atomAt?
    rw [listGet?_map, sourceLookup]
    rfl
  have initialBound : index < (initialHydrogenExpansionState mol).1.length := by
    simpa [initialHydrogenExpansionState] using bound
  have folded := fold_withExplicitHydrogensStep_atomAt?_of_lt mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol) index initialBound
  have resultLookup :
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomAt? index =
        some (materializedAtomSpec spec) := by
    rw [folded]
    exact initialLookup
  rw [withExplicitHydrogens_atomAt?_eq_fold]
  exact resultLookup

/-- On the source atom prefix, expanding hydrogens does not change the checked semantic
conversion: materialization only consumes the inline count, which the conversion never reads. -/
theorem withExplicitHydrogens_atomAt?_bind_toSemanticAtom?_of_lt
    (mol : RawMolecule) (index : ℕ) (bound : index < mol.atomCount) :
    (mol.withExplicitHydrogens.atomAt? index).bind AtomSpec.toSemanticAtom? =
      (mol.atomAt? index).bind AtomSpec.toSemanticAtom? := by
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt mol.atoms index bound
  have source : mol.atomAt? index = some spec := by simpa [atomAt?] using lookup
  rw [withExplicitHydrogens_atomAt?_of_lt mol index spec source, source]
  simp [AtomSpec.toSemanticAtom?_materializedAtomSpec]

end RawMolecule

/-! ## The headline transport and the admission endpoint -/

namespace RawHydrogenExpandedGraphReadiness

open LocalizedRawGraphReadiness

/-- **The raw readiness gate transports to the hydrogen-expanded graph on every raw molecule.**

There is no `HydrogenClosed` hypothesis and no written-neighbour certificate of the input: the
expansion may insert arbitrarily many hydrogen atoms and bonds, and the expanded graph still
satisfies exactly the same four raw conditions. -/
theorem rawLocalizedGraphSourceReady_withExplicitHydrogens
    (molecule : RawMolecule) (rawReady : RawLocalizedGraphSourceReady molecule) :
    RawLocalizedGraphSourceReady molecule.withExplicitHydrogens := by
  unfold RawLocalizedGraphSourceReady at rawReady ⊢
  exact ⟨molecule.withExplicitHydrogens_admissible_of_admissible rawReady.1,
    molecule.withExplicitHydrogens_allAtomsNonAromatic rawReady.2.1,
    molecule.withExplicitHydrogens_preserves_rule2MassesKnown rawReady.2.2.1,
    molecule.withExplicitHydrogens_allBondsLocalizedCovalent rawReady.2.2.2⟩

/-- **Admission of the actual expanded runtime object for the actual supplied coordinates.**

Given raw readiness of the parsed graph and a spatial configuration with one position per atom of
the *expanded* graph (`spatial.positions.length = molecule.withExplicitHydrogens.atomCount`),
`LocalizedReference.admitRawSpatial?` succeeds on `molecule.withExplicitHydrogens` and returns an
input whose semantic molecule is exactly the conversion of that expanded graph, whose molecule
agreement is the expanded graph, and whose spatial configuration is exactly the supplied `spatial`.
No hydrogen positions are invented: the caller's own configuration is consumed unchanged.

The semantic inventory is preserved exactly: at every index the semantic atom is the checked
conversion of the expanded atom lookup, and the semantic atom count is the expanded atom count. -/
theorem admitRawSpatial?_of_raw_withExplicitHydrogens
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule)
    (spatialLength : spatial.positions.length = molecule.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.withExplicitHydrogens.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? molecule.withExplicitHydrogens spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.withExplicitHydrogens.AuthoritativeStructureAgreement
              input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                (∀ index, listGet? semantic.atoms index =
                  (molecule.withExplicitHydrogens.atomAt? index).bind
                    AtomSpec.toSemanticAtom?) ∧
                  semantic.atomCount = molecule.withExplicitHydrogens.atomCount := by
  obtain ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq⟩ :=
    admitRawSpatial?_of_raw molecule.withExplicitHydrogens spatial
      (rawLocalizedGraphSourceReady_withExplicitHydrogens molecule rawReady) spatialLength
  refine ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, ?_, ?_⟩
  · intro index
    exact RawMolecule.toSemanticMolecule?_atomAt?
      molecule.withExplicitHydrogens semantic converted index
  · exact RawMolecule.toSemanticMolecule?_atomCount
      molecule.withExplicitHydrogens semantic converted

/-- Source-prefix form of the same admission: the semantic atom at a source index is the checked
conversion of the *source* atom, even though the admitted graph is the expanded one.  This records
that expansion adds hydrogens without disturbing the source atomic inventory. -/
theorem admitRawSpatial?_of_raw_withExplicitHydrogens_sourcePrefix
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule)
    (spatialLength : spatial.positions.length = molecule.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      LocalizedReference.admitRawSpatial? molecule.withExplicitHydrogens spatial = some input ∧
        input.certified.certified.input.molecule = semantic ∧
          input.certified.certified.input.spatial? = some spatial ∧
            (∀ index, index < molecule.atomCount →
              listGet? semantic.atoms index =
                (molecule.atomAt? index).bind AtomSpec.toSemanticAtom?) := by
  obtain ⟨semantic, input, _converted, accepted, moleculeEq, _agreement, spatialEq, inventory,
    _count⟩ :=
    admitRawSpatial?_of_raw_withExplicitHydrogens molecule spatial rawReady spatialLength
  refine ⟨semantic, input, accepted, moleculeEq, spatialEq, ?_⟩
  intro index bound
  rw [inventory index, RawMolecule.withExplicitHydrogens_atomAt?_bind_toSemanticAtom?_of_lt
    molecule index bound]

end RawHydrogenExpandedGraphReadiness

end TetraStereo.OneCenter

/-! ## Kernel-authority certificates -/

assert_kernel_only TetraStereo.OneCenter.RawMolecule.initialHydrogenExpansionState_allAtomsNonAromatic
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.initialHydrogenExpansionState_allBondsLocalizedCovalent
assert_kernel_only TetraStereo.OneCenter.RawMolecule.initialHydrogenExpansionState_admissible
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogensStep_preserves_allAtomsNonAromatic
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogensStep_preserves_allBondsLocalizedCovalent
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.fold_withExplicitHydrogensStep_preserves_allAtomsNonAromatic
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.fold_withExplicitHydrogensStep_preserves_allBondsLocalizedCovalent
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_admissible_of_admissible
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_allAtomsNonAromatic
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_allBondsLocalizedCovalent
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_atomAt?_eq_fold
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogensStep_atomAt?_of_lt
assert_kernel_only TetraStereo.OneCenter.RawMolecule.fold_withExplicitHydrogensStep_atomAt?_of_lt
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_atomAt?_of_lt
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_atomAt?_bind_toSemanticAtom?_of_lt
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpandedGraphReadiness.rawLocalizedGraphSourceReady_withExplicitHydrogens
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpandedGraphReadiness.admitRawSpatial?_of_raw_withExplicitHydrogens
assert_kernel_only
  TetraStereo.OneCenter.RawHydrogenExpandedGraphReadiness.admitRawSpatial?_of_raw_withExplicitHydrogens_sourcePrefix
