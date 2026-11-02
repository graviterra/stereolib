import TetraStereo.OneCenter.RawHydrogenExpansionClosure
import TetraStereo.OneCenter.RawHydrogenExpandedGraphReadiness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter

/-!
# Construction of the expanded raw intake from the source gate alone

`RawIntakeMaterializationFidelity` bridges raw readiness to the hydrogen-expanded graph only on
`RawMolecule.HydrogenClosed`, i.e. only when `withExplicitHydrogens` inserts no atom.  The runtime
SMILES path supplies `parsed.withExplicitHydrogens` precisely because atoms are inserted.  The
`HydrogenClosed` premise was therefore an external-domain assumption that the runtime cannot
discharge.

The two successor modules remove the two independent obstacles:

* `RawHydrogenExpansionClosure.hydrogenClosed_withExplicitHydrogens` proves
  `mol.withExplicitHydrogens.HydrogenClosed` for every raw molecule, with no admissibility or
  valence hypothesis;
* `RawHydrogenExpandedGraphReadiness.rawLocalizedGraphSourceReady_withExplicitHydrogens` proves the
  four-component source gate on the expanded graph from the source gate alone.

This module composes those results with the existing actual admission theorem.  Everything below is
stated for an arbitrary finite parsed molecule; the only external hypotheses are the actual source
gate `RawLocalizedGraphSourceReady molecule` and the caller's actual spatial length
`spatial.positions.length = molecule.withExplicitHydrogens.atomCount`.  In particular there is

* no `HydrogenClosed` premise on the input or on the output,
* no supplied semantic conversion (`toSemanticMolecule? = some semantic`),
* no supplied admission/certification success,
* no supplied readiness proof of the expanded graph,
* no constructed or invented hydrogen coordinates.

The construction records the actual output of the production definitions:

* structural admission: `WellFormed` of the source and of the expanded graph;
* closure of the expanded graph (`HydrogenClosed`, with its executable reflection);
* the exact generated-hydrogen count
  `atomCount + Σ hydrogenCountAt` and the per-index fresh atoms
  `AtomSpec.aliphatic Element.H`;
* bond semantics: every expanded bond is either literally a source bond or a generated
  `single` bond from a source atom to a fresh hydrogen index;
* atom inventory: the semantic atom at every source index is exactly the checked conversion of the
  corresponding source atom;
* the certified finite graph: the admitted `CertifiedLocalizedCIPInput`'s vertex type has exactly
  the expanded atom count, and its graph atomic number / Rule-2 mass fields are the semantic atoms'
  source-backed data.

The normalized runtime object is handled separately: `RawNormalizationSourceReady` is the exact
transparent gate under which `normalizeUnspecifiedBonds` lands in the source gate, and the admission
corollaries run the actual runtime pipeline `normalizeUnspecifiedBonds.withExplicitHydrogens`.
-/

namespace RawExpandedIntakeConstruction

open LocalizedRawGraphReadiness
open RawMolecule

/-! ## Well-formedness derived from the source gate -/

/-- The structural half of the source gate is exactly `WellFormed`. -/
theorem wellFormed_of_rawReady (molecule : RawMolecule)
    (rawReady : RawLocalizedGraphSourceReady molecule) :
    molecule.WellFormed :=
  rawReady.1.1

/-- **The expanded graph is well-formed whenever the source gate holds.**  This is derived from the
readiness transport, not assumed. -/
theorem wellFormed_withExplicitHydrogens_of_rawReady (molecule : RawMolecule)
    (rawReady : RawLocalizedGraphSourceReady molecule) :
    molecule.withExplicitHydrogens.WellFormed :=
  (RawHydrogenExpandedGraphReadiness.rawLocalizedGraphSourceReady_withExplicitHydrogens
    molecule rawReady).1.1

/-- The expanded graph is structurally admitted whenever the source gate holds. -/
theorem admissible_withExplicitHydrogens_of_rawReady (molecule : RawMolecule)
    (rawReady : RawLocalizedGraphSourceReady molecule) :
    molecule.withExplicitHydrogens.Admissible :=
  (RawHydrogenExpandedGraphReadiness.rawLocalizedGraphSourceReady_withExplicitHydrogens
    molecule rawReady).1

/-! ## Closure and readiness of the actual expanded graph -/




theorem expandedHydrogenClosed (molecule : RawMolecule) :
    molecule.withExplicitHydrogens.HydrogenClosed :=
  RawHydrogenExpansionClosure.hydrogenClosed_withExplicitHydrogens molecule

/-- Executable reflection of expanded closure. -/
theorem expandedHydrogenClosedCheck (molecule : RawMolecule) :
    molecule.withExplicitHydrogens.hydrogenClosed? = true :=
  RawHydrogenExpansionClosure.hydrogenClosed?_withExplicitHydrogens molecule

/-- **The actual expanded graph satisfies the source gate whenever the source does.**  No
`HydrogenClosed` premise is used. -/
theorem expandedSourceReady_of_rawReady (molecule : RawMolecule)
    (rawReady : RawLocalizedGraphSourceReady molecule) :
    RawLocalizedGraphSourceReady molecule.withExplicitHydrogens :=
  RawHydrogenExpandedGraphReadiness.rawLocalizedGraphSourceReady_withExplicitHydrogens
    molecule rawReady

/-- The expanded source gate is executable at the call site. -/
theorem expandedSourceReadyCheck_of_rawReadyCheck (molecule : RawMolecule)
    (checked : rawLocalizedGraphSourceReady? molecule = true) :
    rawLocalizedGraphSourceReady? molecule.withExplicitHydrogens = true :=
  (rawLocalizedGraphSourceReady?_eq_true_iff molecule.withExplicitHydrogens).mpr
    (expandedSourceReady_of_rawReady molecule
      ((rawLocalizedGraphSourceReady?_eq_true_iff molecule).mp checked))

/-! ## Generated hydrogen count -/

/-- One expansion step increases the atom count by exactly the target's hydrogen count. -/
theorem expansionStep_atomCount (molecule : RawMolecule)
    (state : HydrogenExpansionState) (index : ℕ) :
    (withExplicitHydrogensStep molecule state index).toRawMolecule.atomCount =
      state.toRawMolecule.atomCount + molecule.hydrogenCountAt index :=
  RawHydrogenExpansionClosure.withExplicitHydrogensStep_atomCount molecule state index

/-- A full expansion fold appends the sum of the visited hydrogen counts. -/
theorem fold_atomCount_eq (molecule : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState) :
    (indices.foldl (withExplicitHydrogensStep molecule) state).toRawMolecule.atomCount =
      state.toRawMolecule.atomCount + (indices.map molecule.hydrogenCountAt).sum := by
  induction indices generalizing state with
  | nil => simp
  | cons index rest inductionHypothesis =>
      rw [List.foldl_cons,
        inductionHypothesis (withExplicitHydrogensStep molecule state index),
        expansionStep_atomCount]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **Generated hydrogen count of the actual expansion.**  The expanded atom count is the source
atom count plus exactly the source hydrogen counts summed over the source indices.  No atom other
than the parsed atoms and the implied hydrogens is introduced. -/
theorem withExplicitHydrogens_atomCount_eq_sum (molecule : RawMolecule) :
    molecule.withExplicitHydrogens.atomCount =
      molecule.atomCount +
        ((List.range molecule.atomCount).map molecule.hydrogenCountAt).sum := by
  change molecule.withExplicitHydrogens.atoms.length =
    molecule.atomCount +
      ((List.range molecule.atomCount).map molecule.hydrogenCountAt).sum
  rw [RawMolecule.withExplicitHydrogens_atoms_eq_fold]
  simpa [RawMolecule.atomCount, initialHydrogenExpansionState,
    HydrogenExpansionState.toRawMolecule] using
    fold_atomCount_eq molecule (List.range molecule.atomCount)
      (initialHydrogenExpansionState molecule)

/-- The number of generated hydrogens is exactly the source hydrogen-count sum. -/
theorem withExplicitHydrogens_generated_count (molecule : RawMolecule) :
    molecule.withExplicitHydrogens.atomCount - molecule.atomCount =
      ((List.range molecule.atomCount).map molecule.hydrogenCountAt).sum := by
  rw [withExplicitHydrogens_atomCount_eq_sum]
  omega

/-- Every atom of the expanded graph at a fresh index is an ordinary aliphatic hydrogen. -/
theorem atomAt?_eq_hydrogen_of_atomCount_le (molecule : RawMolecule) (index : ℕ)
    (lower : molecule.atomCount ≤ index)
    (upper : index < molecule.withExplicitHydrogens.atomCount) :
    molecule.withExplicitHydrogens.atomAt? index =
      some (AtomSpec.aliphatic Element.H) := by
  have foldUpper : index <
      ((List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
        (initialHydrogenExpansionState molecule)).toRawMolecule.atomCount := by
    have observed : index < molecule.withExplicitHydrogens.atoms.length := by
      simpa [RawMolecule.atomCount] using upper
    rw [RawMolecule.withExplicitHydrogens_atoms_eq_fold] at observed
    simpa [RawMolecule.atomCount] using observed
  obtain ⟨atom, atomLookup⟩ :=
    listGet?_exists_of_lt
      (((List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
        (initialHydrogenExpansionState molecule)).toRawMolecule.atoms) index
      (by simpa [RawMolecule.atomCount] using foldUpper)
  have resultLookup :
      ((List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
        (initialHydrogenExpansionState molecule)).toRawMolecule.atomAt? index = some atom := by
    simpa [RawMolecule.atomAt?] using atomLookup
  have atomIsHydrogen : atom = AtomSpec.aliphatic Element.H :=
    RawHydrogenExpansionClosure.fold_atomAt?_eq_hydrogen_of_le molecule
      (List.range molecule.atomCount) (initialHydrogenExpansionState molecule) index atom
      (by
        simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule,
          RawMolecule.atomCount] using lower)
      resultLookup
  have expandedLookup : molecule.withExplicitHydrogens.atomAt? index = some atom := by
    simp only [RawMolecule.atomAt?]
    rw [RawMolecule.withExplicitHydrogens_atoms_eq_fold]
    exact resultLookup
  rw [atomIsHydrogen] at expandedLookup
  exact expandedLookup

/-- Source atoms are materialized pointwise: the source atom's inline count is consumed, and the
element, isotope, charge, aromatic flag, and tetrahedral input are unchanged. -/
theorem atomAt?_source_prefix (molecule : RawMolecule) (index : ℕ) (spec : AtomSpec)
    (source : molecule.atomAt? index = some spec) :
    molecule.withExplicitHydrogens.atomAt? index = some (materializedAtomSpec spec) := by
  have bound : index < molecule.atomCount :=
    listGet?_eq_some_implies_lt molecule.atoms index spec (by simpa [RawMolecule.atomAt?] using source)
  simpa [source] using
    (RawHydrogenExpansionClosure.withExplicitHydrogens_atomAt?_of_lt molecule index bound)

/-! ## Bond semantics of the actual expansion -/

/-- A raw bond is a generated hydrogen bond when it is an ordinary single bond from a real source
atom to a fresh atom index.  This is the exact shape emitted by `withExplicitHydrogensStep`. -/
def IsGeneratedHydrogenBond (molecule : RawMolecule) (bond : RawBond) : Prop :=
  bond.kind = ParsedBondKind.single ∧
    bond.source < molecule.atomCount ∧
      molecule.atomCount ≤ bond.target

/-- Generated bonds survive any suffix of the expansion fold. -/
theorem fold_generated_bond_mem (molecule : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState) (bond : RawBond)
    (member : bond ∈ state.toRawMolecule.bonds) :
    bond ∈ (indices.foldl (withExplicitHydrogensStep molecule) state).toRawMolecule.bonds :=
  RawHydrogenExpansionClosure.fold_withExplicitHydrogensStep_bonds_mem
    molecule indices state bond member

/-- A state-level bond-semantics invariant: every bond currently present is a source bond or a
generated hydrogen bond. -/
theorem fold_bond_semantics (molecule : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (indicesBound : ∀ index, index ∈ indices → index < molecule.atomCount)
    (invariant : ∀ bond, bond ∈ state.toRawMolecule.bonds →
      bond ∈ molecule.bonds ∨ IsGeneratedHydrogenBond molecule bond) :
    ∀ bond, bond ∈ (indices.foldl (withExplicitHydrogensStep molecule) state).toRawMolecule.bonds →
      bond ∈ molecule.bonds ∨ IsGeneratedHydrogenBond molecule bond := by
  induction indices generalizing state with
  | nil => exact invariant
  | cons index rest inductionHypothesis =>
      apply inductionHypothesis (withExplicitHydrogensStep molecule state index)
        (withExplicitHydrogensStep_preserves_shapeInvariant molecule state index shape)
        (fun item member => indicesBound item (by simp [member]))
      intro bond member
      have indexBound : index < molecule.atomCount := indicesBound index (by simp)
      simp only [withExplicitHydrogensStep] at member
      split at member
      · exact invariant bond (by simpa [HydrogenExpansionState.toRawMolecule] using member)
      · dsimp only [HydrogenExpansionState.toRawMolecule] at member
        let count := molecule.hydrogenCountAt index
        let base := state.1.length
        let hydrogenIds := (List.range count).map fun offset => base + offset
        let newBonds := hydrogenIds.map fun target =>
          { source := index, target := target, kind := ParsedBondKind.single : RawBond }
        have permuted :
            (spliceHydrogenBondsWithPredecessor (molecule.introductionPredecessors[index]?)
              state.2.1 index newBonds).Perm (state.2.1 ++ newBonds) :=
          spliceHydrogenBondsWithPredecessor_perm _ _ _ _
        have appended : bond ∈ state.2.1 ++ newBonds := permuted.mem_iff.mp member
        rcases List.mem_append.mp appended with old | fresh
        · exact invariant bond (by simpa [HydrogenExpansionState.toRawMolecule] using old)
        · rcases List.mem_map.mp fresh with ⟨target, targetMember, bondEq⟩
          rw [← bondEq]
          refine Or.inr ⟨rfl, indexBound, ?_⟩
          rcases List.mem_map.mp targetMember with ⟨offset, _offsetMember, targetEq⟩
          rw [← targetEq]
          exact Nat.le_add_right_of_le shape.originalAtoms

/-- **Bond semantics of the expanded graph.**  Every bond of the actual expansion is either
literally one of the source bonds or a generated single bond from a source atom to a fresh
hydrogen index.  No other bond is introduced. -/
theorem bond_semantics (molecule : RawMolecule) {bond : RawBond}
    (member : bond ∈ molecule.withExplicitHydrogens.bonds) :
    bond ∈ molecule.bonds ∨ IsGeneratedHydrogenBond molecule bond := by
  rw [RawMolecule.withExplicitHydrogens_bonds_eq_fold] at member
  exact fold_bond_semantics molecule (List.range molecule.atomCount)
    (initialHydrogenExpansionState molecule)
    (initialHydrogenExpansionState_shapeInvariant molecule)
    (fun index indexMember => List.mem_range.mp indexMember)
    (fun sourceBond sourceMember => Or.inl (by
      simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule] using sourceMember))
    bond member

/-- Under the source gate the generated target is also a real expanded atom index. -/
theorem bond_semantics_of_rawReady (molecule : RawMolecule)
    (rawReady : RawLocalizedGraphSourceReady molecule) {bond : RawBond}
    (member : bond ∈ molecule.withExplicitHydrogens.bonds) :
    bond ∈ molecule.bonds ∨
      (bond.kind = ParsedBondKind.single ∧
        bond.source < molecule.atomCount ∧
          molecule.atomCount ≤ bond.target ∧
            bond.target < molecule.withExplicitHydrogens.atomCount) := by
  rcases bond_semantics molecule member with source | generated
  · exact Or.inl source
  · rcases generated with ⟨kindEq, sourceBound, targetLower⟩
    have endpoints :=
      (admissible_withExplicitHydrogens_of_rawReady molecule rawReady).1 bond member
    exact Or.inr ⟨kindEq, sourceBound, targetLower, by simpa using endpoints.2.1⟩

/-- **Every fresh expanded atom is the target of a generated single bond from a source atom.**
This is the forward bond inventory matching the fresh-atom inventory above. -/
theorem fold_fresh_atom_has_generated_bond (molecule : RawMolecule) (indices : List ℕ)
    (state : HydrogenExpansionState)
    (shape : state.ShapeInvariant molecule)
    (indicesBound : ∀ index, index ∈ indices → index < molecule.atomCount) :
    ∀ atomIndex, state.toRawMolecule.atomCount ≤ atomIndex →
      atomIndex <
        (indices.foldl (withExplicitHydrogensStep molecule) state).toRawMolecule.atomCount →
      ∃ sourceIndex, sourceIndex ∈ indices ∧ sourceIndex < molecule.atomCount ∧
        ({ source := sourceIndex, target := atomIndex,
            kind := ParsedBondKind.single } : RawBond) ∈
          (indices.foldl (withExplicitHydrogensStep molecule) state).toRawMolecule.bonds := by
  induction indices generalizing state with
  | nil =>
      intro atomIndex lower upper
      simp only [List.foldl_nil] at upper
      exfalso
      omega
  | cons index rest inductionHypothesis =>
      intro atomIndex lower upper
      by_cases within :
          atomIndex <
            (withExplicitHydrogensStep molecule state index).toRawMolecule.atomCount
      · let base := state.1.length
        let count := molecule.hydrogenCountAt index
        have lowerBase : base ≤ atomIndex := by
          simpa [base, RawMolecule.atomCount, HydrogenExpansionState.toRawMolecule] using lower
        have stepCount :
            (withExplicitHydrogensStep molecule state index).toRawMolecule.atomCount =
              base + count := by
          rw [expansionStep_atomCount]
          simp [base, count, RawMolecule.atomCount, HydrogenExpansionState.toRawMolecule]
        have offsetBound : atomIndex - base < count := by omega
        let bond : RawBond :=
          { source := index, target := base + (atomIndex - base),
            kind := ParsedBondKind.single }
        have targetEq : bond.target = atomIndex := by
          dsimp only [bond]
          omega
        have bondEq :
            ({ source := index, target := atomIndex,
                kind := ParsedBondKind.single } : RawBond) = bond := by
          dsimp only [bond]
          rw [show state.1.length + (atomIndex - state.1.length) = atomIndex by omega]
        have bondMemStep :
            bond ∈ (withExplicitHydrogensStep molecule state index).toRawMolecule.bonds := by
          dsimp only [bond, base, count]
          exact RawHydrogenExpansionClosure.withExplicitHydrogensStep_new_bond_mem
            molecule state index (atomIndex - state.1.length) offsetBound
        have bondMemFinal :
            bond ∈ (rest.foldl (withExplicitHydrogensStep molecule)
              (withExplicitHydrogensStep molecule state index)).toRawMolecule.bonds :=
          fold_generated_bond_mem molecule rest
            (withExplicitHydrogensStep molecule state index) bond bondMemStep
        refine ⟨index, by simp, indicesBound index (by simp), ?_⟩
        rw [bondEq]
        simpa only [List.foldl_cons] using bondMemFinal
      · obtain ⟨sourceIndex, sourceMember, sourceBound, bondMember⟩ :=
          inductionHypothesis (withExplicitHydrogensStep molecule state index)
            (withExplicitHydrogensStep_preserves_shapeInvariant molecule state index shape)
            (fun item member => indicesBound item (by simp [member]))
            atomIndex (Nat.le_of_not_gt within)
            (by simpa only [List.foldl_cons] using upper)
        exact ⟨sourceIndex, by simp [sourceMember], sourceBound,
          by simpa only [List.foldl_cons] using bondMember⟩

/-- Existence form for a concrete fresh index of the actual expanded graph. -/
theorem fresh_atom_has_generated_single_bond (molecule : RawMolecule) (index : ℕ)
    (lower : molecule.atomCount ≤ index)
    (upper : index < molecule.withExplicitHydrogens.atomCount) :
    ∃ sourceIndex, sourceIndex < molecule.atomCount ∧
      ({ source := sourceIndex, target := index,
          kind := ParsedBondKind.single } : RawBond) ∈
        molecule.withExplicitHydrogens.bonds := by
  have foldUpper : index <
      ((List.range molecule.atomCount).foldl (withExplicitHydrogensStep molecule)
        (initialHydrogenExpansionState molecule)).toRawMolecule.atomCount := by
    have observed : index < molecule.withExplicitHydrogens.atoms.length := by
      simpa [RawMolecule.atomCount] using upper
    rw [RawMolecule.withExplicitHydrogens_atoms_eq_fold] at observed
    simpa [RawMolecule.atomCount] using observed
  obtain ⟨sourceIndex, _rangeMember, sourceBound, bondMember⟩ :=
    fold_fresh_atom_has_generated_bond molecule (List.range molecule.atomCount)
      (initialHydrogenExpansionState molecule)
      (initialHydrogenExpansionState_shapeInvariant molecule)
      (fun item member => List.mem_range.mp member)
      index
      (by
        simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule,
          RawMolecule.atomCount] using lower)
      foldUpper
  refine ⟨sourceIndex, sourceBound, ?_⟩
  rw [RawMolecule.withExplicitHydrogens_bonds_eq_fold]
  exact bondMember

/-! ## The actual expanded admission construction -/

/-- **Full expanded raw intake fidelity from the source gate alone.**

For an arbitrary finite parsed molecule that passes the explicit source gate
`RawLocalizedGraphSourceReady` and an actual spatial configuration with one coordinate per atom of
the *expanded* graph, the executable `LocalizedReference.admitRawSpatial?` accepts the actual
runtime object `molecule.withExplicitHydrogens`.

The returned input carries exactly the supplied coordinates, its semantic molecule is exactly the
checked conversion of the expanded graph, and the semantic inventory agrees indexwise with the
expanded atom lookups.  The source atom prefix is the checked conversion of the source atoms.  The
expanded graph itself is closed, well-formed, and lies in the localized CIP graph domain.  The
generated hydrogen count is the source hydrogen-count sum.

No `HydrogenClosed` premise, supplied conversion, output readiness, or admission success appears;
all of them are derived. -/
theorem admitRawSpatial?_of_raw_expanded
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
                  semantic.atomCount = molecule.withExplicitHydrogens.atomCount ∧
                    molecule.withExplicitHydrogens.HydrogenClosed ∧
                      molecule.withExplicitHydrogens.WellFormed ∧
                        input.certified.certified.input.molecule.LocalizedCIPGraphReady ∧
                          (∀ index, index < molecule.atomCount →
                            listGet? semantic.atoms index =
                              (molecule.atomAt? index).bind AtomSpec.toSemanticAtom?) ∧
                            molecule.withExplicitHydrogens.atomCount =
                              molecule.atomCount +
                                ((List.range molecule.atomCount).map
                                  molecule.hydrogenCountAt).sum := by
  obtain ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, inventory,
    count⟩ :=
    RawHydrogenExpandedGraphReadiness.admitRawSpatial?_of_raw_withExplicitHydrogens
      molecule spatial rawReady spatialLength
  refine ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, inventory,
    count, expandedHydrogenClosed molecule, ?_, ?_, ?_, ?_⟩
  · exact (expandedSourceReady_of_rawReady molecule rawReady).1.1
  · exact input.certified.graphReady
  · intro index bound
    rw [inventory index,
      RawMolecule.withExplicitHydrogens_atomAt?_bind_toSemanticAtom?_of_lt molecule index bound]
  · exact withExplicitHydrogens_atomCount_eq_sum molecule

/-- The source atom inventory survives the construction verbatim at every source index. -/
theorem source_inventory_of_raw_expanded
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
  obtain ⟨semantic, input, _converted, accepted, moleculeEq, _agreement, spatialEq, _inventory,
    _count, _closed, _wellFormed, _ready, sourceInventory, _atomCount⟩ :=
    admitRawSpatial?_of_raw_expanded molecule spatial rawReady spatialLength
  exact ⟨semantic, input, accepted, moleculeEq, spatialEq, sourceInventory⟩

/-! ## Certified finite graph alignment -/

/-- **The certified finite CIP graph is aligned with the expanded intake.**

The admitted certificate's molecule has exactly the expanded atom count, so its vertex type
`Fin input.certified.certified.input.molecule.atomCount` is the finite atom index type of the
expanded graph.  Its atomic number and Rule-2 mass fields are exactly the certified input
molecule's source-backed atom data.  The last component exposes the source-backed mass (rather than
the constructor's total `getD 0` fallback) using the certificate's own `LocalizedCIPGraphReady`. -/
theorem certifiedFiniteGraph_alignment
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule)
    (spatialLength : spatial.positions.length = molecule.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      input.certified.certified.input.molecule = semantic ∧
        input.certified.certified.input.molecule.atomCount =
          molecule.withExplicitHydrogens.atomCount ∧
          Fintype.card (Fin input.certified.certified.input.molecule.atomCount) =
            molecule.withExplicitHydrogens.atomCount ∧
            (∀ index : Fin input.certified.certified.input.molecule.atomCount,
              input.certified.moleculeGraph.atomZ index =
                (input.certified.certified.input.molecule.atoms.get index).element.atomicNumber) ∧
              (∀ index : Fin input.certified.certified.input.molecule.atomCount,
                input.certified.moleculeGraph.atomMass index =
                  (input.certified.certified.input.molecule.atoms.get index).rule2MassPico?.getD 0) ∧
                (∀ index : Fin input.certified.certified.input.molecule.atomCount,
                  ∃ mass,
                    (input.certified.certified.input.molecule.atoms.get index).rule2MassPico? =
                      some mass ∧
                      input.certified.moleculeGraph.atomMass index = mass) := by
  obtain ⟨semantic, input, _converted, _accepted, moleculeEq, _agreement, _spatialEq, _inventory,
    count, _closed, _wellFormed, _ready, _prefix, _atomCount⟩ :=
    admitRawSpatial?_of_raw_expanded molecule spatial rawReady spatialLength
  refine ⟨semantic, input, moleculeEq, ?_, ?_, ?_, ?_, ?_⟩
  · exact moleculeEq ▸ count
  · rw [Fintype.card_fin]
    exact moleculeEq ▸ count
  · intro index
    exact SemanticMolecule.toLocalizedMoleculeGraph_atomZ
      input.certified.certified.input.molecule index
  · intro index
    exact SemanticMolecule.toLocalizedMoleculeGraph_atomMass
      input.certified.certified.input.molecule index
  · intro index
    simpa [CertifiedLocalizedCIPInput.moleculeGraph] using
      SemanticMolecule.toLocalizedMoleculeGraph_atomMass_eq_of_ready
        input.certified.certified.input.molecule input.certified.graphReady index

/-! ## The normalized runtime object -/

/-- Transparent source gate under which `normalizeUnspecifiedBonds` lands in the localized source
gate.  It is the source gate itself, with the bond condition weakened from "localized covalent" to
"localized covalent or unspecified".  Aromatic spellings remain excluded. -/
def RawNormalizationSourceReady (molecule : RawMolecule) : Prop :=
  molecule.Admissible ∧
    (∀ atom, atom ∈ molecule.atoms → atom.aromatic = false) ∧
      molecule.Rule2MassesKnown ∧
        ∀ bond, bond ∈ molecule.bonds →
          bond.kind.IsLocalizedCovalent ∨ bond.kind = ParsedBondKind.unspecified

/-- Normalizing an unspecified bond of a non-aromatic molecule always yields the ordinary single
bond; every other accepted spelling is unchanged.  Consequently normalization can only help the
localized bond gate. -/
theorem isLocalizedCovalent_of_normalizeUnspecifiedBond (molecule : RawMolecule) (bond : RawBond)
    (sourceAllowed : bond.kind.IsLocalizedCovalent ∨ bond.kind = ParsedBondKind.unspecified)
    (nonAromatic : ∀ atom, atom ∈ molecule.atoms → atom.aromatic = false) :
    (molecule.normalizeUnspecifiedBond bond).kind.IsLocalizedCovalent := by
  rcases bond with ⟨source, target, kind⟩
  cases kind with
  | unspecified =>
      simp only [RawMolecule.normalizeUnspecifiedBond]
      cases sourceLookup : molecule.atomAt? source with
      | none => exact ⟨1, rfl⟩
      | some left =>
          cases targetLookup : molecule.atomAt? target with
          | none => exact ⟨1, rfl⟩
          | some right =>
              have leftNonAromatic : left.aromatic = false :=
                nonAromatic left
                  (listGet?_eq_some_implies_mem molecule.atoms source left
                    (by simpa [RawMolecule.atomAt?] using sourceLookup))
              have rightNonAromatic : right.aromatic = false :=
                nonAromatic right
                  (listGet?_eq_some_implies_mem molecule.atoms target right
                    (by simpa [RawMolecule.atomAt?] using targetLookup))
              simp only [defaultBondKind, leftNonAromatic, rightNonAromatic, Bool.false_and,
                Bool.false_eq_true, if_false]
              exact ⟨1, rfl⟩
  | single => exact ⟨1, rfl⟩
  | double => exact ⟨2, rfl⟩
  | triple => exact ⟨3, rfl⟩
  | up => exact ⟨1, rfl⟩
  | down => exact ⟨1, rfl⟩
  | aromatic =>
      rcases sourceAllowed with ⟨order, orderEq⟩ | impossible
      · simp [ParsedBondKind.localizedBondOrder?] at orderEq
      · exact absurd impossible (by intro h; cases h)

/-- **Normalization lands in the localized source gate.**  The source gate with unspecified bonds
allowed is sufficient for `normalizeUnspecifiedBonds` to satisfy `RawLocalizedGraphSourceReady`. -/
theorem normalizeUnspecifiedBonds_rawReady_of_sourceReady (molecule : RawMolecule)
    (sourceReady : RawNormalizationSourceReady molecule) :
    RawLocalizedGraphSourceReady molecule.normalizeUnspecifiedBonds := by
  unfold RawNormalizationSourceReady at sourceReady
  unfold RawLocalizedGraphSourceReady
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact RawMolecule.normalizeUnspecifiedBonds_admissible molecule sourceReady.1
  · intro atom member
    exact sourceReady.2.1 atom
      (by simpa [RawMolecule.normalizeUnspecifiedBonds] using member)
  · exact (RawMolecule.normalizeUnspecifiedBonds_rule2MassesKnown molecule).mpr
      sourceReady.2.2.1
  · intro bond member
    have mapped : ∃ sourceBond, sourceBond ∈ molecule.bonds ∧
        molecule.normalizeUnspecifiedBond sourceBond = bond := by
      simpa [RawMolecule.normalizeUnspecifiedBonds] using member
    obtain ⟨sourceBond, sourceMember, bondEq⟩ := mapped
    rw [← bondEq]
    exact isLocalizedCovalent_of_normalizeUnspecifiedBond molecule sourceBond
      (sourceReady.2.2.2 sourceBond sourceMember) sourceReady.2.1

/-- **Characterization of the normalized source gate.**  If the normalized molecule passes the
localized source gate, then the original molecule is admitted, non-aromatic, Rule-2 covered, and
every source bond is either localized covalent or unspecified.  Only these valid source gates are
asserted; in particular no aromatic bond spelling is claimed to normalize into the localized
domain. -/
theorem sourceReady_of_normalizeUnspecifiedBonds_ready (molecule : RawMolecule)
    (ready : RawLocalizedGraphSourceReady molecule.normalizeUnspecifiedBonds) :
    RawNormalizationSourceReady molecule := by
  unfold RawLocalizedGraphSourceReady at ready
  unfold RawNormalizationSourceReady
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro bond member
      have normalizedMember :
          molecule.normalizeUnspecifiedBond bond ∈ molecule.normalizeUnspecifiedBonds.bonds :=
        List.mem_map.mpr ⟨bond, member, rfl⟩
      have endpoints := ready.1.1 (molecule.normalizeUnspecifiedBond bond) normalizedMember
      simpa [RawMolecule.BondEndpointsOK, RawMolecule.normalizeUnspecifiedBonds] using endpoints
    · have unique := ready.1.2
      simpa [RawMolecule.BondRecordsUnique, RawMolecule.normalizeUnspecifiedBonds,
        List.map_map, Function.comp_def] using unique
  · intro atom member
    exact ready.2.1 atom (by simpa [RawMolecule.normalizeUnspecifiedBonds] using member)
  · exact (RawMolecule.normalizeUnspecifiedBonds_rule2MassesKnown molecule).mp ready.2.2.1
  · intro bond member
    have normalizedMember :
        molecule.normalizeUnspecifiedBond bond ∈ molecule.normalizeUnspecifiedBonds.bonds :=
      List.mem_map.mpr ⟨bond, member, rfl⟩
    have localized := ready.2.2.2 (molecule.normalizeUnspecifiedBond bond) normalizedMember
    rcases bond with ⟨source, target, kind⟩
    cases kind with
    | unspecified => exact Or.inr rfl
    | single =>
        exact Or.inl (by simpa [RawMolecule.normalizeUnspecifiedBond] using localized)
    | double =>
        exact Or.inl (by simpa [RawMolecule.normalizeUnspecifiedBond] using localized)
    | triple =>
        exact Or.inl (by simpa [RawMolecule.normalizeUnspecifiedBond] using localized)
    | up =>
        exact Or.inl (by simpa [RawMolecule.normalizeUnspecifiedBond] using localized)
    | down =>
        exact Or.inl (by simpa [RawMolecule.normalizeUnspecifiedBond] using localized)
    | aromatic =>
        exact absurd localized (by
          simp [RawMolecule.normalizeUnspecifiedBond, ParsedBondKind.IsLocalizedCovalent,
            ParsedBondKind.localizedBondOrder?])

/-- **Actual normalized runtime admission.**  When `normalizeUnspecifiedBonds` passes the localized
source gate, the runtime object `normalizeUnspecifiedBonds.withExplicitHydrogens` is admitted for
the caller's actual expanded coordinates, with no `HydrogenClosed` premise. -/
theorem admitRawSpatial?_of_normalizedExpanded
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule.normalizeUnspecifiedBonds)
    (spatialLength : spatial.positions.length =
      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.toSemanticMolecule? =
          some semantic ∧
        LocalizedReference.admitRawSpatial?
            molecule.normalizeUnspecifiedBonds.withExplicitHydrogens spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.AuthoritativeStructureAgreement
              input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                (∀ index, listGet? semantic.atoms index =
                  (molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomAt? index).bind
                    AtomSpec.toSemanticAtom?) ∧
                  semantic.atomCount =
                    molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomCount ∧
                    molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.HydrogenClosed ∧
                      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.WellFormed ∧
                        input.certified.certified.input.molecule.LocalizedCIPGraphReady ∧
                          (∀ index, index < molecule.normalizeUnspecifiedBonds.atomCount →
                            listGet? semantic.atoms index =
                              (molecule.normalizeUnspecifiedBonds.atomAt? index).bind
                                AtomSpec.toSemanticAtom?) ∧
                            molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomCount =
                              molecule.normalizeUnspecifiedBonds.atomCount +
                                ((List.range molecule.normalizeUnspecifiedBonds.atomCount).map
                                  molecule.normalizeUnspecifiedBonds.hydrogenCountAt).sum :=
  admitRawSpatial?_of_raw_expanded molecule.normalizeUnspecifiedBonds spatial rawReady spatialLength

/-- **Runtime admission from the valid source gate.**  The original parsed molecule only has to
satisfy `RawNormalizationSourceReady`; normalization and hydrogen expansion are both executed by the
pipeline, and the resulting actual expanded graph is admitted for the caller's actual coordinates. -/
theorem admitRawSpatial?_of_sourceReady_normalized
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (sourceReady : RawNormalizationSourceReady molecule)
    (spatialLength : spatial.positions.length =
      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.toSemanticMolecule? =
          some semantic ∧
        LocalizedReference.admitRawSpatial?
            molecule.normalizeUnspecifiedBonds.withExplicitHydrogens spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.AuthoritativeStructureAgreement
              input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                semantic.atomCount =
                  molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomCount := by
  obtain ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, _inventory,
    count, _closed, _wellFormed, _ready, _prefix, _atomCount⟩ :=
    admitRawSpatial?_of_normalizedExpanded molecule spatial
      (normalizeUnspecifiedBonds_rawReady_of_sourceReady molecule sourceReady) spatialLength
  exact ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, count⟩

/-! ## Non-vacuity: unbracketed methane

The fidelity module proved that unbracketed methane passes the source gate but is *not*
`HydrogenClosed`; the old bridge therefore could not be applied to it.  The construction here
applies, and the admitted semantic molecule has all five expanded atoms. -/

open RawIntakeMaterializationCounterexample

/-- Five actual coordinates for the runtime object of methane, which has one carbon and four
generated hydrogens. -/
def methaneExpandedSpatial : SpatialConfiguration :=
  { positions := List.replicate 5 { x := 0, y := 0, z := 0 } }

theorem methaneExpandedSpatial_length :
    methaneExpandedSpatial.positions.length =
      sourceMethane.withExplicitHydrogens.atomCount := by
  rw [sourceMethane_withExplicitHydrogens_atomCount]
  rfl

/-- **The HydrogenClosed premise is genuinely removed.**  The source methane graph is outside
`HydrogenClosed`; its actual explicit-hydrogen expansion is closed and admitted. The expanded
semantic molecule has five atoms rather than the one atom of the raw heavy-atom conversion. -/
theorem methane_expanded_admission :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      sourceMethane.withExplicitHydrogens.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? sourceMethane.withExplicitHydrogens
            methaneExpandedSpatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            semantic.atomCount = 5 := by
  obtain ⟨semantic, input, converted, accepted, moleculeEq, _agreement, _spatialEq, _inventory,
    count, _closed, _wellFormed, _ready, _prefix, _atomCount⟩ :=
    admitRawSpatial?_of_raw_expanded sourceMethane methaneExpandedSpatial sourceMethane_ready
      methaneExpandedSpatial_length
  exact ⟨semantic, input, converted, accepted, moleculeEq,
    count.trans sourceMethane_withExplicitHydrogens_atomCount⟩

end RawExpandedIntakeConstruction

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.wellFormed_of_rawReady
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.wellFormed_withExplicitHydrogens_of_rawReady
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.admissible_withExplicitHydrogens_of_rawReady
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.expandedHydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.expandedHydrogenClosedCheck
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.expandedSourceReady_of_rawReady
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.expandedSourceReadyCheck_of_rawReadyCheck
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.expansionStep_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.fold_atomCount_eq
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.withExplicitHydrogens_atomCount_eq_sum
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.withExplicitHydrogens_generated_count
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.atomAt?_eq_hydrogen_of_atomCount_le
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.atomAt?_source_prefix
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.fold_generated_bond_mem
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.fold_bond_semantics
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.bond_semantics
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.bond_semantics_of_rawReady
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.fold_fresh_atom_has_generated_bond
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.fresh_atom_has_generated_single_bond
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.admitRawSpatial?_of_raw_expanded
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.source_inventory_of_raw_expanded
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.certifiedFiniteGraph_alignment
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.isLocalizedCovalent_of_normalizeUnspecifiedBond
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.normalizeUnspecifiedBonds_rawReady_of_sourceReady
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.sourceReady_of_normalizeUnspecifiedBonds_ready
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.admitRawSpatial?_of_normalizedExpanded
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.admitRawSpatial?_of_sourceReady_normalized
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.methaneExpandedSpatial_length
assert_kernel_only
  TetraStereo.OneCenter.RawExpandedIntakeConstruction.methane_expanded_admission
