import TetraStereo.OneCenter.LocalizedRawGraphReadiness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Raw intake versus hydrogen materialization

`LocalizedRawGraphReadiness.RawLocalizedGraphSourceReady` accepts a parsed raw graph and
`admitRawSpatial?_of_raw` converts exactly that graph with `RawMolecule.toSemanticMolecule?`.
That conversion is atom-index preserving but *lossy*: `AtomSpec.toSemanticAtom?` reads only the
element, isotope, charge and aromatic flag.  In particular an unbracketed organic-subset atom with
implied hydrogens is converted as a bare heavy atom; the implied hydrogen inventory is not present
in the semantic molecule at all.  The runtime SMILES path does not have this behaviour: it supplies
`parsed.withExplicitHydrogens`, where the implied hydrogens have become real atoms.

This module makes the distinction explicit.

* `RawMolecule.HydrogenClosed` is the domain on which every hydrogen-expansion step is the
  identity, so materialization inserts no atom.  It has an executable reflection `hydrogenClosed?`.
* On that domain `withExplicitHydrogens` is *structurally* the identity on atoms (up to consuming
  the inline count) and bonds, and `toSemanticMolecule?` commutes with it.  This is the
  fully-materialized domain used by the admission bridge.
* The raw-readiness gate is transported across `withExplicitHydrogens` on that domain, yielding a
  reference-admission bridge for the normalized, expanded graph together with preserved atom
  inventory and atom count.
* `RawIntakeMaterializationCounterexample` proves an *actual* accepted raw input — unbracketed
  methane — that is outside the materialized domain: raw admission converts it as one atom, while
  the runtime expanded graph has five.

Nothing here claims that raw admission is chemically complete.  On inputs with implied hydrogens
the raw semantic molecule is explicitly a heavy-atom skeleton, not the expanded graph.
-/

/-! ## Atom conversion is insensitive to the consumed inline count -/

namespace AtomSpec

/-- Materializing an atom (replacing its inline hydrogen count by `some 0`) does not change the
semantic atom produced by the parser conversion.  The conversion never reads
`explicitHydrogens?`. -/
@[simp] theorem toSemanticAtom?_materializedAtomSpec (atom : AtomSpec) :
    AtomSpec.toSemanticAtom? (RawMolecule.materializedAtomSpec atom) =
      AtomSpec.toSemanticAtom? atom := by
  unfold AtomSpec.toSemanticAtom? RawMolecule.materializedAtomSpec
  simp

end AtomSpec

namespace RawMolecule

/-! ## The fully materialized domain -/

/-- An atom list on which hydrogen materialization inserts no atom.

Every atom index carries zero implied/explicit hydrogens under the OpenSMILES policy.  On this
domain every step of the expansion fold is the identity, so `withExplicitHydrogens` inserts no
atom.  It is deliberately weaker than saying the molecule already contains explicit hydrogen
*atoms*; bracket counts `[CH0]` and ordinary atoms with saturated valence also belong. -/
def HydrogenClosed (mol : RawMolecule) : Prop :=
  ∀ idx, idx < mol.atomCount → mol.hydrogenCountAt idx = 0

/-- Executable form of `HydrogenClosed`. -/
def hydrogenClosed? (mol : RawMolecule) : Bool :=
  (List.range mol.atomCount).all fun idx => mol.hydrogenCountAt idx == 0

@[simp] theorem hydrogenClosed?_eq_true_iff (mol : RawMolecule) :
    mol.hydrogenClosed? = true ↔ mol.HydrogenClosed := by
  simp [hydrogenClosed?, HydrogenClosed, List.all_eq_true, List.mem_range, beq_iff_eq]

/-- A list-lookup bridge to the core `GetElem?` operation, used to apply `List.ext_getElem?`. -/
theorem listGet?_eq_getElem? {α : Type*} (values : List α) (index : ℕ) :
    listGet? values index = values[index]? := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => simpa [listGet?] using inductionHypothesis index

/-! ## The expansion fold on the materialized domain -/

/-- A zero hydrogen count makes one expansion step the identity. -/
theorem withExplicitHydrogensStep_eq_self_of_hydrogenCountAt_eq_zero
    (mol : RawMolecule) (state : HydrogenExpansionState) (idx : ℕ)
    (countZero : mol.hydrogenCountAt idx = 0) :
    withExplicitHydrogensStep mol state idx = state := by
  simp [withExplicitHydrogensStep, countZero]

/-- A fold of expansion steps whose indices all carry zero hydrogens is the identity. -/
theorem fold_withExplicitHydrogensStep_eq_self_of_forall_zero
    (mol : RawMolecule) (indices : List ℕ) :
    ∀ (state : HydrogenExpansionState),
      (∀ idx, idx ∈ indices → mol.hydrogenCountAt idx = 0) →
      indices.foldl (withExplicitHydrogensStep mol) state = state := by
  induction indices with
  | nil =>
      intro state zero
      rfl
  | cons idx rest inductionHypothesis =>
      intro state zero
      have idxZero : mol.hydrogenCountAt idx = 0 := zero idx (by simp)
      have restZero : ∀ atom, atom ∈ rest → mol.hydrogenCountAt atom = 0 := by
        intro atom member
        exact zero atom (by simp [member])
      rw [List.foldl_cons,
        withExplicitHydrogensStep_eq_self_of_hydrogenCountAt_eq_zero mol state idx idxZero]
      exact inductionHypothesis state restZero

/-- On a hydrogen-closed molecule the actual expansion fold is the initial accumulator. -/
theorem fold_range_withExplicitHydrogensStep_eq_initial_of_hydrogenClosed
    (mol : RawMolecule) (closed : mol.HydrogenClosed) :
    (List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol) =
      initialHydrogenExpansionState mol :=
  fold_withExplicitHydrogensStep_eq_self_of_forall_zero mol (List.range mol.atomCount)
    (initialHydrogenExpansionState mol)
    (fun idx member => closed idx (List.mem_range.mp member))

/-! ## Structural identity of `withExplicitHydrogens` on the domain -/

/-- Projection of the actual expansion fold out of `withExplicitHydrogens` (atoms). -/
theorem withExplicitHydrogens_atoms_eq_fold (mol : RawMolecule) :
    mol.withExplicitHydrogens.atoms =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atoms := rfl

/-- Projection of the actual expansion fold out of `withExplicitHydrogens` (bonds). -/
theorem withExplicitHydrogens_bonds_eq_fold (mol : RawMolecule) :
    mol.withExplicitHydrogens.bonds =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.bonds := rfl

theorem withExplicitHydrogens_atoms_of_hydrogenClosed
    (mol : RawMolecule) (closed : mol.HydrogenClosed) :
    mol.withExplicitHydrogens.atoms = mol.atoms.map materializedAtomSpec := by
  rw [withExplicitHydrogens_atoms_eq_fold,
    fold_range_withExplicitHydrogensStep_eq_initial_of_hydrogenClosed mol closed]
  rfl

theorem withExplicitHydrogens_bonds_of_hydrogenClosed
    (mol : RawMolecule) (closed : mol.HydrogenClosed) :
    mol.withExplicitHydrogens.bonds = mol.bonds := by
  rw [withExplicitHydrogens_bonds_eq_fold,
    fold_range_withExplicitHydrogensStep_eq_initial_of_hydrogenClosed mol closed]
  rfl

theorem withExplicitHydrogens_atomCount_of_hydrogenClosed
    (mol : RawMolecule) (closed : mol.HydrogenClosed) :
    mol.withExplicitHydrogens.atomCount = mol.atomCount := by
  show mol.withExplicitHydrogens.atoms.length = mol.atoms.length
  rw [withExplicitHydrogens_atoms_of_hydrogenClosed mol closed, List.length_map]

/-- Endpoint validity and unordered-edge uniqueness survive materialization on the closed domain. -/
theorem withExplicitHydrogens_admissible_of_hydrogenClosed
    (mol : RawMolecule) (admitted : mol.Admissible) (closed : mol.HydrogenClosed) :
    mol.withExplicitHydrogens.Admissible := by
  constructor
  · intro bond member
    have sourceMember : bond ∈ mol.bonds := by
      simpa [withExplicitHydrogens_bonds_of_hydrogenClosed mol closed] using member
    have sourceBounds := admitted.1 bond sourceMember
    change bond.source < mol.withExplicitHydrogens.atomCount ∧
      bond.target < mol.withExplicitHydrogens.atomCount ∧ bond.source ≠ bond.target
    rw [withExplicitHydrogens_atomCount_of_hydrogenClosed mol closed]
    exact sourceBounds
  · show (mol.withExplicitHydrogens.bonds.map RawBond.edgeKey).Nodup
    rw [withExplicitHydrogens_bonds_of_hydrogenClosed mol closed]
    exact admitted.2

/-! ## Conversion commutes on the domain -/

/-- Indexwise atom conversion through materialization is unchanged on the closed domain. -/
theorem atomAt?_withExplicitHydrogens_eq_bind_of_hydrogenClosed
    (mol : RawMolecule) (closed : mol.HydrogenClosed) (index : ℕ) :
    (mol.withExplicitHydrogens.atomAt? index).bind AtomSpec.toSemanticAtom? =
      (mol.atomAt? index).bind AtomSpec.toSemanticAtom? := by
  simp only [atomAt?]
  rw [withExplicitHydrogens_atoms_of_hydrogenClosed mol closed, listGet?_map]
  cases observed : listGet? mol.atoms index with
  | none => rfl
  | some atom => simp [AtomSpec.toSemanticAtom?_materializedAtomSpec]

/-- **Raw conversion commutes with hydrogen materialization on the fully materialized domain.**

In particular the semantic molecule obtained from the raw graph by `toSemanticMolecule?` is exactly
the one obtained from the runtime expanded graph, so the raw intake is faithful on
`HydrogenClosed` inputs. -/
theorem toSemanticMolecule?_withExplicitHydrogens_eq_of_hydrogenClosed
    (mol : RawMolecule) (closed : mol.HydrogenClosed) :
    mol.withExplicitHydrogens.toSemanticMolecule? = mol.toSemanticMolecule? := by
  cases observed : mol.toSemanticMolecule? with
  | none =>
      have expandedNone : mol.withExplicitHydrogens.toSemanticMolecule? = none := by
        cases expanded : mol.withExplicitHydrogens.toSemanticMolecule? with
        | none => rfl
        | some semantic =>
            have expandedKnown :
                ∀ atom, atom ∈ mol.withExplicitHydrogens.atoms → atom.element ≠ .wildcard :=
              (RawMolecule.toSemanticMolecule?_isSome (mol.withExplicitHydrogens)).mp
                (by simp [expanded])
            have sourceKnown : ∀ atom, atom ∈ mol.atoms → atom.element ≠ .wildcard := by
              intro atom member
              have materializedMember :
                  materializedAtomSpec atom ∈ mol.withExplicitHydrogens.atoms := by
                rw [withExplicitHydrogens_atoms_of_hydrogenClosed mol closed]
                exact List.mem_map_of_mem member
              exact expandedKnown (materializedAtomSpec atom) materializedMember
            have present := (RawMolecule.toSemanticMolecule?_isSome mol).mpr sourceKnown
            rw [observed] at present
            exact absurd present (by simp)
      rw [expandedNone]
  | some semantic =>
      have sourceKnown : ∀ atom, atom ∈ mol.atoms → atom.element ≠ .wildcard :=
        (RawMolecule.toSemanticMolecule?_isSome mol).mp (by simp [observed])
      have expandedKnown :
          ∀ atom, atom ∈ mol.withExplicitHydrogens.atoms → atom.element ≠ .wildcard := by
        intro atom member
        have mapped : atom ∈ mol.atoms.map materializedAtomSpec := by
          simpa [withExplicitHydrogens_atoms_of_hydrogenClosed mol closed] using member
        rcases List.mem_map.mp mapped with ⟨source, sourceMember, equality⟩
        rw [← equality]
        simpa using sourceKnown source sourceMember
      have expandedSome : mol.withExplicitHydrogens.toSemanticMolecule?.isSome = true :=
        (RawMolecule.toSemanticMolecule?_isSome (mol.withExplicitHydrogens)).mpr expandedKnown
      obtain ⟨converted, expanded⟩ := Option.isSome_iff_exists.mp expandedSome
      have atomEq : converted.atoms = semantic.atoms := by
        apply List.ext_getElem?
        intro index
        simp only [← listGet?_eq_getElem?]
        calc
          listGet? converted.atoms index =
              ((mol.withExplicitHydrogens).atomAt? index).bind AtomSpec.toSemanticAtom? :=
            RawMolecule.toSemanticMolecule?_atomAt?
              (mol.withExplicitHydrogens) converted expanded index
          _ = (mol.atomAt? index).bind AtomSpec.toSemanticAtom? :=
            atomAt?_withExplicitHydrogens_eq_bind_of_hydrogenClosed mol closed index
          _ = listGet? semantic.atoms index :=
            (RawMolecule.toSemanticMolecule?_atomAt? mol semantic observed index).symm
      have interactionEq : converted.interactions = semantic.interactions := by
        calc
          converted.interactions =
              (mol.withExplicitHydrogens).bonds.map RawBond.toSemanticInteraction :=
            RawMolecule.toSemanticMolecule?_interactions
              (mol.withExplicitHydrogens) converted expanded
          _ = mol.bonds.map RawBond.toSemanticInteraction := by
            rw [withExplicitHydrogens_bonds_of_hydrogenClosed mol closed]
          _ = semantic.interactions :=
            (RawMolecule.toSemanticMolecule?_interactions mol semantic observed).symm
      have convertedEq : converted = semantic := by
        rcases semantic with ⟨semanticAtoms, semanticInteractions⟩
        rcases converted with ⟨convertedAtoms, convertedInteractions⟩
        simp only [SemanticMolecule.mk.injEq]
        exact ⟨atomEq, interactionEq⟩
      rw [expanded, convertedEq]

end RawMolecule

/-! ## Transport of raw readiness to the expanded graph -/

namespace RawIntakeMaterialization

open LocalizedRawGraphReadiness

/-- On the fully materialized domain, raw graph readiness transports to the hydrogen-expanded
graph.  This is what makes the runtime expanded object acceptable to the same reference pipeline. -/
theorem rawLocalizedGraphSourceReady_withExplicitHydrogens
    (molecule : RawMolecule) (rawReady : RawLocalizedGraphSourceReady molecule)
    (materialized : molecule.HydrogenClosed) :
    RawLocalizedGraphSourceReady molecule.withExplicitHydrogens := by
  unfold RawLocalizedGraphSourceReady at rawReady ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact molecule.withExplicitHydrogens_admissible_of_hydrogenClosed rawReady.1 materialized
  · intro atom member
    have mapped : atom ∈ molecule.atoms.map RawMolecule.materializedAtomSpec := by
      simpa [RawMolecule.withExplicitHydrogens_atoms_of_hydrogenClosed molecule materialized]
        using member
    rcases List.mem_map.mp mapped with ⟨source, sourceMember, equality⟩
    rw [← equality]
    simpa using rawReady.2.1 source sourceMember
  · exact molecule.withExplicitHydrogens_preserves_rule2MassesKnown rawReady.2.2.1
  · intro bond member
    have sourceMember : bond ∈ molecule.bonds := by
      simpa [RawMolecule.withExplicitHydrogens_bonds_of_hydrogenClosed molecule materialized]
        using member
    exact rawReady.2.2.2 bond sourceMember

/-- **Reference-admission bridge for the materialized raw intake.**

The runtime path supplies `parsed.withExplicitHydrogens`.  On the fully materialized domain the raw
readiness gate is enough to pass that same expanded graph through the reference pipeline, and the
resulting semantic molecule preserves the raw atomic inventory indexwise and preserves the atom
count (the expanded graph has the same atom count as the raw graph precisely on this domain).

The chemical claim is conditional on `molecule.HydrogenClosed`; it does not assert that arbitrary
raw-readiness admissions are chemically complete. -/
theorem admitRawSpatial?_of_raw_materialized
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule)
    (materialized : molecule.HydrogenClosed)
    (spatialLength : spatial.positions.length = molecule.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.withExplicitHydrogens.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? molecule.withExplicitHydrogens spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.withExplicitHydrogens.AuthoritativeStructureAgreement
              input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                (∀ index, listGet? semantic.atoms index =
                  (molecule.atomAt? index).bind AtomSpec.toSemanticAtom?) ∧
                  semantic.atomCount = molecule.atomCount := by
  obtain ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq⟩ :=
    admitRawSpatial?_of_raw molecule.withExplicitHydrogens spatial
      (rawLocalizedGraphSourceReady_withExplicitHydrogens molecule rawReady materialized)
      spatialLength
  refine ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, ?_, ?_⟩
  · intro index
    calc
      listGet? semantic.atoms index =
          ((molecule.withExplicitHydrogens).atomAt? index).bind AtomSpec.toSemanticAtom? :=
        RawMolecule.toSemanticMolecule?_atomAt?
          (molecule.withExplicitHydrogens) semantic converted index
      _ = (molecule.atomAt? index).bind AtomSpec.toSemanticAtom? :=
        RawMolecule.atomAt?_withExplicitHydrogens_eq_bind_of_hydrogenClosed
          molecule materialized index
  · calc
      semantic.atomCount = molecule.withExplicitHydrogens.atomCount :=
        RawMolecule.toSemanticMolecule?_atomCount
          (molecule.withExplicitHydrogens) semantic converted
      _ = molecule.atomCount :=
        RawMolecule.withExplicitHydrogens_atomCount_of_hydrogenClosed molecule materialized

/-- Executable-call-site form of the materialized admission bridge. -/
theorem admitRawSpatial?_of_rawCheck_materialized
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawChecked : rawLocalizedGraphSourceReady? molecule = true)
    (materializedChecked : molecule.hydrogenClosed? = true)
    (spatialLength : spatial.positions.length = molecule.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.withExplicitHydrogens.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? molecule.withExplicitHydrogens spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.withExplicitHydrogens.AuthoritativeStructureAgreement
              input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                (∀ index, listGet? semantic.atoms index =
                  (molecule.atomAt? index).bind AtomSpec.toSemanticAtom?) ∧
                  semantic.atomCount = molecule.atomCount :=
  admitRawSpatial?_of_raw_materialized molecule spatial
    ((rawLocalizedGraphSourceReady?_eq_true_iff molecule).mp rawChecked)
    ((RawMolecule.hydrogenClosed?_eq_true_iff molecule).mp materializedChecked)
    spatialLength

/-! ## The normalized runtime object -/

theorem normalizeUnspecifiedBonds_atomCount (molecule : RawMolecule) :
    molecule.normalizeUnspecifiedBonds.atomCount = molecule.atomCount := rfl

/-- Materialization preserves the original source-token introduction lineage exactly.  Generated
hydrogen atoms carry no source token, so no fabricated predecessor is ever recorded; the lineage is
transported unchanged through atom materialization and through normalization. -/
theorem withExplicitHydrogens_sourceLineage (molecule : RawMolecule) :
    molecule.withExplicitHydrogens.introductionPredecessors =
      molecule.introductionPredecessors :=
  RawMolecule.withExplicitHydrogens_introductionPredecessors molecule

theorem normalizeUnspecifiedBonds_sourceLineage (molecule : RawMolecule) :
    molecule.normalizeUnspecifiedBonds.introductionPredecessors =
      molecule.introductionPredecessors := rfl

/-- **Bridge for the actual runtime normalized expanded graph.**

`ChemistryNormalizationResult.parsed` is `molecule.normalizeUnspecifiedBonds`; the runtime SMILES
path supplies `parsed.withExplicitHydrogens`.  Under raw readiness plus the materialized-domain
gate, the reference pipeline accepts exactly that object and preserves the original atom count. -/
theorem admitRawSpatial?_of_parsed_materialized
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (rawReady : RawLocalizedGraphSourceReady molecule.normalizeUnspecifiedBonds)
    (materialized : molecule.normalizeUnspecifiedBonds.HydrogenClosed)
    (spatialLength : spatial.positions.length =
      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.atomCount) :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.toSemanticMolecule? =
          some semantic ∧
        LocalizedReference.admitRawSpatial? molecule.normalizeUnspecifiedBonds.withExplicitHydrogens
            spatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            molecule.normalizeUnspecifiedBonds.withExplicitHydrogens.AuthoritativeStructureAgreement
              input.certified.certified.input ∧
              input.certified.certified.input.spatial? = some spatial ∧
                (∀ index, listGet? semantic.atoms index =
                  (molecule.normalizeUnspecifiedBonds.atomAt? index).bind
                    AtomSpec.toSemanticAtom?) ∧
                  semantic.atomCount = molecule.atomCount := by
  obtain ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, inventory,
    count⟩ :=
    admitRawSpatial?_of_raw_materialized molecule.normalizeUnspecifiedBonds spatial
      rawReady materialized spatialLength
  refine ⟨semantic, input, converted, accepted, moleculeEq, agreement, spatialEq, inventory, ?_⟩
  calc
    semantic.atomCount = molecule.normalizeUnspecifiedBonds.atomCount := count
    _ = molecule.atomCount := normalizeUnspecifiedBonds_atomCount molecule

end RawIntakeMaterialization

/-! ## The counterexample: an actual accepted input with implied hydrogens -/

namespace RawIntakeMaterializationCounterexample

open LocalizedRawGraphReadiness

/-- Unbracketed methane in the organic subset: one carbon, no written bonds. -/
def sourceMethane : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.C], bonds := [] }

theorem sourceMethane_atomCount : sourceMethane.atomCount = 1 := rfl

/-- The frozen Rule-2 mass datum for ordinary carbon. -/
theorem sourceMethane_rule2Mass :
    ∃ mass, RawMolecule.rule2MassPico? Element.C none = some mass := by
  obtain ⟨mass, massEq⟩ :=
    CIPRule2MassData.every_current_atomic_number_has_an_ordinary_value 6 (by decide)
  exact ⟨mass, by
    simpa [RawMolecule.rule2MassPico?, Element.atomicNumber] using massEq⟩

/-- The OpenSMILES implicit-hydrogen policy fills the lone carbon to valence four. -/
theorem sourceMethane_hydrogenCountAt_zero :
    sourceMethane.hydrogenCountAt 0 = 4 := by
  decide

/-- Unbracketed methane passes the *raw* localized readiness gate.  The carbon is a supported
element with a Rule-2 mass datum, there are no aromatic atoms and no bonds at all. -/
theorem sourceMethane_ready : RawLocalizedGraphSourceReady sourceMethane := by
  unfold RawLocalizedGraphSourceReady
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro bond member
      simp [sourceMethane] at member
    · simp [RawMolecule.BondRecordsUnique, sourceMethane]
  · intro atom member
    simp [sourceMethane] at member
    subst atom
    rfl
  · intro atom member
    simp [sourceMethane] at member
    subst atom
    simpa [AtomSpec.aliphatic] using sourceMethane_rule2Mass
  · intro bond member
    simp [sourceMethane] at member

/-- Methane is *outside* the fully materialized domain: its implied hydrogens are not zero. -/
theorem sourceMethane_not_hydrogenClosed : ¬ sourceMethane.HydrogenClosed := by
  intro closed
  have countZero := closed 0 (by simp [sourceMethane, RawMolecule.atomCount])
  rw [sourceMethane_hydrogenCountAt_zero] at countZero
  exact absurd countZero (by decide)

/-- The atom list produced by one expansion step: the step inserts no atom at a zero count and
otherwise appends exactly that many materialized hydrogen atoms. -/
theorem withExplicitHydrogensStep_atoms_eq
    (mol : RawMolecule) (state : RawMolecule.HydrogenExpansionState) (idx : ℕ) :
    (RawMolecule.withExplicitHydrogensStep mol state idx).toRawMolecule.atoms =
      state.toRawMolecule.atoms ++
        List.replicate (mol.hydrogenCountAt idx) (AtomSpec.aliphatic Element.H) := by
  unfold RawMolecule.withExplicitHydrogensStep
  by_cases zero : mol.hydrogenCountAt idx = 0
  · simp [zero]
  · have nonzeroBool : (mol.hydrogenCountAt idx == 0) = false := by
      simp [zero]
    simp [nonzeroBool, RawMolecule.HydrogenExpansionState.toRawMolecule]

theorem sourceMethane_step_atoms :
    (RawMolecule.withExplicitHydrogensStep sourceMethane
        (RawMolecule.initialHydrogenExpansionState sourceMethane) 0).toRawMolecule.atoms =
      sourceMethane.atoms.map RawMolecule.materializedAtomSpec ++
        List.replicate 4 (AtomSpec.aliphatic Element.H) := by
  rw [withExplicitHydrogensStep_atoms_eq, sourceMethane_hydrogenCountAt_zero]
  simp [RawMolecule.initialHydrogenExpansionState, sourceMethane,
    RawMolecule.HydrogenExpansionState.toRawMolecule]

theorem sourceMethane_withExplicitHydrogens_atoms :
    sourceMethane.withExplicitHydrogens.atoms =
      [RawMolecule.materializedAtomSpec (AtomSpec.aliphatic Element.C)] ++
        List.replicate 4 (AtomSpec.aliphatic Element.H) := by
  rw [RawMolecule.withExplicitHydrogens_atoms_eq_fold]
  rw [show List.range sourceMethane.atomCount = [0] from by decide]
  rw [List.foldl_cons, List.foldl_nil]
  rw [sourceMethane_step_atoms]
  rfl

/-- The runtime expanded graph has five atoms: one carbon plus four materialized hydrogens. -/
theorem sourceMethane_withExplicitHydrogens_atomCount :
    sourceMethane.withExplicitHydrogens.atomCount = 5 := by
  show sourceMethane.withExplicitHydrogens.atoms.length = 5
  rw [sourceMethane_withExplicitHydrogens_atoms]
  simp

/-- Raw conversion of methane succeeds and yields a one-atom semantic molecule. -/
theorem sourceMethane_toSemanticMolecule_atomCount :
    ∃ semantic, sourceMethane.toSemanticMolecule? = some semantic ∧
      semantic.atomCount = 1 := by
  have someTrue : sourceMethane.toSemanticMolecule?.isSome = true :=
    (RawMolecule.toSemanticMolecule?_isSome sourceMethane).mpr (by
      intro atom member
      simp [sourceMethane] at member
      subst atom
      simp [AtomSpec.aliphatic])
  obtain ⟨semantic, converted⟩ := Option.isSome_iff_exists.mp someTrue
  refine ⟨semantic, converted, ?_⟩
  calc
    semantic.atomCount = sourceMethane.atomCount :=
      RawMolecule.toSemanticMolecule?_atomCount sourceMethane semantic converted
    _ = 1 := rfl

/-- A one-coordinate spatial configuration, exactly matching the raw one-atom graph. -/
def sourceMethaneSpatial : SpatialConfiguration :=
  { positions := [{ x := 0, y := 0, z := 0 }] }

theorem sourceMethaneSpatial_length :
    sourceMethaneSpatial.positions.length = sourceMethane.atomCount := rfl

/-- **Actual raw-admission counterexample.**

Unbracketed methane is accepted by the reference raw path with a single coordinate, and the
resulting semantic molecule has one atom.  The runtime normalized expanded graph of the same input
has five atoms.  Hence the raw readiness theorem does not preserve the atomic inventory of the
runtime expanded intake: it converts a heavy-atom skeleton and silently omits the four implied
hydrogens.  This is a concrete input, not a hypothetical inconsistency. -/
theorem sourceMethane_raw_admission_missing_implicit_hydrogens :
    ∃ (semantic : SemanticMolecule) (input : LocalizedReference.Input),
      sourceMethane.toSemanticMolecule? = some semantic ∧
        LocalizedReference.admitRawSpatial? sourceMethane sourceMethaneSpatial = some input ∧
          input.certified.certified.input.molecule = semantic ∧
            semantic.atomCount = 1 ∧
              sourceMethane.withExplicitHydrogens.atomCount = 5 ∧
                semantic.atomCount ≠ sourceMethane.withExplicitHydrogens.atomCount := by
  obtain ⟨semantic, input, converted, accepted, moleculeEq, _agreement, _spatialEq⟩ :=
    admitRawSpatial?_of_raw sourceMethane sourceMethaneSpatial
      sourceMethane_ready sourceMethaneSpatial_length
  have countOne : semantic.atomCount = 1 := by
    calc
      semantic.atomCount = sourceMethane.atomCount :=
        RawMolecule.toSemanticMolecule?_atomCount sourceMethane semantic converted
      _ = 1 := rfl
  refine ⟨semantic, input, converted, accepted, moleculeEq, countOne,
    sourceMethane_withExplicitHydrogens_atomCount, ?_⟩
  rw [countOne, sourceMethane_withExplicitHydrogens_atomCount]
  decide

end RawIntakeMaterializationCounterexample

/-! ## Kernel-authority certificates -/

assert_kernel_only TetraStereo.OneCenter.AtomSpec.toSemanticAtom?_materializedAtomSpec
assert_kernel_only TetraStereo.OneCenter.RawMolecule.hydrogenClosed?_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.RawMolecule.listGet?_eq_getElem?
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogensStep_eq_self_of_hydrogenCountAt_eq_zero
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.fold_withExplicitHydrogensStep_eq_self_of_forall_zero
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.fold_range_withExplicitHydrogensStep_eq_initial_of_hydrogenClosed
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_atoms_eq_fold
assert_kernel_only TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_bonds_eq_fold
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_atoms_of_hydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_bonds_of_hydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_atomCount_of_hydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.withExplicitHydrogens_admissible_of_hydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.atomAt?_withExplicitHydrogens_eq_bind_of_hydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.toSemanticMolecule?_withExplicitHydrogens_eq_of_hydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterialization.rawLocalizedGraphSourceReady_withExplicitHydrogens
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterialization.admitRawSpatial?_of_raw_materialized
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterialization.admitRawSpatial?_of_rawCheck_materialized
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterialization.normalizeUnspecifiedBonds_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterialization.withExplicitHydrogens_sourceLineage
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterialization.normalizeUnspecifiedBonds_sourceLineage
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterialization.admitRawSpatial?_of_parsed_materialized
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethaneSpatial_length
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_rule2Mass
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_hydrogenCountAt_zero
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_ready
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_not_hydrogenClosed
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.withExplicitHydrogensStep_atoms_eq
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_step_atoms
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_withExplicitHydrogens_atoms
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_withExplicitHydrogens_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_toSemanticMolecule_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RawIntakeMaterializationCounterexample.sourceMethane_raw_admission_missing_implicit_hydrogens

end TetraStereo.OneCenter
