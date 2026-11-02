import TetraStereo.OneCenter.ExplicitHydrogens

set_option autoImplicit false

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

namespace TetraStereo.UniversalProof.ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure

































































/-- Fresh hydrogen atom indices appended when one atom's implied hydrogens are materialized. -/
def freshHydrogenIds (base count : ℕ) : List ℕ :=
  (List.range count).map fun offset => base + offset

/-- The single bonds created for those fresh hydrogens: every one runs from the materialized parent
atom to exactly one appended hydrogen. -/
def freshHydrogenBonds (parent base count : ℕ) : List RawBond :=
  (freshHydrogenIds base count).map fun target =>
    { source := parent, target := target, kind := ParsedBondKind.single }

/-- The hydrogen-expansion fold result, named so the transport statements can talk about it directly. -/
abbrev expansionResult (mol : RawMolecule) : HydrogenExpansionState :=
  (List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
    (initialHydrogenExpansionState mol)

theorem mem_freshHydrogenIds_iff (base count index : ℕ) :
    index ∈ freshHydrogenIds base count ↔ ∃ offset, offset < count ∧ index = base + offset := by
  unfold freshHydrogenIds
  rw [List.mem_map]
  constructor
  · rintro ⟨offset, offsetMem, equal⟩
    exact ⟨offset, List.mem_range.mp offsetMem, equal.symm⟩
  · rintro ⟨offset, offsetLt, rfl⟩
    exact ⟨offset, List.mem_range.mpr offsetLt, rfl⟩

theorem mem_freshHydrogenBonds_iff (parent base count : ℕ) (bond : RawBond) :
    bond ∈ freshHydrogenBonds parent base count ↔
      ∃ offset, offset < count ∧
        bond = { source := parent, target := base + offset, kind := ParsedBondKind.single } := by
  unfold freshHydrogenBonds
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨middle, middleMem, rfl⟩
    rcases (mem_freshHydrogenIds_iff base count middle).mp middleMem with
      ⟨offset, offsetLt, rfl⟩
    exact ⟨offset, offsetLt, rfl⟩
  · rintro ⟨offset, offsetLt, rfl⟩
    apply List.mem_map.mpr
    exact ⟨base + offset,
      (mem_freshHydrogenIds_iff base count (base + offset)).mpr ⟨offset, offsetLt, rfl⟩, rfl⟩

/-- Every generated hydrogen bond carries the materialized atom as its source. -/
theorem freshHydrogenBonds_source (parent base count : ℕ) {bond : RawBond}
    (member : bond ∈ freshHydrogenBonds parent base count) : bond.source = parent := by
  obtain ⟨offset, _, rfl⟩ := (mem_freshHydrogenBonds_iff parent base count bond).mp member
  rfl

/-- Every generated hydrogen bond points into the fresh block `[base, base + count)`. -/
theorem freshHydrogenBonds_target_bounds (parent base count : ℕ) {bond : RawBond}
    (member : bond ∈ freshHydrogenBonds parent base count) :
    base ≤ bond.target ∧ bond.target < base + count := by
  obtain ⟨offset, offsetLt, rfl⟩ := (mem_freshHydrogenBonds_iff parent base count bond).mp member
  exact ⟨Nat.le_add_right base offset, Nat.add_lt_add_left offsetLt base⟩

/-- Every generated hydrogen bond is a single bond. -/
theorem freshHydrogenBonds_kind (parent base count : ℕ) {bond : RawBond}
    (member : bond ∈ freshHydrogenBonds parent base count) :
    bond.kind = ParsedBondKind.single := by
  obtain ⟨offset, _, rfl⟩ := (mem_freshHydrogenBonds_iff parent base count bond).mp member
  rfl

/-- Generated hydrogen bonds are pairwise distinct records, because their targets are. -/
theorem freshHydrogenBonds_nodup (parent base count : ℕ) :
    (freshHydrogenBonds parent base count).Nodup := by
  unfold freshHydrogenBonds freshHydrogenIds
  exact (List.nodup_range.map (by
    intro first second equal
    exact Nat.add_left_cancel equal)).map (by
      intro first second equal
      exact congrArg RawBond.target equal)

/-- A generated hydrogen bond exists only when the count is positive. -/
theorem mem_freshHydrogenBonds_pos (parent base count : ℕ) {bond : RawBond}
    (member : bond ∈ freshHydrogenBonds parent base count) : 0 < count := by
  obtain ⟨offset, offsetLt, _⟩ := (mem_freshHydrogenBonds_iff parent base count bond).mp member
  exact Nat.lt_of_le_of_lt (Nat.zero_le offset) offsetLt

theorem withExplicitHydrogensStep_atoms_length
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) :
    (withExplicitHydrogensStep mol state index).1.length =
      state.1.length + mol.hydrogenCountAt index := by
  simp only [withExplicitHydrogensStep]
  split
  · rename_i zero
    have countZero : mol.hydrogenCountAt index = 0 := by simpa using zero
    simp [countZero]
  · simp [List.length_append, List.length_replicate]

theorem withExplicitHydrogensStep_atomCount
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) :
    (withExplicitHydrogensStep mol state index).toRawMolecule.atomCount =
      state.1.length + mol.hydrogenCountAt index := by
  have lengthForm := withExplicitHydrogensStep_atoms_length mol state index
  simpa [HydrogenExpansionState.toRawMolecule, atomCount] using lengthForm

/-- One materialization step rewrites the accumulator bond list to exactly the old records plus the
generated hydrogen bonds, as a multiset. -/
theorem withExplicitHydrogensStep_bonds_perm
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) :
    (withExplicitHydrogensStep mol state index).toRawMolecule.bonds.Perm
      (state.toRawMolecule.bonds ++
        freshHydrogenBonds index state.1.length (mol.hydrogenCountAt index)) := by
  simp only [withExplicitHydrogensStep]
  split
  · rename_i zero
    have countZero : mol.hydrogenCountAt index = 0 := by simpa using zero
    have emptyExtra :
        freshHydrogenBonds index state.1.length (mol.hydrogenCountAt index) = [] := by
      rw [countZero]
      rfl
    rw [emptyExtra, List.append_nil]
  · dsimp only [HydrogenExpansionState.toRawMolecule]
    exact spliceHydrogenBondsWithPredecessor_perm _ _ _ _

/-- Exact membership transport for one step. -/
theorem withExplicitHydrogensStep_bonds_mem_iff
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) (bond : RawBond) :
    bond ∈ (withExplicitHydrogensStep mol state index).toRawMolecule.bonds ↔
      bond ∈ state.toRawMolecule.bonds ∨
        bond ∈ freshHydrogenBonds index state.1.length (mol.hydrogenCountAt index) := by
  rw [(withExplicitHydrogensStep_bonds_perm mol state index).mem_iff]
  exact List.mem_append

/-! ## The reviewed transport invariant (with the two new clauses) -/

/-- Accumulator invariant for the full expansion fold.

`originalRetained` records that every source bond survives as the identical record.
`generatedShape` records that every non-source bond is a generated single bond from a real parent
index (`< mol.atomCount`) to an appended hydrogen that currently lies inside the accumulator's atom
block. `generatedParentDemand` is the new clause: the recorded parent has strictly positive implied
hydrogen demand. -/
structure ReviewedBondTransportInvariant (mol : RawMolecule)
    (state : HydrogenExpansionState) : Prop where
  originalRetained : ∀ bond, bond ∈ mol.bonds → bond ∈ state.toRawMolecule.bonds
  generatedShape : ∀ bond, bond ∈ state.toRawMolecule.bonds → bond ∉ mol.bonds →
    bond.source < mol.atomCount ∧ mol.atomCount ≤ bond.target ∧
      bond.target < state.toRawMolecule.atomCount ∧ bond.kind = ParsedBondKind.single
  generatedParentDemand : ∀ bond, bond ∈ state.toRawMolecule.bonds → bond ∉ mol.bonds →
    0 < mol.hydrogenCountAt bond.source

theorem initialState_reviewedInvariant (mol : RawMolecule) :
    ReviewedBondTransportInvariant mol (initialHydrogenExpansionState mol) := by
  constructor
  · intro bond member
    simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule] using member
  · intro bond member absent
    exact absurd (by
      simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule] using member)
      absent
  · intro bond member absent
    exact absurd (by
      simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule] using member)
      absent

theorem withExplicitHydrogensStep_preserves_reviewedInvariant
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (indexBound : index < mol.atomCount)
    (shape : HydrogenExpansionState.ShapeInvariant mol state)
    (invariant : ReviewedBondTransportInvariant mol state) :
    ReviewedBondTransportInvariant mol (withExplicitHydrogensStep mol state index) := by
  constructor
  · intro bond source
    exact (withExplicitHydrogensStep_bonds_mem_iff mol state index bond).mpr
      (Or.inl (invariant.originalRetained bond source))
  · intro bond member absent
    rcases (withExplicitHydrogensStep_bonds_mem_iff mol state index bond).mp member with old | fresh
    · obtain ⟨sourceBound, targetLower, targetUpper, kindEq⟩ :=
        invariant.generatedShape bond old absent
      refine ⟨sourceBound, targetLower, ?_, kindEq⟩
      rw [withExplicitHydrogensStep_atomCount]
      exact lt_of_lt_of_le targetUpper
        (Nat.le_add_right state.1.length (mol.hydrogenCountAt index))
    · obtain ⟨offset, offsetLt, rfl⟩ :=
        (mem_freshHydrogenBonds_iff index state.1.length (mol.hydrogenCountAt index) bond).mp fresh
      refine ⟨indexBound, ?_, ?_, rfl⟩
      · exact Nat.le_trans shape.originalAtoms (Nat.le_add_right state.1.length offset)
      · rw [withExplicitHydrogensStep_atomCount]
        exact Nat.add_lt_add_left offsetLt state.1.length
  · intro bond member absent
    rcases (withExplicitHydrogensStep_bonds_mem_iff mol state index bond).mp member with old | fresh
    · exact invariant.generatedParentDemand bond old absent
    · obtain ⟨offset, offsetLt, rfl⟩ :=
        (mem_freshHydrogenBonds_iff index state.1.length (mol.hydrogenCountAt index) bond).mp fresh
      exact Nat.lt_of_le_of_lt (Nat.zero_le offset) offsetLt

theorem fold_reviewedInvariant
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (indicesBound : ∀ index ∈ indices, index < mol.atomCount)
    (shape : HydrogenExpansionState.ShapeInvariant mol state)
    (invariant : ReviewedBondTransportInvariant mol state) :
    ReviewedBondTransportInvariant mol
      (indices.foldl (withExplicitHydrogensStep mol) state) := by
  induction indices generalizing state with
  | nil => exact invariant
  | cons index rest inductionHypothesis =>
      have indexBound : index < mol.atomCount := indicesBound index (by simp)
      have restBound : ∀ item ∈ rest, item < mol.atomCount := by
        intro item present
        exact indicesBound item (by simp [present])
      have nextShape :=
        withExplicitHydrogensStep_preserves_shapeInvariant mol state index shape
      have nextInvariant :=
        withExplicitHydrogensStep_preserves_reviewedInvariant mol state index
          indexBound shape invariant
      exact inductionHypothesis (withExplicitHydrogensStep mol state index)
        restBound nextShape nextInvariant

theorem reviewedBondTransport (mol : RawMolecule) :
    ReviewedBondTransportInvariant mol (expansionResult mol) :=
  fold_reviewedInvariant mol (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (by intro index member; exact List.mem_range.mp member)
    (initialHydrogenExpansionState_shapeInvariant mol)
    (initialState_reviewedInvariant mol)

/-! ## Bridging the fold result back to `withExplicitHydrogens` -/

/-- `withExplicitHydrogens` canonicalizes the fold's written order and retains the source's
introduction history. Generated hydrogens do not acquire fabricated source-token history. -/
theorem withExplicitHydrogens_eq (mol : RawMolecule) :
    mol.withExplicitHydrogens =
      { (expansionResult mol).toRawMolecule.withExactWrittenNeighbors with
        introductionPredecessors := mol.introductionPredecessors } := rfl

@[simp] theorem withExplicitHydrogens_bonds_eq_fold (mol : RawMolecule) :
    mol.withExplicitHydrogens.bonds = (expansionResult mol).toRawMolecule.bonds := rfl

@[simp] theorem withExplicitHydrogens_atomCount_eq (mol : RawMolecule) :
    mol.withExplicitHydrogens.atomCount = (expansionResult mol).toRawMolecule.atomCount := rfl

@[simp] theorem withExplicitHydrogens_atomAt?_eq (mol : RawMolecule) (idx : ℕ) :
    mol.withExplicitHydrogens.atomAt? idx = (expansionResult mol).toRawMolecule.atomAt? idx := rfl

@[simp] theorem withExplicitHydrogens_incidentBondOrderSum_eq (mol : RawMolecule) (idx : ℕ) :
    mol.withExplicitHydrogens.incidentBondOrderSum idx =
      (expansionResult mol).toRawMolecule.incidentBondOrderSum idx := rfl

/-! ## The public transport statements -/

/-- The actual production expansion retains every source bond as the identical record,
unconditionally. -/
theorem withExplicitHydrogens_retains_original_bonds (mol : RawMolecule) :
    ∀ bond, bond ∈ mol.bonds → bond ∈ mol.withExplicitHydrogens.bonds := by
  intro bond source
  rw [withExplicitHydrogens_bonds_eq_fold]
  exact (reviewedBondTransport mol).originalRetained bond source

/-- Any returned bond that is not a source bond is a single bond from a real parent index to an
appended hydrogen with a valid index. (This is the archival shape clause, re-derived.) -/
theorem withExplicitHydrogens_generated_bond_shape
    (mol : RawMolecule) {bond : RawBond}
    (member : bond ∈ mol.withExplicitHydrogens.bonds) (absent : bond ∉ mol.bonds) :
    bond.source < mol.atomCount ∧ mol.atomCount ≤ bond.target ∧
      bond.target < mol.withExplicitHydrogens.atomCount ∧
      bond.kind = ParsedBondKind.single := by
  have memberFold : bond ∈ (expansionResult mol).toRawMolecule.bonds := by
    rwa [withExplicitHydrogens_bonds_eq_fold] at member
  obtain ⟨sourceBound, targetLower, targetUpper, kindEq⟩ :=
    (reviewedBondTransport mol).generatedShape bond memberFold absent
  exact ⟨sourceBound, targetLower, by rwa [withExplicitHydrogens_atomCount_eq], kindEq⟩

/-- **New clause.** Every non-source returned bond is sourced at an atom with strictly positive
implied hydrogen demand: the generated bond really belongs to a parent that demanded it. -/
theorem withExplicitHydrogens_generated_bond_parentDemand
    (mol : RawMolecule) {bond : RawBond}
    (member : bond ∈ mol.withExplicitHydrogens.bonds) (absent : bond ∉ mol.bonds) :
    0 < mol.hydrogenCountAt bond.source := by
  have memberFold : bond ∈ (expansionResult mol).toRawMolecule.bonds := by
    rwa [withExplicitHydrogens_bonds_eq_fold] at member
  exact (reviewedBondTransport mol).generatedParentDemand bond memberFold absent

theorem initialHydrogenExpansionState_wellFormed
    (mol : RawMolecule) (well : mol.WellFormed) :
    (initialHydrogenExpansionState mol).toRawMolecule.WellFormed := by
  intro bond member
  simpa [BondEndpointsOK] using well bond member

/-- The committed materialized-valence invariant holds for the actual expansion fold, under the
explicit domain `mol.WellFormed`. -/
theorem expansionFold_materializedValenceInvariant
    (mol : RawMolecule) (well : mol.WellFormed) :
    (expansionResult mol).MaterializedValenceInvariant mol :=
  fold_withExplicitHydrogensStep_preserves_materializedValenceInvariant mol
    (List.range mol.atomCount) (initialHydrogenExpansionState mol)
    (by intro index member; exact List.mem_range.mp member)
    (initialHydrogenExpansionState_shapeInvariant mol)
    (initialHydrogenExpansionState_wellFormed mol well)
    (initialHydrogenExpansionState_materializedValenceInvariant mol)

/-- **New clause.** Under the explicit domain `mol.WellFormed`, the target of every non-source
returned bond is a real hydrogen atom (`AtomSpec.aliphatic Element.H`) carrying exactly one incident
bond in the returned molecule. -/
theorem withExplicitHydrogens_generated_bond_target
    (mol : RawMolecule) (well : mol.WellFormed) {bond : RawBond}
    (member : bond ∈ mol.withExplicitHydrogens.bonds) (absent : bond ∉ mol.bonds) :
    mol.withExplicitHydrogens.atomAt? bond.target = some (AtomSpec.aliphatic Element.H) ∧
      mol.withExplicitHydrogens.incidentBondOrderSum bond.target = 1 := by
  obtain ⟨_sourceBound, targetLower, targetUpper, _kindEq⟩ :=
    withExplicitHydrogens_generated_bond_shape mol member absent
  have invariant := expansionFold_materializedValenceInvariant mol well
  have targetBoundFold : bond.target < (expansionResult mol).toRawMolecule.atomCount := by
    rw [← withExplicitHydrogens_atomCount_eq]
    exact targetUpper
  obtain ⟨atom, lookup⟩ :=
    listGet?_exists_of_lt (expansionResult mol).toRawMolecule.atoms bond.target targetBoundFold
  have lookupAt : (expansionResult mol).toRawMolecule.atomAt? bond.target = some atom := by
    simpa [atomAt?] using lookup
  obtain ⟨atomIdentity, incident⟩ := invariant.freshAtom bond.target atom targetLower lookupAt
  refine ⟨?_, ?_⟩
  · rw [withExplicitHydrogens_atomAt?_eq, lookupAt, atomIdentity]
  · rw [withExplicitHydrogens_incidentBondOrderSum_eq, incident]

/-- The complete reviewed closure of the transport gap: every non-source returned bond is a single
bond from a real, hydrogen-demanding parent index to a freshly appended hydrogen that is in range,
lies strictly above the parent, is a real hydrogen atom, and has valence exactly one. -/
theorem withExplicitHydrogens_generated_bond_closure
    (mol : RawMolecule) (well : mol.WellFormed) {bond : RawBond}
    (member : bond ∈ mol.withExplicitHydrogens.bonds) (absent : bond ∉ mol.bonds) :
    bond.source < mol.atomCount ∧
      0 < mol.hydrogenCountAt bond.source ∧
      mol.atomCount ≤ bond.target ∧
      bond.target < mol.withExplicitHydrogens.atomCount ∧
      bond.source < bond.target ∧
      bond.kind = ParsedBondKind.single ∧
      mol.withExplicitHydrogens.atomAt? bond.target = some (AtomSpec.aliphatic Element.H) ∧
      mol.withExplicitHydrogens.incidentBondOrderSum bond.target = 1 := by
  obtain ⟨sourceBound, targetLower, targetUpper, kindEq⟩ :=
    withExplicitHydrogens_generated_bond_shape mol member absent
  obtain ⟨hAtom, hValence⟩ :=
    withExplicitHydrogens_generated_bond_target mol well member absent
  exact ⟨sourceBound,
    withExplicitHydrogens_generated_bond_parentDemand mol member absent,
    targetLower, targetUpper, lt_of_lt_of_le sourceBound targetLower, kindEq, hAtom, hValence⟩

/-! ## Positive-demand source

A two-atom unbracketed carbon skeleton (`C–F`) with strictly positive implied hydrogen demand at the
carbon. The fixture exercises the transformation on a genuine input; it asserts no chemical or
descriptor outcome. -/

def substitutedCarbonSource : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.F]
    bonds := [⟨0, 1, ParsedBondKind.single⟩]
    neighborOrder := [[1], [0]] }

theorem substitutedCarbonSource_hydrogenCountAt_zero :
    substitutedCarbonSource.hydrogenCountAt 0 = 3 := by decide

theorem substitutedCarbonSource_positiveDemand :
    0 < substitutedCarbonSource.hydrogenCountAt 0 := by
  rw [substitutedCarbonSource_hydrogenCountAt_zero]
  decide

theorem substitutedCarbonSource_admissible : substitutedCarbonSource.Admissible :=
  (admissible?_eq_true_iff substitutedCarbonSource).mp (by decide)

theorem substitutedCarbonSource_wellFormed : substitutedCarbonSource.WellFormed :=
  substitutedCarbonSource_admissible.1

/-- The actual expanded bond list: the three generated hydrogen bonds come first (the materializer
splices them before the parent's first outgoing bond), followed by the retained source bond. -/
theorem substitutedCarbonSource_expandedBonds :
    substitutedCarbonSource.withExplicitHydrogens.bonds =
      [⟨0, 2, ParsedBondKind.single⟩, ⟨0, 3, ParsedBondKind.single⟩,
       ⟨0, 4, ParsedBondKind.single⟩, ⟨0, 1, ParsedBondKind.single⟩] := by decide

theorem substitutedCarbonSource_generatedBond_mem :
    (⟨0, 2, ParsedBondKind.single⟩ : RawBond) ∈
      substitutedCarbonSource.withExplicitHydrogens.bonds := by
  rw [substitutedCarbonSource_expandedBonds]
  decide

theorem substitutedCarbonSource_generatedBond_absent :
    (⟨0, 2, ParsedBondKind.single⟩ : RawBond) ∉ substitutedCarbonSource.bonds := by decide

theorem substitutedCarbonSource_generatedBond_source :
    (⟨0, 2, ParsedBondKind.single⟩ : RawBond).source = 0 := rfl

/-- Non-vacuous instantiation of the new positive-demand clause on the real fixture. -/
theorem substitutedCarbonSource_generatedBond_demand :
    0 < substitutedCarbonSource.hydrogenCountAt
      (⟨0, 2, ParsedBondKind.single⟩ : RawBond).source :=
  withExplicitHydrogens_generated_bond_parentDemand substitutedCarbonSource
    substitutedCarbonSource_generatedBond_mem substitutedCarbonSource_generatedBond_absent

/-- Non-vacuous instantiation of the new target-is-hydrogen clause on the real fixture. -/
theorem substitutedCarbonSource_generatedBond_target :
    substitutedCarbonSource.withExplicitHydrogens.atomAt?
        (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target = some (AtomSpec.aliphatic Element.H) ∧
      substitutedCarbonSource.withExplicitHydrogens.incidentBondOrderSum
        (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target = 1 :=
  withExplicitHydrogens_generated_bond_target substitutedCarbonSource
    substitutedCarbonSource_wellFormed substitutedCarbonSource_generatedBond_mem
    substitutedCarbonSource_generatedBond_absent

/-- Non-vacuous instantiation of the full closure on the real fixture. -/
theorem substitutedCarbonSource_closure :
    (⟨0, 2, ParsedBondKind.single⟩ : RawBond).source < substitutedCarbonSource.atomCount ∧
      0 < substitutedCarbonSource.hydrogenCountAt
        (⟨0, 2, ParsedBondKind.single⟩ : RawBond).source ∧
      substitutedCarbonSource.atomCount ≤
        (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target ∧
      (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target <
        substitutedCarbonSource.withExplicitHydrogens.atomCount ∧
      (⟨0, 2, ParsedBondKind.single⟩ : RawBond).source <
        (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target ∧
      (⟨0, 2, ParsedBondKind.single⟩ : RawBond).kind = ParsedBondKind.single ∧
      substitutedCarbonSource.withExplicitHydrogens.atomAt?
        (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target = some (AtomSpec.aliphatic Element.H) ∧
      substitutedCarbonSource.withExplicitHydrogens.incidentBondOrderSum
        (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target = 1 :=
  withExplicitHydrogens_generated_bond_closure substitutedCarbonSource
    substitutedCarbonSource_wellFormed substitutedCarbonSource_generatedBond_mem
    substitutedCarbonSource_generatedBond_absent

/-- Retention plus positive-demand/shape for every non-source bond, on the real fixture. -/
theorem substitutedCarbonSource_transport :
    (∀ bond, bond ∈ substitutedCarbonSource.bonds →
        bond ∈ substitutedCarbonSource.withExplicitHydrogens.bonds) ∧
      (∀ bond, bond ∈ substitutedCarbonSource.withExplicitHydrogens.bonds →
        bond ∉ substitutedCarbonSource.bonds →
          0 < substitutedCarbonSource.hydrogenCountAt bond.source ∧
            bond.source < bond.target ∧
            bond.kind = ParsedBondKind.single) := by
  refine ⟨withExplicitHydrogens_retains_original_bonds substitutedCarbonSource, ?_⟩
  intro bond member absent
  obtain ⟨_sourceBound, demand, _targetLower, _targetUpper, sourceLt, kindEq, _hAtom, _hValence⟩ :=
    withExplicitHydrogens_generated_bond_closure substitutedCarbonSource
      substitutedCarbonSource_wellFormed member absent
  exact ⟨demand, sourceLt, kindEq⟩

end TetraStereo.UniversalProof.ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure
