import TetraStereo.OneCenter.ExplicitHydrogens

set_option autoImplicit false

namespace TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule























































/-- Fresh hydrogen atom indices appended when one atom's implied hydrogens are materialized. -/
def freshHydrogenIds (base count : ℕ) : List ℕ :=
  (List.range count).map fun offset => base + offset

/-- The single bonds created for those fresh hydrogens: every one runs from the materialized parent
atom to exactly one appended hydrogen. -/
def freshHydrogenBonds (parent base count : ℕ) : List RawBond :=
  (freshHydrogenIds base count).map fun target =>
    { source := parent, target := target, kind := ParsedBondKind.single }

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

/-- A generated hydrogen bond is never a self-loop, provided the parent index lies below the fresh
block. This is the loop assumption made explicit. -/
theorem freshHydrogenBonds_no_loop (parent base count : ℕ) (parentLt : parent < base)
    {bond : RawBond} (member : bond ∈ freshHydrogenBonds parent base count) :
    bond.source ≠ bond.target := by
  obtain ⟨offset, _, rfl⟩ := (mem_freshHydrogenBonds_iff parent base count bond).mp member
  show parent ≠ base + offset
  omega

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

/-- Any bond of one step is either an existing accumulator bond or a generated hydrogen bond that
points from the materialized atom `index` into the fresh block. -/
theorem withExplicitHydrogensStep_returned_bond_shape
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ) {bond : RawBond}
    (member : bond ∈ (withExplicitHydrogensStep mol state index).toRawMolecule.bonds) :
    bond ∈ state.toRawMolecule.bonds ∨
      (bond.source = index ∧
        state.1.length ≤ bond.target ∧
        bond.target < state.1.length + mol.hydrogenCountAt index ∧
        bond.kind = ParsedBondKind.single) := by
  rcases (withExplicitHydrogensStep_bonds_mem_iff mol state index bond).mp member with old | fresh
  · exact Or.inl old
  · refine Or.inr ⟨freshHydrogenBonds_source _ _ _ fresh, ?_, ?_,
      freshHydrogenBonds_kind _ _ _ fresh⟩
    · exact (freshHydrogenBonds_target_bounds _ _ _ fresh).1
    · exact (freshHydrogenBonds_target_bounds _ _ _ fresh).2

/-- A generated hydrogen bond never duplicates an existing accumulator record, given that the
accumulator is well-formed. This is the duplicate assumption made explicit. -/
theorem withExplicitHydrogensStep_generated_not_original
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (well : state.toRawMolecule.WellFormed) {bond : RawBond}
    (member : bond ∈ freshHydrogenBonds index state.1.length (mol.hydrogenCountAt index)) :
    bond ∉ state.toRawMolecule.bonds := by
  intro old
  have targetLt : bond.target < state.1.length := (well bond old).2.1
  have targetLower := (freshHydrogenBonds_target_bounds _ _ _ member).1
  omega

/-- Endpoint validity of a generated bond inside the returned molecule: the parent index is a real
atom and the fresh target is a real (new) atom, with no self-loop. -/
theorem withExplicitHydrogensStep_generated_bond_endpoints_valid
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (indexBound : index < mol.atomCount) (shape : HydrogenExpansionState.ShapeInvariant mol state)
    {bond : RawBond}
    (member : bond ∈ (withExplicitHydrogensStep mol state index).toRawMolecule.bonds)
    (absent : bond ∉ state.toRawMolecule.bonds) :
    bond.source < (withExplicitHydrogensStep mol state index).toRawMolecule.atomCount ∧
      bond.target < (withExplicitHydrogensStep mol state index).toRawMolecule.atomCount ∧
      bond.source ≠ bond.target := by
  have fresh : bond ∈ freshHydrogenBonds index state.1.length (mol.hydrogenCountAt index) := by
    rcases (withExplicitHydrogensStep_bonds_mem_iff mol state index bond).mp member with old | fresh
    · exact absurd old absent
    · exact fresh
  have sourceEq := freshHydrogenBonds_source _ _ _ fresh
  have targetBounds := freshHydrogenBonds_target_bounds _ _ _ fresh
  have indexLtBase : index < state.1.length :=
    lt_of_lt_of_le indexBound shape.originalAtoms
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceEq, withExplicitHydrogensStep_atomCount]
    exact lt_of_lt_of_le indexLtBase (Nat.le_add_right _ _)
  · rw [withExplicitHydrogensStep_atomCount]
    exact targetBounds.2
  · rw [sourceEq]
    exact Nat.ne_of_lt (lt_of_lt_of_le indexLtBase targetBounds.1)

/-- Accumulator invariant for the full expansion fold.

`originalRetained` records that every source bond survives as the identical record.
`generatedShape` records that every non-source bond is a generated single bond from a real parent
index (`< mol.atomCount`) to an appended hydrogen (`mol.atomCount ≤ target`) that currently lies
inside the accumulator's atom block. Both clauses are about exact records, not up to isomorphism. -/
structure BondTransportInvariant (mol : RawMolecule) (state : HydrogenExpansionState) : Prop where
  originalRetained : ∀ bond, bond ∈ mol.bonds → bond ∈ state.toRawMolecule.bonds
  generatedShape : ∀ bond, bond ∈ state.toRawMolecule.bonds → bond ∉ mol.bonds →
    bond.source < mol.atomCount ∧ mol.atomCount ≤ bond.target ∧
      bond.target < state.toRawMolecule.atomCount ∧ bond.kind = ParsedBondKind.single

theorem initialHydrogenExpansionState_bondTransportInvariant (mol : RawMolecule) :
    BondTransportInvariant mol (initialHydrogenExpansionState mol) := by
  constructor
  · intro bond member
    simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule] using member
  · intro bond member absent
    exact absurd (by
      simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule] using member)
      absent

theorem withExplicitHydrogensStep_preserves_bondTransportInvariant
    (mol : RawMolecule) (state : HydrogenExpansionState) (index : ℕ)
    (indexBound : index < mol.atomCount)
    (shape : HydrogenExpansionState.ShapeInvariant mol state)
    (invariant : BondTransportInvariant mol state) :
    BondTransportInvariant mol (withExplicitHydrogensStep mol state index) := by
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

theorem fold_withExplicitHydrogensStep_preserves_bondTransportInvariant
    (mol : RawMolecule) (indices : List ℕ) (state : HydrogenExpansionState)
    (indicesBound : ∀ index ∈ indices, index < mol.atomCount)
    (shape : HydrogenExpansionState.ShapeInvariant mol state)
    (invariant : BondTransportInvariant mol state) :
    BondTransportInvariant mol (indices.foldl (withExplicitHydrogensStep mol) state) := by
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
        withExplicitHydrogensStep_preserves_bondTransportInvariant mol state index
          indexBound shape invariant
      exact inductionHypothesis (withExplicitHydrogensStep mol state index)
        restBound nextShape nextInvariant

/-- The actual production expansion retains every source bond and turns every other returned bond
into a single bond from a real parent atom to an appended hydrogen. -/
theorem withExplicitHydrogens_bondTransport (mol : RawMolecule) :
    (∀ bond, bond ∈ mol.bonds → bond ∈ mol.withExplicitHydrogens.bonds) ∧
      (∀ bond, bond ∈ mol.withExplicitHydrogens.bonds → bond ∉ mol.bonds →
        bond.source < mol.atomCount ∧ mol.atomCount ≤ bond.target ∧
          bond.target < mol.withExplicitHydrogens.atomCount ∧
          bond.source ≠ bond.target ∧ bond.kind = ParsedBondKind.single) := by
  have invariant :
      BondTransportInvariant mol
        ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
          (initialHydrogenExpansionState mol)) :=
    fold_withExplicitHydrogensStep_preserves_bondTransportInvariant mol
      (List.range mol.atomCount) (initialHydrogenExpansionState mol)
      (by intro index member; exact List.mem_range.mp member)
      (initialHydrogenExpansionState_shapeInvariant mol)
      (initialHydrogenExpansionState_bondTransportInvariant mol)
  have bondsEq : mol.withExplicitHydrogens.bonds =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.bonds := by
    unfold withExplicitHydrogens
    simp only [withExactWrittenNeighbors_bonds]
  have countEq : mol.withExplicitHydrogens.atomCount =
      ((List.range mol.atomCount).foldl (withExplicitHydrogensStep mol)
        (initialHydrogenExpansionState mol)).toRawMolecule.atomCount := by
    rfl
  constructor
  · intro bond source
    rw [bondsEq]
    exact invariant.originalRetained bond source
  · intro bond member absent
    rw [bondsEq] at member
    obtain ⟨sourceBound, targetLower, targetUpper, kindEq⟩ :=
      invariant.generatedShape bond member absent
    rw [countEq]
    exact ⟨sourceBound, targetLower, targetUpper,
      Nat.ne_of_lt (lt_of_lt_of_le sourceBound targetLower), kindEq⟩

theorem withExplicitHydrogens_retains_original_bonds (mol : RawMolecule) :
    ∀ bond, bond ∈ mol.bonds → bond ∈ mol.withExplicitHydrogens.bonds :=
  (withExplicitHydrogens_bondTransport mol).1

theorem withExplicitHydrogens_generated_bond_shape (mol : RawMolecule) {bond : RawBond}
    (member : bond ∈ mol.withExplicitHydrogens.bonds) (absent : bond ∉ mol.bonds) :
    bond.source < mol.atomCount ∧ mol.atomCount ≤ bond.target ∧
      bond.target < mol.withExplicitHydrogens.atomCount ∧
      bond.source ≠ bond.target ∧ bond.kind = ParsedBondKind.single :=
  (withExplicitHydrogens_bondTransport mol).2 bond member absent

/-! ## Positive-demand source

A two-atom unbracketed carbon skeleton with strictly positive implied hydrogen demand at the carbon.
The fixture exercises the transformation on a genuine input; it asserts no chemical or descriptor
outcome. -/

def substitutedCarbonSource : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.F]
    bonds := [⟨0, 1, ParsedBondKind.single⟩]
    neighborOrder := [[1], [0]] }

theorem substitutedCarbonSource_hydrogenCountAt_zero :
    substitutedCarbonSource.hydrogenCountAt 0 = 3 := by
  decide +kernel

theorem substitutedCarbonSource_positiveDemand :
    0 < substitutedCarbonSource.hydrogenCountAt 0 := by
  rw [substitutedCarbonSource_hydrogenCountAt_zero]
  omega

theorem substitutedCarbonSource_admissible : substitutedCarbonSource.Admissible :=
  (admissible?_eq_true_iff substitutedCarbonSource).mp (by decide +kernel)

theorem substitutedCarbonSource_originalBond :
    (⟨0, 1, ParsedBondKind.single⟩ : RawBond) ∈ substitutedCarbonSource.bonds := by
  simp [substitutedCarbonSource]

/-- The actual expanded bond list: the three generated hydrogen bonds come first (the materializer
splices them before the parent's first outgoing bond), followed by the retained source bond. -/
theorem substitutedCarbonSource_expandedBonds :
    substitutedCarbonSource.withExplicitHydrogens.bonds =
      [⟨0, 2, ParsedBondKind.single⟩, ⟨0, 3, ParsedBondKind.single⟩,
       ⟨0, 4, ParsedBondKind.single⟩, ⟨0, 1, ParsedBondKind.single⟩] := by
  decide +kernel

theorem substitutedCarbonSource_originalBond_retained :
    (⟨0, 1, ParsedBondKind.single⟩ : RawBond) ∈
      substitutedCarbonSource.withExplicitHydrogens.bonds :=
  withExplicitHydrogens_retains_original_bonds substitutedCarbonSource _
    substitutedCarbonSource_originalBond

theorem substitutedCarbonSource_generated_bond_points_to_parent :
    ∃ bond ∈ substitutedCarbonSource.withExplicitHydrogens.bonds,
      bond.source = 0 ∧ bond.target = 2 ∧ bond.kind = ParsedBondKind.single := by
  refine ⟨⟨0, 2, ParsedBondKind.single⟩, ?_, rfl, rfl, rfl⟩
  rw [substitutedCarbonSource_expandedBonds]
  decide +kernel

theorem substitutedCarbonSource_generated_bond_shape :
    (⟨0, 2, ParsedBondKind.single⟩ : RawBond).source < substitutedCarbonSource.atomCount ∧
      substitutedCarbonSource.atomCount ≤ (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target ∧
      (⟨0, 2, ParsedBondKind.single⟩ : RawBond).target <
        substitutedCarbonSource.withExplicitHydrogens.atomCount := by
  have member : (⟨0, 2, ParsedBondKind.single⟩ : RawBond) ∈
      substitutedCarbonSource.withExplicitHydrogens.bonds := by
    rw [substitutedCarbonSource_expandedBonds]
    decide +kernel
  have absent : (⟨0, 2, ParsedBondKind.single⟩ : RawBond) ∉ substitutedCarbonSource.bonds := by
    decide +kernel
  obtain ⟨sourceBound, targetLower, targetUpper, _, _⟩ :=
    withExplicitHydrogens_generated_bond_shape substitutedCarbonSource member absent
  exact ⟨sourceBound, targetLower, targetUpper⟩

theorem substitutedCarbonSource_transport :
    (∀ bond, bond ∈ substitutedCarbonSource.bonds →
        bond ∈ substitutedCarbonSource.withExplicitHydrogens.bonds) ∧
      (∀ bond, bond ∈ substitutedCarbonSource.withExplicitHydrogens.bonds →
        bond ∉ substitutedCarbonSource.bonds →
          bond.source < substitutedCarbonSource.atomCount ∧
            substitutedCarbonSource.atomCount ≤ bond.target ∧
            bond.target < substitutedCarbonSource.withExplicitHydrogens.atomCount ∧
            bond.source ≠ bond.target ∧ bond.kind = ParsedBondKind.single) :=
  withExplicitHydrogens_bondTransport substitutedCarbonSource

end TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport
