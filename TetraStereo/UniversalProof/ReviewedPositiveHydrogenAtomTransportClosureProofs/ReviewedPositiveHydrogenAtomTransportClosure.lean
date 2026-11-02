import TetraStereo.OneCenter.ExplicitHydrogens
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization
import TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ReviewedPositiveHydrogenAtomTransportClosureProofs.ReviewedPositiveHydrogenAtomTransportClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
























































/-! ## Arithmetic of the committed block base -/

/-- One more processed prefix index adds exactly the next atom's computed hydrogen demand to the
mapped range sum. -/
theorem range_map_sum_succ (h : ℕ → ℕ) (k : ℕ) :
    ((List.range (k + 1)).map h).sum = ((List.range k).map h).sum + h k := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem hydrogenExpansionBase_zero (mol : RawMolecule) :
    hydrogenExpansionBase mol 0 = mol.atomCount := by
  unfold hydrogenExpansionBase
  simp

theorem hydrogenExpansionBase_succ (mol : RawMolecule) (parent : ℕ) :
    hydrogenExpansionBase mol (parent + 1) =
      hydrogenExpansionBase mol parent + mol.hydrogenCountAt parent := by
  unfold hydrogenExpansionBase
  rw [range_map_sum_succ]
  omega

/-- The committed block base is monotone in the parent index, so blocks are laid down in order. -/
theorem hydrogenExpansionBase_mono (mol : RawMolecule) (a b : ℕ) (bound : a ≤ b) :
    hydrogenExpansionBase mol a ≤ hydrogenExpansionBase mol b := by
  obtain ⟨d, rfl⟩ := Nat.le.dest bound
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, hydrogenExpansionBase_succ]
      exact le_trans (ih (Nat.le_add_right a d)) (Nat.le_add_right _ _)

/-- The actual expanded atom count is the base of the whole block. -/
theorem withExplicitHydrogens_atomCount_eq_base (mol : RawMolecule) :
    mol.withExplicitHydrogens.atomCount = hydrogenExpansionBase mol mol.atomCount := by
  unfold hydrogenExpansionBase
  exact withExplicitHydrogens_atomCount_eq mol

/-! ## Block index bounds, membership and coverage -/

theorem materializedHydrogenId_lower (mol : RawMolecule) (parent offset : ℕ) :
    mol.atomCount ≤ hydrogenExpansionBase mol parent + offset :=
  le_trans (hydrogenExpansionBase_original_count_le mol parent) (Nat.le_add_right _ _)

/-- Every block index a parent actually demands lies inside the real expanded atom range. -/
theorem materializedHydrogenId_lt_expanded (mol : RawMolecule) (parent offset : ℕ)
    (parentBound : parent < mol.atomCount) (offsetBound : offset < mol.hydrogenCountAt parent) :
    hydrogenExpansionBase mol parent + offset < mol.withExplicitHydrogens.atomCount := by
  rw [withExplicitHydrogens_atomCount_eq_base]
  have stepLe := hydrogenExpansionBase_mono mol (parent + 1) mol.atomCount (by omega)
  rw [hydrogenExpansionBase_succ] at stepLe
  omega

/-- Membership in a parent's block, resolved to the running-prefix offset. -/
theorem mem_materializedHydrogenIds_iff (mol : RawMolecule) (parent index : ℕ) :
    index ∈ materializedHydrogenIds mol parent ↔
      ∃ offset, offset < mol.hydrogenCountAt parent ∧
        hydrogenExpansionBase mol parent + offset = index := by
  unfold materializedHydrogenIds
  rw [List.mem_map]
  constructor
  · rintro ⟨offset, offsetMem, equal⟩
    exact ⟨offset, List.mem_range.mp offsetMem, equal⟩
  · rintro ⟨offset, offsetBound, equal⟩
    exact ⟨offset, List.mem_range.mpr offsetBound, equal⟩

/-- The ascending range fold covers every appended index: the consecutive blocks of the processed
prefix have no gap. -/
theorem blockCoverage (mol : RawMolecule) :
    ∀ k index, mol.atomCount ≤ index → index < hydrogenExpansionBase mol k →
      ∃ parent, parent < k ∧ hydrogenExpansionBase mol parent ≤ index ∧
        index < hydrogenExpansionBase mol parent + mol.hydrogenCountAt parent := by
  intro k
  induction k with
  | zero =>
      intro index lower upper
      rw [hydrogenExpansionBase_zero] at upper
      omega
  | succ k inductionHypothesis =>
      intro index lower upper
      rw [hydrogenExpansionBase_succ] at upper
      by_cases inOld : index < hydrogenExpansionBase mol k
      · obtain ⟨parent, parentBound, lowerBase, upperBase⟩ :=
          inductionHypothesis index lower inOld
        exact ⟨parent, by omega, lowerBase, upperBase⟩
      · exact ⟨k, by omega, Nat.le_of_not_gt inOld, upper⟩

/-- Atom-side coverage: every appended index belongs to some demanding parent's block. -/
theorem materializedHydrogenId_covered (mol : RawMolecule) (index : ℕ)
    (lower : mol.atomCount ≤ index)
    (upper : index < mol.withExplicitHydrogens.atomCount) :
    ∃ parent, parent < mol.atomCount ∧ index ∈ materializedHydrogenIds mol parent := by
  rw [withExplicitHydrogens_atomCount_eq_base] at upper
  obtain ⟨parent, parentBound, lowerBase, upperBase⟩ :=
    blockCoverage mol mol.atomCount index lower upper
  exact ⟨parent, parentBound, (mem_materializedHydrogenIds_iff mol parent index).mpr
    ⟨index - hydrogenExpansionBase mol parent, by omega, by omega⟩⟩

/-- Consecutive blocks are disjoint, so an appended index has a unique demanding parent. -/
theorem materializedHydrogenId_parent_unique (mol : RawMolecule) (index parent₁ parent₂ : ℕ)
    (member₁ : index ∈ materializedHydrogenIds mol parent₁)
    (member₂ : index ∈ materializedHydrogenIds mol parent₂) :
    parent₁ = parent₂ := by
  obtain ⟨offset₁, offsetBound₁, equal₁⟩ :=
    (mem_materializedHydrogenIds_iff mol parent₁ index).mp member₁
  obtain ⟨offset₂, offsetBound₂, equal₂⟩ :=
    (mem_materializedHydrogenIds_iff mol parent₂ index).mp member₂
  rcases le_total parent₁ parent₂ with hle | hge
  · rcases lt_or_eq_of_le hle with hlt | heq
    · have stepLe := hydrogenExpansionBase_mono mol (parent₁ + 1) parent₂ (by omega)
      have upper₁ : index < hydrogenExpansionBase mol (parent₁ + 1) := by
        rw [hydrogenExpansionBase_succ]; omega
      have lower₂ : hydrogenExpansionBase mol parent₂ ≤ index := by omega
      omega
    · exact heq
  · rcases lt_or_eq_of_le hge with hlt | heq
    · have stepLe := hydrogenExpansionBase_mono mol (parent₂ + 1) parent₁ (by omega)
      have upper₂ : index < hydrogenExpansionBase mol (parent₂ + 1) := by
        rw [hydrogenExpansionBase_succ]; omega
      have lower₁ : hydrogenExpansionBase mol parent₁ ≤ index := by omega
      omega
    · exact heq.symm

/-- The appended atoms form exactly the disjoint union of one consecutive block per demanding
parent: every appended index lies in a unique parent's block. -/
theorem materializedHydrogen_partition (mol : RawMolecule) (index : ℕ)
    (lower : mol.atomCount ≤ index)
    (upper : index < mol.withExplicitHydrogens.atomCount) :
    ∃! parent, parent < mol.atomCount ∧ index ∈ materializedHydrogenIds mol parent := by
  obtain ⟨parent, parentBound, member⟩ := materializedHydrogenId_covered mol index lower upper
  refine ⟨parent, ⟨parentBound, member⟩, ?_⟩
  intro other hother
  exact materializedHydrogenId_parent_unique mol index other parent hother.2 member

/-! ## Atom identity, valence and the parent bond of each materialized hydrogen -/

theorem withExplicitHydrogens_materializedHydrogen_isHydrogen (mol : RawMolecule)
    (well : mol.WellFormed) (parent offset : ℕ) (parentBound : parent < mol.atomCount)
    (offsetBound : offset < mol.hydrogenCountAt parent) :
    mol.withExplicitHydrogens.atomAt? (hydrogenExpansionBase mol parent + offset) =
      some (AtomSpec.aliphatic Element.H) := by
  have lower := materializedHydrogenId_lower mol parent offset
  have upper := materializedHydrogenId_lt_expanded mol parent offset parentBound offsetBound
  obtain ⟨atom, lookup⟩ := listGet?_exists_of_lt mol.withExplicitHydrogens.atoms
    (hydrogenExpansionBase mol parent + offset) upper
  have lookupAt : mol.withExplicitHydrogens.atomAt?
      (hydrogenExpansionBase mol parent + offset) = some atom := by
    simpa [atomAt?] using lookup
  have fresh := withExplicitHydrogens_freshAtom mol well
    (hydrogenExpansionBase mol parent + offset) atom lower lookupAt
  rw [← fresh.1]
  exact lookupAt

theorem withExplicitHydrogens_materializedHydrogen_incidentOrder_one (mol : RawMolecule)
    (well : mol.WellFormed) (parent offset : ℕ) (parentBound : parent < mol.atomCount)
    (offsetBound : offset < mol.hydrogenCountAt parent) :
    mol.withExplicitHydrogens.incidentBondOrderSum
      (hydrogenExpansionBase mol parent + offset) = 1 := by
  have lower := materializedHydrogenId_lower mol parent offset
  have upper := materializedHydrogenId_lt_expanded mol parent offset parentBound offsetBound
  obtain ⟨atom, lookup⟩ := listGet?_exists_of_lt mol.withExplicitHydrogens.atoms
    (hydrogenExpansionBase mol parent + offset) upper
  have lookupAt : mol.withExplicitHydrogens.atomAt?
      (hydrogenExpansionBase mol parent + offset) = some atom := by
    simpa [atomAt?] using lookup
  exact (withExplicitHydrogens_freshAtom mol well
    (hydrogenExpansionBase mol parent + offset) atom lower lookupAt).2

/-- Each materialized hydrogen is bonded to its demanding parent with bond order exactly one: the
created single bond is the unique connecting record and uniqueness makes the matrix entry its kind. -/
theorem withExplicitHydrogens_materializedHydrogen_bondOrder_eq_one (mol : RawMolecule)
    (admitted : mol.StereochemicalAdmissible) (parent offset : ℕ)
    (parentBound : parent < mol.atomCount) (offsetBound : offset < mol.hydrogenCountAt parent) :
    mol.withExplicitHydrogens.bondOrder parent (hydrogenExpansionBase mol parent + offset) = 1 := by
  have member := withExplicitHydrogens_createdBond_mem mol parent offset parentBound offsetBound
  have expansionAdmissible := mol.withExplicitHydrogens_preserves_admissible admitted
  have connects :
      ({ source := parent, target := hydrogenExpansionBase mol parent + offset,
         kind := ParsedBondKind.single } : RawBond).connects parent
        (hydrogenExpansionBase mol parent + offset) = true := by
    simp [RawBond.connects]
  have exactOrder := mol.withExplicitHydrogens.bondOrder_eq_kind_of_mem_connects
    expansionAdmissible.1 expansionAdmissible.2 member connects
  rw [exactOrder]
  rfl

/-- Complete reviewed closure of the hydrogen-atom provenance obligation on an admissible source:
partition, hydrogen identity, incident order one, and exact parent bond order one. -/
theorem materializedHydrogen_provenance (mol : RawMolecule) (admitted : mol.StereochemicalAdmissible) :
    (∀ index, mol.atomCount ≤ index → index < mol.withExplicitHydrogens.atomCount →
        ∃! parent, parent < mol.atomCount ∧ index ∈ materializedHydrogenIds mol parent) ∧
      (∀ parent offset, parent < mol.atomCount → offset < mol.hydrogenCountAt parent →
        mol.withExplicitHydrogens.atomAt? (hydrogenExpansionBase mol parent + offset) =
            some (AtomSpec.aliphatic Element.H) ∧
          mol.withExplicitHydrogens.incidentBondOrderSum
              (hydrogenExpansionBase mol parent + offset) = 1 ∧
          mol.withExplicitHydrogens.bondOrder parent
              (hydrogenExpansionBase mol parent + offset) = 1) := by
  refine ⟨fun index lower upper => materializedHydrogen_partition mol index lower upper, ?_⟩
  intro parent offset parentBound offsetBound
  exact ⟨withExplicitHydrogens_materializedHydrogen_isHydrogen mol admitted.1.1 parent offset
          parentBound offsetBound,
    withExplicitHydrogens_materializedHydrogen_incidentOrder_one mol admitted.1.1 parent offset
      parentBound offsetBound,
    withExplicitHydrogens_materializedHydrogen_bondOrder_eq_one mol admitted parent offset
      parentBound offsetBound⟩

/-! ## Nonvacuity on the two production demand surfaces

Both witnesses are the archived original's closed records: one carries a written inline count, the
other is filled from the default-valence table. They are transformation nonvacuity only. -/

theorem unbracketedCarbon_stereochemicalAdmissible :
    unbracketedCarbon.StereochemicalAdmissible := by
  refine ⟨⟨unbracketedCarbon_wellFormed, ?_⟩, ?_⟩
  · unfold BondRecordsUnique
    decide
  · unfold WrittenNeighborExact
    decide

/-- The default-valence carbon's four materialized hydrogens form the consecutive block `1..4`. -/
theorem unbracketedCarbon_blocks :
    materializedHydrogenIds unbracketedCarbon 0 = [1, 2, 3, 4] := by
  decide

/-- The materialized hydrogen at index one is a single-bonded hydrogen of the source carbon. -/
theorem unbracketedCarbon_materializedHydrogen_bondOrder_one :
    unbracketedCarbon.withExplicitHydrogens.bondOrder 0 1 = 1 := by
  have provenance := (materializedHydrogen_provenance unbracketedCarbon
    unbracketedCarbon_stereochemicalAdmissible).2 0 0
      (by rw [unbracketedCarbon_atomCount]; omega)
      (by rw [unbracketedCarbon_hydrogenCountAt]; omega)
  have baseZero : hydrogenExpansionBase unbracketedCarbon 0 = 1 := by
    rw [hydrogenExpansionBase_zero, unbracketedCarbon_atomCount]
  rw [baseZero, Nat.add_zero] at provenance
  exact provenance.2.2

theorem bracketCarbonHalide_stereochemicalAdmissible :
    bracketCarbonHalide.StereochemicalAdmissible :=
  ⟨⟨bracketCarbonHalide_wellFormed, by unfold BondRecordsUnique; decide⟩,
    bracketCarbonHalide_writtenNeighborExact⟩

/-- The `[C@@H]`-centre's single materialized hydrogen sits at index four and is single-bonded to
the carbon centre. -/
theorem bracketCarbonHalide_materializedHydrogen_bondOrder_one :
    bracketCarbonHalide.withExplicitHydrogens.bondOrder 0 4 = 1 := by
  have provenance := (materializedHydrogen_provenance bracketCarbonHalide
    bracketCarbonHalide_stereochemicalAdmissible).2 0 0
      (by rw [bracketCarbonHalide_atomCount]; omega)
      (by rw [bracketCarbonHalide_centerHydrogens]; omega)
  have baseZero : hydrogenExpansionBase bracketCarbonHalide 0 = 4 := by
    rw [hydrogenExpansionBase_zero, bracketCarbonHalide_atomCount]
  rw [baseZero, Nat.add_zero] at provenance
  exact provenance.2.2

end TetraStereo.UniversalProof.ReviewedPositiveHydrogenAtomTransportClosureProofs.ReviewedPositiveHydrogenAtomTransportClosure
