import TetraStereo.OneCenter.ExplicitHydrogens

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

/-!
# Structural hydrogen-expansion identity and exact written-order provenance

Zero hydrogen demand does not make the raw records identical: production replaces every inline
hydrogen field by `some 0` and materializes a total written-neighbor table. The general theorem
below identifies all four actual returned fields under zero demand and exact written neighbors.
Full record identity additionally requires already normalized inline fields and a total stored
table. These are independent input-record conditions, with no expected descriptor, output,
source state, successful compiler, sort or expansion equation supplied by the caller.

TECHNICAL_PROOF_REQUIRED: runtime/source cursor transport when positive hydrogen demand changes
the graph; public runtime/parser output refinement; broader mixed and five-family integration.
HUMAN_REVIEW_REQUIRED: chemical and annotation conventions. No scientific approval is asserted.
-/

/-- The actual materializer requests no new hydrogen at any actual input index. -/
def ZeroHydrogenDemand (molecule : RawMolecule) : Prop :=
  ∀ index, index < molecule.atomCount → molecule.hydrogenCountAt index = 0

/-- All inline count records are already in the materializer's consumed-count format. -/
def InlineCountsNormalized (molecule : RawMolecule) : Prop :=
  ∀ atom ∈ molecule.atoms, atom.explicitHydrogens? = some 0

/-- Independent structural conditions for exact raw-record identity. -/
structure StructurallyExpansionFixed (molecule : RawMolecule) : Prop where
  inlineCounts : InlineCountsNormalized molecule
  writtenExact : molecule.WrittenNeighborExact
  totalWrittenTable : molecule.neighborOrder.length = molecule.atomCount

/-- Explicit record normalization performed before any positive-demand step. -/
def materializedWrittenRecord (molecule : RawMolecule) : RawMolecule :=
  { atoms := molecule.atoms.map materializedAtomSpec
    bonds := molecule.bonds
    neighborOrder := (List.range molecule.atomCount).map molecule.writtenNeighbors
    introductionPredecessors := molecule.introductionPredecessors }

theorem normalized_inline_counts_zero_demand (molecule : RawMolecule)
    (normalized : InlineCountsNormalized molecule) : ZeroHydrogenDemand molecule := by
  intro index _bound
  cases observed : molecule.atomAt? index with
  | none => simp [hydrogenCountAt, observed]
  | some atom =>
      have member : atom ∈ molecule.atoms :=
        listGet?_eq_some_implies_mem molecule.atoms index atom observed
      simp [hydrogenCountAt, observed, normalized atom member]

theorem zero_demand_step_identity (molecule : RawMolecule) (state : HydrogenExpansionState)
    (index : Nat) (zero : molecule.hydrogenCountAt index = 0) :
    withExplicitHydrogensStep molecule state index = state := by
  simp [withExplicitHydrogensStep, zero]

theorem zero_demand_fold_identity (molecule : RawMolecule) (indices : List Nat)
    (state : HydrogenExpansionState)
    (zero : ∀ index ∈ indices, molecule.hydrogenCountAt index = 0) :
    indices.foldl (withExplicitHydrogensStep molecule) state = state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      rw [List.foldl_cons, zero_demand_step_identity molecule state index
        (zero index (by simp))]
      exact inductionHypothesis state (by
        intro next member
        exact zero next (List.mem_cons_of_mem index member))

theorem materialized_record_atom_count (molecule : RawMolecule) :
    (materializedWrittenRecord molecule).atomCount = molecule.atomCount := by
  simp [materializedWrittenRecord, atomCount]

theorem materialized_record_bond_order (molecule : RawMolecule) (left right : Nat) :
    (materializedWrittenRecord molecule).bondOrder left right =
      molecule.bondOrder left right := rfl

theorem materialized_record_written_order (molecule : RawMolecule) (index : Nat)
    (bound : index < molecule.atomCount) :
    (materializedWrittenRecord molecule).writtenNeighbors index =
      molecule.writtenNeighbors index := by
  unfold materializedWrittenRecord writtenNeighbors
  rw [getElem?_map_range _ _ _ bound]

theorem materialized_record_written_exact (molecule : RawMolecule)
    (exact : molecule.WrittenNeighborExact) :
    (materializedWrittenRecord molecule).WrittenNeighborExact := by
  apply WrittenNeighborExact.of_at
  intro center
  have bound : center.val < molecule.atomCount := by
    simpa only [materialized_record_atom_count] using center.isLt
  have clauses := WrittenNeighborExact.at molecule exact ⟨center.val, bound⟩
  rw [materialized_record_written_order molecule center.val bound]
  refine ⟨clauses.1, ?_, ?_⟩
  · intro ligand member
    simpa only [materialized_record_atom_count] using clauses.2.1 ligand member
  · intro ligand
    have ligandBound : ligand.val < molecule.atomCount := by
      simpa only [materialized_record_atom_count] using ligand.isLt
    exact clauses.2.2 ⟨ligand.val, ligandBound⟩

theorem materialized_record_exact_table_identity (molecule : RawMolecule)
    (exact : molecule.WrittenNeighborExact) :
    (materializedWrittenRecord molecule).withExactWrittenNeighbors =
      materializedWrittenRecord molecule := by
  have recordExact := materialized_record_written_exact molecule exact
  have table :
      (List.range (materializedWrittenRecord molecule).atomCount).map
          (materializedWrittenRecord molecule).exactWrittenNeighbors =
        (List.range molecule.atomCount).map molecule.writtenNeighbors := by
    rw [materialized_record_atom_count]
    apply List.map_congr_left
    intro index member
    have bound := List.mem_range.mp member
    rw [exactWrittenNeighbors_eq_of_exact _ recordExact
      ⟨index, by simpa only [materialized_record_atom_count] using bound⟩,
      materialized_record_written_order molecule index bound]
  change ({ atoms := molecule.atoms.map materializedAtomSpec, bonds := molecule.bonds, neighborOrder := (List.range (materializedWrittenRecord molecule).atomCount).map (materializedWrittenRecord molecule).exactWrittenNeighbors, introductionPredecessors := molecule.introductionPredecessors } : RawMolecule) = _
  rw [table]
  rfl

/-- Exact whole-record description; zero demand alone never supplies raw-record identity. -/
theorem zero_demand_expansion_exact_record (molecule : RawMolecule)
    (zero : ZeroHydrogenDemand molecule) (exact : molecule.WrittenNeighborExact) :
    molecule.withExplicitHydrogens = materializedWrittenRecord molecule := by
  unfold withExplicitHydrogens
  rw [zero_demand_fold_identity molecule (List.range molecule.atomCount)
    (initialHydrogenExpansionState molecule) (by
      intro index member
      exact zero index (List.mem_range.mp member))]
  change (materializedWrittenRecord molecule).withExactWrittenNeighbors = _
  exact materialized_record_exact_table_identity molecule exact

theorem zero_demand_expansion_atoms (molecule : RawMolecule)
    (zero : ZeroHydrogenDemand molecule) (exact : molecule.WrittenNeighborExact) :
    molecule.withExplicitHydrogens.atoms = molecule.atoms.map materializedAtomSpec := by
  rw [zero_demand_expansion_exact_record molecule zero exact]
  rfl

theorem zero_demand_expansion_bonds (molecule : RawMolecule)
    (zero : ZeroHydrogenDemand molecule) (exact : molecule.WrittenNeighborExact) :
    molecule.withExplicitHydrogens.bonds = molecule.bonds := by
  rw [zero_demand_expansion_exact_record molecule zero exact]
  rfl

theorem zero_demand_expansion_written_order (molecule : RawMolecule)
    (zero : ZeroHydrogenDemand molecule) (exact : molecule.WrittenNeighborExact)
    (index : Nat) (bound : index < molecule.atomCount) :
    molecule.withExplicitHydrogens.writtenNeighbors index = molecule.writtenNeighbors index := by
  rw [zero_demand_expansion_exact_record molecule zero exact]
  exact materialized_record_written_order molecule index bound

theorem zero_demand_expansion_atom_lookup (molecule : RawMolecule)
    (zero : ZeroHydrogenDemand molecule) (exact : molecule.WrittenNeighborExact) (index : Nat) :
    molecule.withExplicitHydrogens.atomAt? index =
      (molecule.atomAt? index).map materializedAtomSpec := by
  rw [zero_demand_expansion_exact_record molecule zero exact]
  exact listGet?_map materializedAtomSpec molecule.atoms index

theorem materialized_atom_identity (atom : AtomSpec)
    (normalized : atom.explicitHydrogens? = some 0) : materializedAtomSpec atom = atom := by
  cases atom
  simp_all [materializedAtomSpec]

theorem normalized_written_table (molecule : RawMolecule)
    (total : molecule.neighborOrder.length = molecule.atomCount) :
    (List.range molecule.atomCount).map molecule.writtenNeighbors = molecule.neighborOrder := by
  apply List.ext_getElem?
  intro index
  by_cases bound : index < molecule.atomCount
  · rw [getElem?_map_range _ _ _ bound]
    have tableBound : index < molecule.neighborOrder.length := by simpa [total] using bound
    simp only [writtenNeighbors, List.getElem?_eq_getElem tableBound]
  · have leftLength : ((List.range molecule.atomCount).map molecule.writtenNeighbors).length =
        molecule.atomCount := by simp
    rw [List.getElem?_eq_none (by simpa [leftLength] using Nat.le_of_not_gt bound),
      List.getElem?_eq_none (by simpa [total] using Nat.le_of_not_gt bound)]

/-- A general identity theorem for every raw molecule satisfying independent record conditions. -/
theorem structurally_fixed_expansion_identity (molecule : RawMolecule)
    (fixed : StructurallyExpansionFixed molecule) : molecule.withExplicitHydrogens = molecule := by
  rw [zero_demand_expansion_exact_record molecule
    (normalized_inline_counts_zero_demand molecule fixed.inlineCounts) fixed.writtenExact]
  have atoms : molecule.atoms.map materializedAtomSpec = molecule.atoms := by
    have equal : molecule.atoms.map materializedAtomSpec = molecule.atoms.map id := by
      apply List.map_congr_left
      intro atom member
      exact materialized_atom_identity atom (fixed.inlineCounts atom member)
    simpa using equal
  unfold materializedWrittenRecord
  rw [atoms, normalized_written_table molecule fixed.totalWrittenTable]

/-! Closed record fixtures inhabit the structural class for two distinct center elements.
Their purpose is transformation nonvacuity, not a chemical or stereochemical assignment claim. -/

def saturatedStar (centerElement : Element) : RawMolecule :=
  { atoms :=
      [{ AtomSpec.aliphatic centerElement with explicitHydrogens? := some 0, tetrahedral? := some .clockwise },
       { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 },
       { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 },
       { AtomSpec.aliphatic .Br with explicitHydrogens? := some 0 },
       { AtomSpec.aliphatic .I with explicitHydrogens? := some 0 }]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩]
    neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]] }

theorem saturated_star_structurally_fixed (element : Element) :
    StructurallyExpansionFixed (saturatedStar element) := by
  constructor
  · intro atom member
    simp only [saturatedStar, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
  · change (saturatedStar .C).writtenNeighborExact? = true
    decide +kernel
  · rfl

theorem carbon_star_expansion_identity :
    (saturatedStar .C).withExplicitHydrogens = saturatedStar .C :=
  structurally_fixed_expansion_identity _ (saturated_star_structurally_fixed .C)

theorem silicon_star_expansion_identity :
    (saturatedStar .Si).withExplicitHydrogens = saturatedStar .Si :=
  structurally_fixed_expansion_identity _ (saturated_star_structurally_fixed .Si)

end TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
