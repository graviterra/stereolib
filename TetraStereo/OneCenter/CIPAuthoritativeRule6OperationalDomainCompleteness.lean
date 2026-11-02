import TetraStereo.OneCenter.CIPAuthoritativeRule6SemanticUnresolvedIntegration

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPOccurrenceCompleteness
open AuthoritativeCIPOccurrenceCompleteness.DescriptorRule6HierarchySupport
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPRule6Completeness
open AuthoritativeCIPRule6P92Enumeration

/-!
# Structural and chemical closure of the source Rule-6 operational domain

The semantic refusal theorems deliberately exposed the exact operational facts they use.  This
module derives those facts from lower-level source structure, then discharges that source
structure from explicit finite-molecule chemical hypotheses.  Neither layer assumes that source
construction, sorting, adjacency traversal, or a promoted ranking has returned successfully.
-/

/-- Independent source structure sufficient for every resolved Rule-6 operational lookup.

* four materialized source ligand positions make sorted indices zero and one meaningful;
* the uncapped descriptor hierarchy makes promoted comparison total for any auxiliary state;
* recursive cursor support makes every promoted reference ranking executable.

These are lower-level graph and comparator facts, not adapter-output assumptions. -/
structure AuthoritativeSourceRule6StructuralOperationalSupport
    (mol : RawMolecule) (fuel center : Nat) : Prop where
  ligands_length_four : (mol.ligandsWithLonePair center).length = 4
  hierarchy : ∀ state : OccurrenceAuxState,
    DescriptorRule6HierarchySupport mol state fuel
  source_cursors_supported : ∀ cursor,
    cursor ∈ authoritativeSourceRule6LigandCursors mol center →
      CursorSupport mol fuel cursor

/-- A successful source sort is a permutation of four positions.  Consequently its first and
rank-one positions exist, the rank-one position names a source cursor, and structural comparator
support makes every promoted reference ranking total.  Adjacency success is not used to prove
these facts; it is retained only because the resolved operational domain is attached to a fully
constructed source frame. -/
theorem authoritativeSourceRule6ResolvedOperationalDomain_of_structuralSupport
    (mol : RawMolecule) (fuel center : Nat)
    (support : AuthoritativeSourceRule6StructuralOperationalSupport mol fuel center) :
    AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center := by
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  intro state sorted adjacent _stateEq sortedEq _adjacentEq
  have sortedPerm : sorted.Perm (List.range 4) :=
    sortAuthoritativeRule6InitialPositions?_perm
      mol state fuel roots (List.range 4) sorted sortedEq
  have sortedLength : sorted.length = 4 := by
    simpa using sortedPerm.length_eq
  have zeroBound : 0 < sorted.length := by omega
  let firstReference := sorted[0]
  have firstReferenceEq : sorted[0]? = some firstReference :=
    List.getElem?_eq_getElem zeroBound
  have oneBound : 1 < sorted.length := by omega
  let referencePosition := sorted[1]
  have referencePositionEq : sorted[1]? = some referencePosition :=
    List.getElem?_eq_getElem oneBound
  have referencePositionMember : referencePosition ∈ sorted :=
    List.getElem_mem oneBound
  have referencePositionLtFour : referencePosition < 4 :=
    List.mem_range.mp (sortedPerm.mem_iff.mp referencePositionMember)
  have rootsLength : roots.length = 4 := by
    simpa [roots] using
      (authoritativeSourceRule6LigandCursors_length mol center).trans
        support.ligands_length_four
  have referencePositionLtRoots : referencePosition < roots.length := by
    simpa [rootsLength] using referencePositionLtFour
  let referenceRoot := roots[referencePosition]
  have referenceRootEq : roots[sorted[1]?.getD 0]? = some referenceRoot := by
    simp [referencePositionEq, referenceRoot,
      List.getElem?_eq_getElem referencePositionLtRoots]
  have rankingTotal : ∀ reference,
      ∃ ranking,
        authoritativeOccurrenceRule6PositionRankingBackend
            mol state fuel roots ligands reference = some ranking :=
    authoritativeOccurrenceRule6PositionRankingBackend_total_of_support
      (support.hierarchy state) roots (by
        intro root member
        exact support.source_cursors_supported root (by simpa [roots] using member)) ligands
  exact ⟨⟨firstReference, firstReferenceEq⟩,
    ⟨referenceRoot, referenceRootEq⟩, rankingTotal⟩

/-- The genuinely chemical core needed for source Rule-6 operational totality.

Four-coordinate shape is intentionally absent: integrated unannotated applicability already
contains a connectivity frame, from which that local fact is recovered.  The depth inequality is
the exact finite-tree coverage needed by cursor support. -/
structure AuthoritativeSourceRule6ChemicalOperationalCore
    (mol : RawMolecule) (fuel center : Nat) : Prop where
  center_bound : center < mol.atomCount
  well_formed : mol.WellFormed
  unique_bonds : mol.BondRecordsUnique
  written_exact : mol.WrittenNeighborExact
  valence : mol.ValenceOK
  kekule : LocalizedMancudeKekuleAdmissible mol
  depth_covered : 2 * mol.atomCount + 1 ≤ fuel

/-- Explicit chemical hypotheses plus four materialized neighbours yield the lower-level source
support predicate. -/
def AuthoritativeSourceRule6ChemicalOperationalCore.structuralSupport
    {mol : RawMolecule} {fuel center : Nat}
    (chemical : AuthoritativeSourceRule6ChemicalOperationalCore mol fuel center)
    (writtenFour : (mol.writtenNeighbors center).length = 4) :
    AuthoritativeSourceRule6StructuralOperationalSupport mol fuel center := by
  have bonding : CanonicalCenterBondingNumberSix mol center :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center chemical.center_bound chemical.well_formed
        chemical.unique_bonds chemical.valence
  exact
    { ligands_length_four :=
        ligandsWithLonePair_length_eq_four_of_written mol center writtenFour
      hierarchy := fun state =>
        DescriptorRule6HierarchySupport.ofLocalizedMancudeKekuleAdmissible
          mol state fuel chemical.well_formed chemical.unique_bonds chemical.kekule
      source_cursors_supported :=
        authoritativeSourceRule6LigandCursor_supported
          chemical.center_bound chemical.well_formed chemical.written_exact bonding
            writtenFour chemical.depth_covered }

/-- Chemical structure and a four-neighbour source shape close the exposed operational domain,
without an auxiliary-state, sort, adjacency, or ranking success premise. -/
theorem authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalCore
    {mol : RawMolecule} {fuel center : Nat}
    (chemical : AuthoritativeSourceRule6ChemicalOperationalCore mol fuel center)
    (writtenFour : (mol.writtenNeighbors center).length = 4) :
    AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center :=
  authoritativeSourceRule6ResolvedOperationalDomain_of_structuralSupport
    mol fuel center (chemical.structuralSupport writtenFour)

/-- Connectivity-only tetrahedral applicability supplies the one local four-neighbour fact that
is deliberately not part of the molecule-wide chemical core. -/
theorem authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalCore_and_frame
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {fuel center : Nat}
    (chemical : AuthoritativeSourceRule6ChemicalOperationalCore mol fuel center)
    (frame : BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center) :
    AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center := by
  have writtenFour : (mol.writtenNeighbors center).length = 4 := by
    rcases frame with ⟨_spec, _atomEq, _element, _extended, four⟩
    exact four
  exact authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalCore
    chemical writtenFour

/-- At the production analysis fuel, the finite-depth premise is automatic.  This is the direct
raw-chemical entry point for the operational-domain theorem. -/
theorem authoritativeSourceRule6ResolvedOperationalDomain_at_analysisFuel
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {center : Nat}
    (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (writtenExact : mol.WrittenNeighborExact) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (frame : BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center) :
    AuthoritativeSourceRule6ResolvedOperationalDomain
      mol (analysisFuel mol) center := by
  let chemical : AuthoritativeSourceRule6ChemicalOperationalCore
      mol (analysisFuel mol) center :=
    { center_bound := centerBound
      well_formed := wellFormed
      unique_bonds := unique
      written_exact := writtenExact
      valence := valence
      kekule := kekule
      depth_covered := by simp [analysisFuel] }
  exact authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalCore_and_frame
    chemical frame

/-- The existing unannotated chemical-applicability record contains every operational-core fact
except written-neighbour exactness.  Supplying that genuinely separate normalization premise
closes the source operational domain; the record's branch-semantics field is not used. -/
theorem authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalApplicability
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center : Nat)
    (writtenExact : mol.WrittenNeighborExact)
    (applicable : AuthoritativeUnannotatedRule6ChemicalApplicability
      result mol state center) :
    AuthoritativeSourceRule6ResolvedOperationalDomain
      mol (unannotatedRule6ChemicalFuel mol) center := by
  let chemical : AuthoritativeSourceRule6ChemicalOperationalCore
      mol (unannotatedRule6ChemicalFuel mol) center :=
    { center_bound := applicable.molecular_center_bound
      well_formed := applicable.well_formed
      unique_bonds := applicable.unique_bonds
      written_exact := writtenExact
      valence := applicable.valence
      kekule := applicable.kekule
      depth_covered := by
        simp [unannotatedRule6ChemicalFuel, analysisFuel] }
  exact authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalCore_and_frame
    chemical applicable.connectivity_frame

/-- Exact integrated ranking-refusal applicability from chemical structure alone.  Both sides
already contain the connectivity frame, so no separate four-coordinate premise is required. -/
theorem authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic_of_chemicalCore
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (chemical : AuthoritativeSourceRule6ChemicalOperationalCore mol fuel center) :
    AuthoritativeUnannotatedTetrahedralRankingUnresolved
        result mol state fuel center ↔
      AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
        result mol state fuel center := by
  constructor
  · rintro ⟨spec, atomEq, unannotated, frame, ordinaryNone, terminalFalse, sourceNone⟩
    have operational :=
      authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalCore_and_frame
        chemical frame
    exact ⟨spec, atomEq, unannotated, frame, ordinaryNone, terminalFalse,
      (authoritativeSourceRule6Stereogenicity?_eq_none_iff_semanticUnresolved
        mol fuel center operational).mp sourceNone⟩
  · rintro ⟨spec, atomEq, unannotated, frame, ordinaryNone, terminalFalse, semanticFailure⟩
    have operational :=
      authoritativeSourceRule6ResolvedOperationalDomain_of_chemicalCore_and_frame
        chemical frame
    exact ⟨spec, atomEq, unannotated, frame, ordinaryNone, terminalFalse,
      (authoritativeSourceRule6Stereogenicity?_eq_none_iff_semanticUnresolved
        mol fuel center operational).mpr semanticFailure⟩

/-- Exact readiness/refusal normal form under the explicit chemical operational core.  No
four-coordinate or executable-success premise is added: each present branch carries its own
independent connectivity and semantic evidence. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_some_iff_semantic_of_chemicalCore
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (outcome : StereoOutcome)
    (chemical : AuthoritativeSourceRule6ChemicalOperationalCore mol fuel center) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some outcome ↔
      (outcome = .refused .notSpecified ∧
        AuthoritativeUnannotatedTetrahedralStereogenic
          result mol state fuel center) ∨
      (outcome = .refused .rankingUnresolved ∧
        AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
          result mol state fuel center) := by
  rw [unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_some_iff]
  rw [authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic_of_chemicalCore
    result mol state fuel center chemical]

/-- In particular, the public ranking-unresolved outcome has exactly the six semantic source
causes under the chemical operational core. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff_semantic_of_chemicalCore
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (chemical : AuthoritativeSourceRule6ChemicalOperationalCore mol fuel center) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some (.refused .rankingUnresolved) ↔
      AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
        result mol state fuel center :=
  (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff
      result mol state fuel center).trans
    (authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic_of_chemicalCore
      result mol state fuel center chemical)

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter
