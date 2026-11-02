import TetraStereo.OneCenter.RawFourLigandFrameLaws
import TetraStereo.OneCenter.CIPAuthoritativeRule6SourceTopologySemantics
import TetraStereo.OneCenter.CIPAuthoritativeRule6SourceInitialOrderCompleteness
import TetraStereo.OneCenter.CIPAuthoritativeRule6ResolvedBranchAgreement

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open BlueBookP92.Perception
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPOccurrenceCompleteness
open AuthoritativeCIPRule6Completeness

/-!
# Chemical totality of source-level unannotated Rule-6 perception

The canonical occurrence tree is finite for a graph-theoretic reason: every real child adds a
fresh in-range atom to its history, while every duplicate child is terminal.  Tree collection is
therefore total at the molecular fuel bound.  Occurrence labeling remains deliberately fail-closed:
applicability separately requires the source-semantic readiness of that auxiliary environment.
-/

/-- Every node generated downward from a well-formed molecular center has depth at most the
number of real atoms. Duplicate nodes may occupy the last depth, but cannot have children. -/
theorem canonicalCenterTreeNode_depth_le_atomCount
    {mol : RawMolecule} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center node) :
    node.depth ≤ mol.atomCount := by
  induction generated with
  | root =>
      simp [canonicalCenterRoot, CanonicalBranchNode.depth]
  | @child parent child parentGenerated childMember inductionHypothesis =>
      have parentReal := real_of_child_mem childMember
      have parentLengthLe := parentGenerated.real_history_length_le_atomCount
        centerBound wellFormed parentReal
      have parentHead := parentGenerated.history_head
      have parentPositive : 0 < parent.history.length := by
        cases historyEq : parent.history with
        | nil => simp [historyEq] at parentHead
        | cons atom history => simp [historyEq]
      have childDepth := mol.canonicalChildren_depth
        parent child childMember parentPositive
      have parentDepthLt : parent.depth < mol.atomCount := by
        unfold CanonicalBranchNode.depth
        omega
      omega

/-- Breadth-first collection succeeds whenever its starting frontier consists of generated nodes
at one common depth and the remaining fuel extends beyond the maximum molecular depth. -/
theorem collectCanonicalTreeAuthoritative_exists_of_generated_frontier
    {mol : RawMolecule} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed) :
    ∀ fuel depth frontier,
      mol.atomCount < depth + fuel →
      (∀ node, node ∈ frontier →
        CanonicalCenterTreeNode mol center node ∧ node.depth = depth) →
      ∃ nodes, collectCanonicalTreeAuthoritative mol fuel frontier = some nodes
  | 0, depth, [], _bound, _generated => ⟨[], rfl⟩
  | 0, depth, head :: tail, bound, generated => by
      have headGenerated := (generated head (by simp)).1
      have headDepth := (generated head (by simp)).2
      have depthLe := canonicalCenterTreeNode_depth_le_atomCount
        centerBound wellFormed headGenerated
      omega
  | fuel + 1, depth, [], _bound, _generated => ⟨[], rfl⟩
  | fuel + 1, depth, head :: tail, bound, generated => by
      let frontier := head :: tail
      let next := frontier.flatMap mol.canonicalChildren
      have nextGenerated : ∀ node, node ∈ next →
          CanonicalCenterTreeNode mol center node ∧ node.depth = depth + 1 := by
        intro child childPresent
        rw [List.mem_flatMap] at childPresent
        obtain ⟨parent, parentPresent, childMember⟩ := childPresent
        have parentFacts := generated parent parentPresent
        have parentHead := parentFacts.1.history_head
        have parentPositive : 0 < parent.history.length := by
          cases historyEq : parent.history with
          | nil => simp [historyEq] at parentHead
          | cons atom history => simp [historyEq]
        exact ⟨.child parentFacts.1 childMember, by
          rw [mol.canonicalChildren_depth parent child childMember parentPositive,
            parentFacts.2]⟩
      obtain ⟨collected, collectedEq⟩ :=
        collectCanonicalTreeAuthoritative_exists_of_generated_frontier
          centerBound wellFormed fuel (depth + 1) next (by omega) nextGenerated
      have collectedEq' : collectCanonicalTreeAuthoritative mol fuel
          (mol.canonicalChildren head ++ tail.flatMap mol.canonicalChildren) =
            some collected := by
        simpa [next, frontier] using collectedEq
      refine ⟨frontier ++ collected, ?_⟩
      simp [collectCanonicalTreeAuthoritative, frontier, collectedEq']

/-- The complete downward canonical tree at a real center is collected successfully at every
fuel strictly larger than `atomCount`; no width or occurrence-count premise is used. -/
theorem collectCanonicalTreeAuthoritative_center_exists
    {mol : RawMolecule} {center fuel : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (depthCovered : mol.atomCount < fuel) :
    ∃ nodes,
      collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot center] = some nodes := by
  apply collectCanonicalTreeAuthoritative_exists_of_generated_frontier
    centerBound wellFormed fuel 0 [canonicalCenterRoot center]
  · simpa using depthCovered
  · intro node member
    have nodeEq : node = canonicalCenterRoot center := by simpa using member
    subst node
    exact ⟨.root, by simp [canonicalCenterRoot, CanonicalBranchNode.depth]⟩

/- Four-coordinate written-frame lemmas are re-exported from RawFourLigandFrameLaws. -/

/-- Standard written-neighbor integrity makes the center plus its four physical ligand positions
duplicate-free, which is the only carrier condition needed to interpret the exhaustive topology
search as a finite constitutional-bijection decision. -/
theorem authoritativeSourceRule6_centeredLigands_nodup
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (writtenExact : mol.WrittenNeighborExact)
    (writtenFour : (mol.writtenNeighbors center).length = 4) :
    (center :: mol.ligandsWithLonePair center).Nodup := by
  have ligandsEq : mol.ligandsWithLonePair center = mol.writtenNeighbors center :=
    ligandsWithLonePair_eq_writtenNeighbors_of_length_four mol center writtenFour
  have clauses := RawMolecule.WrittenNeighborExact.at mol writtenExact
    (⟨center, centerBound⟩ : Fin mol.atomCount)
  have centerNotWritten : center ∉ mol.writtenNeighbors center := by
    intro centerMember
    have positive := (clauses.2.2 ⟨center, centerBound⟩).mp centerMember
    simp [mol.bondOrder_self center] at positive
  rw [ligandsEq]
  exact List.nodup_cons.mpr ⟨centerNotWritten, clauses.1⟩

/-- Four materialized canonical ligand occurrences give the exact source frame. -/
theorem occurrenceLigandFrame?_eq_occurrenceLigandCursors_of_four
    (mol : RawMolecule) (center : Nat)
    (writtenFour : (mol.writtenNeighbors center).length = 4)
    (occurrencesFour :
      (occurrenceLigandCursors mol (canonicalCenterRoot center)).length = 4) :
    occurrenceLigandFrame? mol (canonicalCenterRoot center) =
      some (occurrenceLigandCursors mol (canonicalCenterRoot center)) := by
  have ligandsFour := ligandsWithLonePair_length_eq_four_of_written
    mol center writtenFour
  have occurrencesFour' :
      (occurrenceLigandCursors mol
        { atom := center, parent := center, history := [center],
          provenance := CanonicalNodeProvenance.realAtom }).length = 4 := by
    simpa [canonicalCenterRoot] using occurrencesFour
  simp [occurrenceLigandFrame?, canonicalCenterRoot, ligandsFour, occurrencesFour']

/-- Chemical totality of the initial authoritative partition at every fuel covering the complete
canonical reroot budget.  The earlier scheduler theorem selected the least standard bound; this
monotone support form is what connects the proof to production's slightly larger `analysisFuel`. -/
theorem authoritativeRule6InitialPartition_exists_of_chemical_frame_at_fuel
    {mol : RawMolecule} {state : OccurrenceAuxState} {center fuel : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    {roots : List CanonicalRerootCursor}
    (frameEq : occurrenceLigandFrame? mol occurrence = some roots)
    (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) :
    ∃ sorted adjacent,
      sortAuthoritativeRule6InitialPositions? mol state fuel
          roots (List.range 4) = some sorted ∧
        compareAuthoritativeRule6InitialAdjacent? mol state fuel
          roots sorted = some adjacent := by
  let hierarchy : DescriptorRule6HierarchySupport mol state fuel :=
    .ofLocalizedMancudeKekuleAdmissible mol state fuel wellFormed unique kekule
  have bonding : CanonicalCenterBondingNumberSix mol center :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center centerBound wellFormed unique valence
  apply authoritativeRule6InitialPartition_exists_of_support hierarchy roots
    (occurrenceLigandFrame?_result_length mol occurrence roots frameEq)
  exact occurrenceLigandFrame_supported centerBound wellFormed bonding occurrenceGenerated
    frameEq fuel depthCovered

/-- Every physical source-frame cursor is a generated molecular root with complete recursive
support. Multiple-bond duplicates remain descendants of that root rather than becoming extra
positions in the center frame. -/
theorem authoritativeSourceRule6LigandCursor_supported
    {mol : RawMolecule} {center fuel : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (writtenExact : mol.WrittenNeighborExact)
    (bonding : CanonicalCenterBondingNumberSix mol center)
    (writtenFour : (mol.writtenNeighbors center).length = 4)
    (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) :
    ∀ cursor, cursor ∈ authoritativeSourceRule6LigandCursors mol center →
      CursorSupport mol fuel cursor := by
  intro cursor member
  simp only [authoritativeSourceRule6LigandCursors, List.mem_map] at member
  rcases member with ⟨ligand, ligandMember, rfl⟩
  have ligandsEq : mol.ligandsWithLonePair center = mol.writtenNeighbors center :=
    ligandsWithLonePair_eq_writtenNeighbors_of_length_four mol center writtenFour
  have writtenMember : ligand ∈ mol.writtenNeighbors center := by
    simpa [ligandsEq] using ligandMember
  let centerFin : Fin mol.atomCount := ⟨center, centerBound⟩
  have clauses := RawMolecule.WrittenNeighborExact.at mol writtenExact centerFin
  have ligandBound : ligand < mol.atomCount := clauses.2.1 ligand writtenMember
  let ligandFin : Fin mol.atomCount := ⟨ligand, ligandBound⟩
  have positive : 0 < mol.bondOrder center ligand :=
    (clauses.2.2 ligandFin).mp writtenMember
  have distinct : ligand ≠ center := by
    intro equal
    have positiveSelf : 0 < mol.bondOrder center center := by
      simpa [equal] using positive
    rw [mol.bondOrder_self] at positiveSelf
    exact (Nat.not_lt_zero 0 positiveSelf).elim
  have childMember : canonicalRoot center ligand ∈
      mol.canonicalChildren (canonicalCenterRoot center) :=
    canonicalRoot_mem_canonicalChildren_of_bondOrder_pos
      mol center ligand distinct positive
  have eligible : CanonicalCenterRerootCursor mol center
      { node := canonicalRoot center ligand
        previous? := some (canonicalCenterRoot center) } := by
    simpa using canonicalRootCursor_eligible childMember
  exact (canonicalCenterCursorSupport centerBound wellFormed bonding eligible).mono depthCovered

/-- Chemical admission makes the physical four-position source partition total. This theorem does
not require the canonical center node to have exactly four children: multiple-bond duplicates may
increase that child count without changing the number of physical ligand positions. -/
theorem authoritativeSourceRule6InitialPartition_exists_at_fuel
    {mol : RawMolecule} {state : OccurrenceAuxState} {center fuel : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol)
    (writtenFour : (mol.writtenNeighbors center).length = 4)
    (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) :
    ∃ sorted adjacent,
      sortAuthoritativeRule6InitialPositions? mol state fuel
          (authoritativeSourceRule6LigandCursors mol center) (List.range 4) = some sorted ∧
        compareAuthoritativeRule6InitialAdjacent? mol state fuel
          (authoritativeSourceRule6LigandCursors mol center) sorted = some adjacent := by
  let hierarchy : DescriptorRule6HierarchySupport mol state fuel :=
    .ofLocalizedMancudeKekuleAdmissible mol state fuel wellFormed unique kekule
  have bonding : CanonicalCenterBondingNumberSix mol center :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center centerBound wellFormed unique valence
  apply authoritativeRule6InitialPartition_exists_of_support hierarchy
    (authoritativeSourceRule6LigandCursors mol center)
  · simpa using ligandsWithLonePair_length_eq_four_of_written mol center writtenFour
  · exact authoritativeSourceRule6LigandCursor_supported centerBound wellFormed writtenExact
      bonding writtenFour depthCovered

/-- Production's molecule-size fuel, used on the explicit unannotated Rule-6 applicability domain. -/
def unannotatedRule6ChemicalFuel (mol : RawMolecule) : Nat :=
  analysisFuel mol

/-- Chemical and semantic applicability of the unannotated Rule-6 fallback.

Finite-molecule hypotheses discharge canonical-tree collection.  `occurrence_environment` records
the separate source-semantic fact that every selected annotated occurrence can be labeled by the
fail-closed authoritative builder.  The final field is the actual stereogenic condition: for that
environment and its initial partition, the partition has the required topology and satisfies the
independent parity-free P-92 Rule-6 branch predicate. It does not mention a Rule-6 result,
descriptor, solved label, or public output. -/
structure AuthoritativeUnannotatedRule6ChemicalApplicability
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center : Nat) where
  spec : AtomSpec
  parsed_atom : result.parsed.atomAt? center = some spec
  unannotated : spec.tetrahedral? = none
  parsed_center_bound : center < result.parsed.atomCount
  molecular_center_bound : center < mol.atomCount
  well_formed : mol.WellFormed
  unique_bonds : mol.BondRecordsUnique
  valence : mol.ValenceOK
  kekule : LocalizedMancudeKekuleAdmissible mol
  connectivity_frame : ConnectivityOnlyTetrahedralFrame result mol center
  occurrence_environment :
    ∃ aux, buildOccurrenceAuxStateFullyAuthoritative?
      mol (unannotatedRule6ChemicalFuel mol) center = some aux
  branch_semantics :
    ∀ aux sorted adjacent,
      buildOccurrenceAuxStateFullyAuthoritative?
          mol (unannotatedRule6ChemicalFuel mol) center = some aux →
      sortAuthoritativeRule6InitialPositions?
          mol aux (unannotatedRule6ChemicalFuel mol)
            (authoritativeSourceRule6LigandCursors mol center) (List.range 4) = some sorted →
      compareAuthoritativeRule6InitialAdjacent?
          mol aux (unannotatedRule6ChemicalFuel mol)
            (authoritativeSourceRule6LigandCursors mol center) sorted = some adjacent →
      ¬ SourceHasOddPartitionPreservingConstitutionAutomorphism
          mol center (mol.ligandsWithLonePair center)
            (fun left right =>
              (compareAuthoritativeRule6InitialPositions?
                mol aux (unannotatedRule6ChemicalFuel mol)
                  (authoritativeSourceRule6LigandCursors mol center) left right).any
                  fun decision => decision.ordering = Ordering.eq) ∧
        AuthoritativeRule6ResolvedBranchAgreement mol aux
          (unannotatedRule6ChemicalFuel mol) (canonicalCenterRoot center)
          (authoritativeSourceRule6LigandCursors mol center) sorted adjacent

/-- The explicit chemical applicability class forces the source-level independent Rule-6
stereogenicity judgment.  Occurrence-environment readiness is bundled explicitly in applicability;
it is not inferred from the finite-molecule hypotheses. -/
theorem authoritativeSourceRule6Stereogenic_of_chemical_applicability
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center : Nat)
    (writtenExact : mol.WrittenNeighborExact)
    (applicable : AuthoritativeUnannotatedRule6ChemicalApplicability
      result mol state center) :
    AuthoritativeSourceRule6Stereogenic
      mol (unannotatedRule6ChemicalFuel mol) center := by
  have writtenFour : (mol.writtenNeighbors center).length = 4 := by
    rcases applicable.connectivity_frame with
      ⟨candidateSpec, _atomEq, _element, _extended, four⟩
    exact four
  obtain ⟨aux, auxEq⟩ := applicable.occurrence_environment
  obtain ⟨sorted, adjacent, sortedEq, adjacentEq⟩ :=
    authoritativeSourceRule6InitialPartition_exists_at_fuel
      (mol := mol) (state := aux) (center := center)
      (fuel := unannotatedRule6ChemicalFuel mol)
      applicable.molecular_center_bound applicable.well_formed
      applicable.unique_bonds writtenExact applicable.valence
      applicable.kekule writtenFour (by
        simp [unannotatedRule6ChemicalFuel, analysisFuel])
  obtain ⟨noOdd, resolved⟩ :=
    applicable.branch_semantics aux sorted adjacent auxEq sortedEq adjacentEq
  let hierarchy : DescriptorRule6HierarchySupport mol aux
      (unannotatedRule6ChemicalFuel mol) :=
    .ofLocalizedMancudeKekuleAdmissible mol aux
      (unannotatedRule6ChemicalFuel mol) applicable.well_formed
      applicable.unique_bonds applicable.kekule
  have bonding : CanonicalCenterBondingNumberSix mol center :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center applicable.molecular_center_bound applicable.well_formed
      applicable.unique_bonds applicable.valence
  have rootsSupported : ∀ cursor,
      cursor ∈ authoritativeSourceRule6LigandCursors mol center →
        CursorSupport mol (unannotatedRule6ChemicalFuel mol) cursor :=
    authoritativeSourceRule6LigandCursor_supported
      applicable.molecular_center_bound applicable.well_formed writtenExact bonding
      writtenFour (by
        simp [unannotatedRule6ChemicalFuel, analysisFuel])
  have rootsLength :
      (authoritativeSourceRule6LigandCursors mol center).length = 4 := by
    rw [authoritativeSourceRule6LigandCursors_length]
    exact ligandsWithLonePair_length_eq_four_of_written mol center writtenFour
  have sortedEqFull :
      sortAuthoritativeRule6InitialPositions?
          mol aux (unannotatedRule6ChemicalFuel mol)
            (authoritativeSourceRule6LigandCursors mol center)
            (List.range (authoritativeSourceRule6LigandCursors mol center).length) =
        some sorted := by
    simpa [rootsLength] using sortedEq
  have adjacentNotLt : some Ordering.lt ∉ adjacent :=
    authoritativeRule6InitialAdjacent_not_lt_of_support
      hierarchy (authoritativeSourceRule6LigandCursors mol center) rootsSupported
      sortedEqFull adjacentEq
  have centeredNodup :
      (center :: mol.ligandsWithLonePair center).Nodup :=
    authoritativeSourceRule6_centeredLigands_nodup mol center
      applicable.molecular_center_bound writtenExact writtenFour
  have oddFalse :=
    (hasOddConstitutionAutomorphismAtCenter_eq_some_false_iff
      mol center (mol.ligandsWithLonePair center)
        (fun left right =>
          (compareAuthoritativeRule6InitialPositions?
            mol aux (unannotatedRule6ChemicalFuel mol)
              (authoritativeSourceRule6LigandCursors mol center) left right).any
              fun decision => decision.ordering = Ordering.eq)
        (ligandsWithLonePair_length_eq_four_of_written mol center writtenFour)
        centeredNodup).mpr noOdd
  have resolvedStereogenic :
      AuthoritativeRule6ResolvedStereogenic mol aux
        (unannotatedRule6ChemicalFuel mol) (canonicalCenterRoot center)
        (authoritativeSourceRule6LigandCursors mol center) sorted adjacent :=
    (authoritativeRule6ResolvedStereogenic_iff_branchAgreement
      mol aux (unannotatedRule6ChemicalFuel mol) (canonicalCenterRoot center)
        (authoritativeSourceRule6LigandCursors mol center) sorted adjacent).mpr resolved
  exact ⟨aux, sorted, adjacent,
    ligandsWithLonePair_length_eq_four_of_written mol center writtenFour,
    auxEq, sortedEq, adjacentEq, adjacentNotLt, oddFalse, resolvedStereogenic⟩

/-- The source Boolean is therefore complete on the explicit chemical applicability class. -/
theorem authoritativeSourceRule6Stereogenicity?_eq_some_true_of_chemical_applicability
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center : Nat)
    (writtenExact : mol.WrittenNeighborExact)
    (applicable : AuthoritativeUnannotatedRule6ChemicalApplicability
      result mol state center) :
    authoritativeSourceRule6Stereogenicity?
        mol (unannotatedRule6ChemicalFuel mol) center = some true :=
  (authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
    mol (unannotatedRule6ChemicalFuel mol) center).mpr
      (authoritativeSourceRule6Stereogenic_of_chemical_applicability
        result mol state center writtenExact applicable)

/-- Chemical applicability also forces the integrated ordinary-tetrahedral perception judgment.
If ordinary Rules-1a--5 already rank the center, that earlier success wins; otherwise the proved
authoritative Rule-6 source judgment is consulted before any legacy terminal-tie exclusion. -/
theorem authoritativeUnannotatedTetrahedralStereogenic_of_chemical_applicability
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center : Nat)
    (writtenExact : mol.WrittenNeighborExact)
    (applicable : AuthoritativeUnannotatedRule6ChemicalApplicability
      result mol state center) :
    AuthoritativeUnannotatedTetrahedralStereogenic
      result mol state (unannotatedRule6ChemicalFuel mol) center := by
  refine ⟨applicable.spec, applicable.parsed_atom, applicable.unannotated,
    applicable.connectivity_frame, ?_⟩
  cases rankingEq : rankBranchPositionsThroughOfficialContext?
      result mol state (unannotatedRule6ChemicalFuel mol) center
        (mol.writtenNeighbors center) with
  | some positions => exact Or.inl ⟨positions, rfl⟩
  | none =>
      exact Or.inr ⟨rfl,
        authoritativeSourceRule6Stereogenic_of_chemical_applicability
          result mol state center writtenExact applicable⟩

/-- Final chemical completeness theorem: every applicable unannotated Rule-6 center is present
exactly once in the integrated molecule-wide scan and is conservatively reported as
configuration-unspecified. -/
theorem every_chemicallyApplicable_unannotatedRule6Center_public_exactly_once
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center : Nat)
    (writtenExact : mol.WrittenNeighborExact)
    (applicable : AuthoritativeUnannotatedRule6ChemicalApplicability
      result mol state center) :
    ∃ assignment,
      assignment ∈ tetrahedralAssignmentsWithAuthoritativeRule6
        result mol state (unannotatedRule6ChemicalFuel mol) ∧
      assignment.unit = .tetrahedral center ∧
      assignment.outcome = .refused .notSpecified ∧
      List.count (.tetrahedral center)
        ((tetrahedralAssignmentsWithAuthoritativeRule6
          result mol state (unannotatedRule6ChemicalFuel mol)).map
            StereoAssignment.unit) = 1 := by
  exact every_authoritativeUnannotatedTetrahedralStereogenic_public_exactly_once
    result mol state (unannotatedRule6ChemicalFuel mol) center
    applicable.parsed_center_bound
    (authoritativeUnannotatedTetrahedralStereogenic_of_chemical_applicability
      result mol state center writtenExact applicable)

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter
