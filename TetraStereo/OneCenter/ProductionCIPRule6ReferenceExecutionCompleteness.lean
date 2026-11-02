import TetraStereo.OneCenter.ProductionCIPRule6InitialPartitionCompleteness
import TetraStereo.OneCenter.ConstitutionAutomorphismSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

/-!
# Structural completeness of Rule-6 reference execution

The initial partition theorem removes every optional failure in the Rules-1--5 ordering stage.
This module follows the reference positions selected from that partition through the literal
production Rule-6 ranking machinery.

The conclusions deliberately separate structural execution from the remaining promoted-ranking
conditions. Strict uniqueness and agreement of the descriptors produced by different admissible
references cannot follow from bounded branching and comparator totality alone. The formerly
separate odd-topology condition is closed here against an independent constitutional-bijection
semantics, in both its positive and negative forms.
-/

open RawMolecule
open ProductionCIPDescriptorBranchingCompleteness
open DeclarativeCIP.ProductionOccurrenceRules456

/-- Promoted insertion preserves exactly the inserted position and the prior positions. -/
theorem InsertPromotedPositionTrace.positions_perm
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {ligands : List Nat}
    {referencePosition candidate : Nat} {input : List Nat}
    {output : List Nat × Nat × Bool}
    (derived : InsertPromotedPositionTrace (mol := mol) aux fuel roots ligands
      referencePosition candidate input output) :
    output.1.Perm (candidate :: input) := by
  induction derived with
  | nil => exact List.Perm.refl _
  | lt low remaining decision deeper comparison isLt tail inductionHypothesis =>
      exact (List.Perm.cons low inductionHypothesis).trans
        (List.Perm.swap candidate low remaining)
  | eq => exact List.Perm.refl _
  | gt => exact List.Perm.refl _

/-- The promoted fold contains exactly the unprocessed input, in reverse insertion order, followed
by the positions already present in the accumulator. -/
theorem FoldPromotedPositionsTrace.positions_perm
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {ligands : List Nat}
    {referencePosition : Nat} {input : List Nat}
    {accumulator output : List Nat × Nat × Bool}
    (derived : FoldPromotedPositionsTrace (mol := mol) aux fuel roots ligands
      referencePosition input accumulator output) :
    output.1.Perm (input.reverse ++ accumulator.1) := by
  induction derived with
  | nil => simp
  | cons candidate remaining accumulator inserted output insertion tail inductionHypothesis =>
      have appended :
          (remaining.reverse ++ inserted.1).Perm
            (remaining.reverse ++ (candidate :: accumulator.1)) :=
        List.Perm.append_left remaining.reverse insertion.positions_perm
      exact inductionHypothesis.trans (by simpa using appended)

/-- A complete promoted ranking is a permutation of its supplied starting positions. -/
theorem PromotedRankingTrace.positions_perm
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor} {ligands start : List Nat}
    {referencePosition : Nat} {ranking : Rule6TrackedRanking}
    (derived : PromotedRankingTrace (mol := mol) aux fuel roots ligands start
      referencePosition ranking) :
    ranking.positions.Perm start := by
  cases derived with
  | intro tracked fold =>
      have trackedPerm : tracked.1.Perm start.reverse := by
        simpa using fold.positions_perm
      exact (List.reverse_perm tracked.1).trans
        (trackedPerm.trans (List.reverse_perm start))

end TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open ProductionCIPDescriptorBranchingCompleteness
open DeclarativeCIP.ProductionOccurrenceRules456

namespace DescriptorBranchingRule6CIPFrame

/-- Every position enumerated by the production two-group reference selector is one of the four
positions in the sorted carrier. -/
theorem equivalentReference_mem_sorted
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (sorted_length : sorted.length = 4) {position : Nat}
    (member : position ∈ rule6EquivalentReferencePositions sorted adjacent) :
    position ∈ sorted := by
  rcases List.length_eq_four.mp sorted_length with ⟨a, b, c, d, rfl⟩
  unfold rule6EquivalentReferencePositions at member
  by_cases first : adjacent.getD 0 none == some Ordering.gt
  · simp at member ⊢
    aesop
  · by_cases second : adjacent.getD 1 none == some Ordering.gt
    · simp at member ⊢
      aesop
    · simp at member ⊢
      aesop

/-- The production two-group reference selector is never empty on an exact four-position frame. -/
theorem equivalentReferences_nonempty
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (sorted_length : sorted.length = 4) :
    (rule6EquivalentReferencePositions sorted adjacent).head?.isSome := by
  rcases List.length_eq_four.mp sorted_length with ⟨a, b, c, d, rfl⟩
  simp only [rule6EquivalentReferencePositions]
  split <;> simp_all
  split <;> simp_all

-- Keep `frame` explicit for source-compatible named theorem applications.
set_option linter.unusedVariables false in
/-- Every production two-group reference is a genuine position below four. -/
theorem equivalentReference_lt_four
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted) (adjacent : List (Option Ordering))
    {position : Nat}
    (member : position ∈ rule6EquivalentReferencePositions sorted adjacent) :
    position < 4 := by
  have sortedLength : sorted.length = 4 := by
    simpa using sorting.perm.length_eq
  have positionMem : position ∈ sorted :=
    equivalentReference_mem_sorted sorted adjacent sortedLength member
  exact List.mem_range.mp (sorting.perm.mem_iff.mp positionMem)

/-- Every reference enumerated for a two-group carrier reaches a complete promoted ranking trace.
No uniqueness or cross-reference descriptor agreement is assumed or concluded. -/
theorem equivalentReference_promoted_trace_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted) (adjacent : List (Option Ordering))
    (referencePosition : Nat)
    (member : referencePosition ∈ rule6EquivalentReferencePositions sorted adjacent) :
    ∃ ranking,
      PromotedRankingTrace (mol := mol) state fuel roots frame.ligands sorted
        referencePosition ranking := by
  have reference_lt := frame.equivalentReference_lt_four sorting adjacent member
  have sorted_lt : ∀ position, position ∈ sorted → position < 4 := by
    intro position positionMember
    exact List.mem_range.mp (sorting.perm.mem_iff.mp positionMember)
  rcases frame.promoted_four_position_ranking_exists referencePosition reference_lt
      sorted sorted_lt with ⟨ranking, rankingEq⟩
  exact ⟨ranking, promotedRankingTrace_complete state fuel roots frame.ligands sorted
    referencePosition ranking rankingEq⟩

/-- The rank-one reference list used in the two-group branch is structurally executable in full:
it is nonempty, every member is below four, and every member has a promoted ranking trace. -/
structure TwoGroupReferenceExecutionCertificate
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Prop where
  references_nonempty :
    (rule6EquivalentReferencePositions sorted adjacent).head?.isSome
  reference_lt_four : ∀ referencePosition,
    referencePosition ∈ rule6EquivalentReferencePositions sorted adjacent →
      referencePosition < 4
  promoted_trace : ∀ referencePosition,
    referencePosition ∈ rule6EquivalentReferencePositions sorted adjacent →
      ∃ ranking,
        PromotedRankingTrace (mol := mol) state fuel roots frame.ligands sorted
          referencePosition ranking

theorem twoGroupReferenceExecutionCertificate_nonempty
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted) :
    Nonempty (TwoGroupReferenceExecutionCertificate frame sorted adjacent) := by
  have sortedLength : sorted.length = 4 := by
    simpa using sorting.perm.length_eq
  exact ⟨
    { references_nonempty := equivalentReferences_nonempty sorted adjacent sortedLength
      reference_lt_four := fun referencePosition member =>
        frame.equivalentReference_lt_four sorting adjacent member
      promoted_trace := fun referencePosition member =>
        frame.equivalentReference_promoted_trace_exists sorting adjacent referencePosition member }⟩

/-- The three-group branch's fixed rank-one reference, its cursor lookup, and its promoted ranking
are all structurally total.  The middle tie, local-reference observation, and strict uniqueness
checks remain separate semantic conditions. -/
theorem threeGroupReferenceExecution_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted) :
    ∃ referencePosition referenceRoot ranking,
      sorted[1]? = some referencePosition ∧
      roots[referencePosition]? = some referenceRoot ∧
      PromotedRankingTrace (mol := mol) state fuel roots frame.ligands sorted
        referencePosition ranking := by
  have sortedLength : sorted.length = 4 := by
    simpa using sorting.perm.length_eq
  have oneBound : 1 < sorted.length := by omega
  let referencePosition := sorted[1]
  have referenceEq : sorted[1]? = some referencePosition :=
    List.getElem?_eq_getElem oneBound
  have referenceMem : referencePosition ∈ sorted := List.getElem_mem oneBound
  have referenceLt : referencePosition < 4 :=
    List.mem_range.mp (sorting.perm.mem_iff.mp referenceMem)
  rcases frame.positionInFrame_of_lt_four referencePosition referenceLt with
    ⟨referenceRoot, referenceRootEq⟩
  have sortedLt : ∀ position, position ∈ sorted → position < 4 := by
    intro position member
    exact List.mem_range.mp (sorting.perm.mem_iff.mp member)
  rcases frame.promoted_four_position_ranking_exists referencePosition referenceLt sorted
      sortedLt with ⟨ranking, rankingEq⟩
  exact ⟨referencePosition, referenceRoot, ranking, referenceEq, referenceRootEq,
    promotedRankingTrace_complete state fuel roots frame.ligands sorted referencePosition
      ranking rankingEq⟩

/-- The two ranking calls in the four-way branch are structurally total.  The first promoted
ranking is a permutation of the initial order, so its rank-one second reference is again a genuine
position below four.  The subsequent difference/agreement checks remain semantic conditions. -/
theorem fourWayReferenceExecution_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted) :
    ∃ firstPosition firstRanking secondPosition secondRanking,
      sorted[0]? = some firstPosition ∧
      PromotedRankingTrace (mol := mol) state fuel roots frame.ligands sorted
        firstPosition firstRanking ∧
      firstRanking.positions[1]? = some secondPosition ∧
      PromotedRankingTrace (mol := mol) state fuel roots frame.ligands
        firstRanking.positions secondPosition secondRanking := by
  have sortedLength : sorted.length = 4 := by
    simpa using sorting.perm.length_eq
  have zeroBound : 0 < sorted.length := by omega
  let firstPosition := sorted[0]
  have firstEq : sorted[0]? = some firstPosition := List.getElem?_eq_getElem zeroBound
  have firstMem : firstPosition ∈ sorted := List.getElem_mem zeroBound
  have firstLt : firstPosition < 4 :=
    List.mem_range.mp (sorting.perm.mem_iff.mp firstMem)
  have sortedLt : ∀ position, position ∈ sorted → position < 4 := by
    intro position member
    exact List.mem_range.mp (sorting.perm.mem_iff.mp member)
  rcases frame.promoted_four_position_ranking_exists firstPosition firstLt sorted sortedLt with
    ⟨firstRanking, firstRankingEq⟩
  let firstTrace := promotedRankingTrace_complete state fuel roots frame.ligands sorted
    firstPosition firstRanking firstRankingEq
  have firstPositionsLength : firstRanking.positions.length = 4 := by
    have lengthEq := firstTrace.positions_perm.length_eq
    simpa [sortedLength] using lengthEq
  have oneBound : 1 < firstRanking.positions.length := by omega
  let secondPosition := firstRanking.positions[1]
  have secondEq : firstRanking.positions[1]? = some secondPosition :=
    List.getElem?_eq_getElem oneBound
  have secondMem : secondPosition ∈ firstRanking.positions := List.getElem_mem oneBound
  have secondSortedMem : secondPosition ∈ sorted := firstTrace.positions_perm.mem_iff.mp secondMem
  have secondLt : secondPosition < 4 :=
    List.mem_range.mp (sorting.perm.mem_iff.mp secondSortedMem)
  have firstPositionsLt : ∀ position, position ∈ firstRanking.positions → position < 4 := by
    intro position member
    exact List.mem_range.mp
      (sorting.perm.mem_iff.mp (firstTrace.positions_perm.mem_iff.mp member))
  rcases frame.promoted_four_position_ranking_exists secondPosition secondLt
      firstRanking.positions firstPositionsLt with ⟨secondRanking, secondRankingEq⟩
  exact ⟨firstPosition, firstRanking, secondPosition, secondRanking, firstEq, firstTrace,
    secondEq, promotedRankingTrace_complete state fuel roots frame.ligands
      firstRanking.positions secondPosition secondRanking secondRankingEq⟩

/-- Vertex carrier searched for a centered constitutional automorphism. -/
def oddConstitutionVertices (mol : RawMolecule) (center : Nat) (ligands : List Nat) : List Nat :=
  (mol.reachableAvoiding (mol.atomCount + 1) mol.atomCount [center] [center] ++
    center :: ligands).eraseDups

/-- Center-fixing seed induced by a permutation of the four ligand roots. -/
def oddConstitutionSeed (center : Nat) (ligands permutation : List Nat) : List (Nat × Nat) :=
  (center, center) :: (List.range 4).map fun index =>
    (ligands.getD index 0, ligands.getD (permutation.getD index 0) 0)

/-- Sources not fixed by the centered seed. -/
def oddConstitutionRemaining (vertices : List Nat) (seed : List (Nat × Nat)) : List Nat :=
  vertices.filter fun atom => !(seed.map Prod.fst).contains atom

/-- Removing a unique in-carrier seed source set and then appending that set recovers exactly the
carrier. -/
theorem oddConstitutionRemaining_append_sources_perm
    (vertices : List Nat) (seed : List (Nat × Nat))
    (vertices_nodup : vertices.Nodup)
    (sources_nodup : (seed.map Prod.fst).Nodup)
    (sources_mem : ∀ source ∈ seed.map Prod.fst, source ∈ vertices) :
    (oddConstitutionRemaining vertices seed ++ seed.map Prod.fst).Perm vertices := by
  have remainingNodup : (oddConstitutionRemaining vertices seed).Nodup :=
    vertices_nodup.filter _
  have disjoint : List.Disjoint (oddConstitutionRemaining vertices seed) (seed.map Prod.fst) := by
    rw [List.disjoint_left]
    intro source sourceRemaining sourceSeed
    have filtered := List.mem_filter.mp sourceRemaining
    have contained : (seed.map Prod.fst).contains source = true := by
      simpa using sourceSeed
    rw [contained] at filtered
    simp at filtered
  have combinedNodup :
      (oddConstitutionRemaining vertices seed ++ seed.map Prod.fst).Nodup :=
    remainingNodup.append sources_nodup disjoint
  apply (List.perm_ext_iff_of_nodup combinedNodup vertices_nodup).mpr
  intro source
  constructor
  · intro member
    rcases List.mem_append.mp member with remainingMem | seedMem
    · exact (List.mem_filter.mp remainingMem).1
    · exact sources_mem source seedMem
  · intro vertexMem
    by_cases sourceSeed : source ∈ seed.map Prod.fst
    · exact List.mem_append_right _ sourceSeed
    · apply List.mem_append_left
      exact List.mem_filter.mpr ⟨vertexMem, by simpa using sourceSeed⟩

/-- Reading every position of an exact four-element list by `getD` recovers the list. -/
theorem map_getD_range_four (values : List Nat) (length_eq : values.length = 4) :
    (List.range 4).map (fun index => values.getD index 0) = values := by
  rcases List.length_eq_four.mp length_eq with ⟨first, second, third, fourth, rfl⟩
  rfl

/-- Source projection of the centered seed is the written ligand frame with its center. -/
theorem oddConstitutionSeed_map_fst
    (center : Nat) (ligands permutation : List Nat) (ligands_length : ligands.length = 4) :
    (oddConstitutionSeed center ligands permutation).map Prod.fst = center :: ligands := by
  simp only [oddConstitutionSeed, List.map_cons, List.map_map]
  congr 1
  exact map_getD_range_four ligands ligands_length

/-- A permutation enumerated from the four positions makes the target seed a permutation of the
same centered ligand carrier. -/
theorem oddConstitutionSeed_map_snd_perm
    (center : Nat) (ligands permutation : List Nat) (ligands_length : ligands.length = 4)
    (permutation_mem : permutation ∈ List.permutations (List.range 4)) :
    ((oddConstitutionSeed center ligands permutation).map Prod.snd).Perm (center :: ligands) := by
  have positionPermutation : permutation.Perm (List.range 4) :=
    List.mem_permutations.mp permutation_mem
  have permutationLength : permutation.length = 4 := by
    simpa using positionPermutation.length_eq
  have readPermutation := map_getD_range_four permutation permutationLength
  have readLigands := map_getD_range_four ligands ligands_length
  have targetEq :
      (oddConstitutionSeed center ligands permutation).map Prod.snd =
        center :: permutation.map (fun position => ligands.getD position 0) := by
    simp only [oddConstitutionSeed, List.map_cons, List.map_map]
    congr 1
    rw [← List.map_map]
    exact congrArg (List.map fun position => ligands.getD position 0) readPermutation
  rw [targetEq]
  exact List.Perm.cons center (by
    have mapped := positionPermutation.map (fun position => ligands.getD position 0)
    rw [readLigands] at mapped
    exact mapped)

/-- Duplicate removal retains every original natural-number member. -/
theorem mem_eraseDups_of_mem_nat {atom : Nat} {values : List Nat}
    (member : atom ∈ values) : atom ∈ values.eraseDups := by
  match values with
  | [] => simp at member
  | value :: rest =>
      rw [List.eraseDups_cons]
      rcases List.mem_cons.mp member with atHead | inRest
      · exact List.mem_cons.mpr (Or.inl atHead)
      · by_cases atomEq : atom = value
        · exact List.mem_cons.mpr (Or.inl atomEq)
        · apply List.mem_cons.mpr
          apply Or.inr
          apply mem_eraseDups_of_mem_nat
          exact List.mem_filter.mpr ⟨inRest, by simp [atomEq]⟩
termination_by values.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun b : Nat => !b == value) rest)

/-- Duplicate removal never invents a natural-number member. -/
theorem mem_of_mem_eraseDups_nat {atom : Nat} {values : List Nat}
    (member : atom ∈ values.eraseDups) : atom ∈ values := by
  match values with
  | [] => simp at member
  | value :: rest =>
      rw [List.eraseDups_cons] at member
      rcases List.mem_cons.mp member with atHead | inTail
      · exact List.mem_cons.mpr (Or.inl atHead)
      · apply List.mem_cons.mpr
        apply Or.inr
        exact (List.mem_filter.mp (mem_of_mem_eraseDups_nat inTail)).1
termination_by values.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun b : Nat => !b == value) rest)

/-- Duplicate removal produces a duplicate-free natural-number list. -/
theorem eraseDups_nodup_nat (values : List Nat) : values.eraseDups.Nodup := by
  match values with
  | [] => simp
  | value :: rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro valueMem
        have filteredMem := List.mem_filter.mp (mem_of_mem_eraseDups_nat valueMem)
        simpa using filteredMem.2
      · exact eraseDups_nodup_nat (rest.filter fun b => !b == value)
termination_by values.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun b : Nat => !b == value) rest)

/-- Every centered written ligand lies in the explicit odd-automorphism carrier, including a
possible lone-pair phantom. -/
theorem mem_oddConstitutionVertices_of_mem_center_ligands
    (mol : RawMolecule) (center : Nat) (ligands : List Nat) {atom : Nat}
    (member : atom ∈ center :: ligands) :
    atom ∈ oddConstitutionVertices mol center ligands := by
  apply mem_eraseDups_of_mem_nat
  exact List.mem_append_right _ member

/-- Exact written-neighbour admission makes the center-plus-ligand frame duplicate-free, including
the branch that inserts one lone-pair phantom. -/
theorem centered_ligandsWithLonePair_nodup
    (mol : RawMolecule) (writtenExact : mol.WrittenNeighborExact) (center : Nat) (spec : AtomSpec)
    (atom_spec : mol.atomAt? center = some spec) :
    (center :: mol.ligandsWithLonePair center).Nodup := by
  have centerBound : center < mol.atomCount :=
    listGet?_eq_some_implies_lt mol.atoms center spec (by simpa [RawMolecule.atomAt?] using atom_spec)
  have writtenFacts := RawMolecule.WrittenNeighborExact.at mol writtenExact ⟨center, centerBound⟩
  have writtenNodup : (mol.writtenNeighbors center).Nodup := writtenFacts.1
  have centerNotWritten : center ∉ mol.writtenNeighbors center := by
    intro centerMem
    have positive := (writtenFacts.2.2 ⟨center, centerBound⟩).mp centerMem
    simp [mol.bondOrder_self center] at positive
  have phantomNotWritten : mol.atomCount ∉ mol.writtenNeighbors center := by
    intro phantomMem
    exact (Nat.lt_irrefl mol.atomCount) (writtenFacts.2.1 mol.atomCount phantomMem)
  have centerNePhantom : center ≠ mol.atomCount := Nat.ne_of_lt centerBound
  simp only [RawMolecule.ligandsWithLonePair, atom_spec]
  split
  · split
    · cases writtenEq : mol.writtenNeighbors center with
      | nil => simp [centerNePhantom]
      | cons first rest =>
          have frameNodup : (first :: rest).Nodup := by simpa [writtenEq] using writtenNodup
          have centerNot : center ∉ first :: rest := by simpa [writtenEq] using centerNotWritten
          have phantomNot : mol.atomCount ∉ first :: rest := by
            simpa [writtenEq] using phantomNotWritten
          simp only [List.nodup_cons] at frameNodup ⊢
          aesop
    · simp [centerNePhantom, phantomNotWritten, writtenNodup, centerNotWritten]
  · exact List.nodup_cons.mpr ⟨centerNotWritten, writtenNodup⟩

/-- One literal step of the production odd-constitutional-topology fold.  Naming the step makes
the finite search boundary explicit: the outer theorem below reasons only about this state
transition, while a later chemical theorem can characterize its inner exact-search Boolean. -/
def oddConstitutionPermutationStep (mol : RawMolecule) (center : Nat)
    (ligands : List Nat) (sameGroup : Nat → Nat → Bool)
    (status : Option Bool) (permutation : List Nat) : Option Bool :=
  if status == some true || RawMolecule.permutationIsEven permutation ||
      !(List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) then
    status
  else
    let mancudeEdges := mol.localizedMancudeEdges
    let vertices := oddConstitutionVertices mol center ligands
    let seed := oddConstitutionSeed center ligands permutation
    let seedValid := seed.all fun pair =>
      mol.sameConstitutionAtom pair.1 pair.2 &&
        mol.constitutionMappingConsistent mancudeEdges (seed.erase pair) pair.1 pair.2
    if !seedValid then status else
      let remaining := oddConstitutionRemaining vertices seed
      if mol.searchConstitutionAutomorphismExact mancudeEdges vertices remaining seed then
        some true
      else status

/-- A step begun at `some` always ends at `some`; malformed-frame failure is not introduced by
candidate evaluation. -/
theorem oddConstitutionPermutationStep_isSome
    (mol : RawMolecule) (center : Nat) (ligands : List Nat)
    (sameGroup : Nat → Nat → Bool) (status : Option Bool) (permutation : List Nat)
    (statusSome : status.isSome) :
    (oddConstitutionPermutationStep mol center ligands sameGroup status permutation).isSome := by
  simp only [oddConstitutionPermutationStep]
  split
  · exact statusSome
  · split
    · exact statusSome
    · split
      · rfl
      · exact statusSome

/-- Status-free acceptance predicate for one candidate odd root permutation. It is the Boolean
result of evaluating exactly one production step from the negative initial status. -/
def oddConstitutionPermutationAccepted (mol : RawMolecule) (center : Nat)
    (ligands : List Nat) (sameGroup : Nat → Nat → Bool) (permutation : List Nat) : Bool :=
  (oddConstitutionPermutationStep mol center ligands sameGroup (some false) permutation).getD false

/-- Exact well-formedness facts needed to interpret one odd-permutation search as a bijection of
the centered molecular carrier. -/
structure OddConstitutionPermutationCarrier (mol : RawMolecule) (center : Nat)
    (ligands : List Nat) (sameGroup : Nat → Nat → Bool) (permutation : List Nat) : Prop where
  odd : RawMolecule.permutationIsEven permutation = false
  partition_preserving :
    (List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) = true
  vertices_nodup : (oddConstitutionVertices mol center ligands).Nodup
  source_coverage :
    (oddConstitutionRemaining (oddConstitutionVertices mol center ligands)
        (oddConstitutionSeed center ligands permutation) ++
      (oddConstitutionSeed center ligands permutation).map Prod.fst).Perm
        (oddConstitutionVertices mol center ligands)
  seed_embedding :
    mol.ConstitutionPartialEmbedding mol.localizedMancudeEdges
      (oddConstitutionVertices mol center ligands) (oddConstitutionSeed center ligands permutation)

/-- The concrete centered carrier and seed form a valid search frame whenever the centered ligand
list is unique and the production all-pairs seed check succeeds. -/
theorem oddConstitutionPermutationCarrier_of_seed_valid
    {mol : RawMolecule} {center : Nat} {ligands permutation : List Nat}
    {sameGroup : Nat → Nat → Bool}
    (ligands_length : ligands.length = 4)
    (centered_ligands_nodup : (center :: ligands).Nodup)
    (permutation_mem : permutation ∈ List.permutations (List.range 4))
    (odd : RawMolecule.permutationIsEven permutation = false)
    (partition_preserving :
      (List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) = true)
    (seed_valid : (oddConstitutionSeed center ligands permutation).all (fun pair =>
      mol.sameConstitutionAtom pair.1 pair.2 &&
        mol.constitutionMappingConsistent mol.localizedMancudeEdges
          ((oddConstitutionSeed center ligands permutation).erase pair) pair.1 pair.2) = true) :
    OddConstitutionPermutationCarrier mol center ligands sameGroup permutation := by
  let vertices := oddConstitutionVertices mol center ligands
  let seed := oddConstitutionSeed center ligands permutation
  have sourceEq : seed.map Prod.fst = center :: ligands :=
    oddConstitutionSeed_map_fst center ligands permutation ligands_length
  have targetPermutation : (seed.map Prod.snd).Perm (center :: ligands) :=
    oddConstitutionSeed_map_snd_perm center ligands permutation ligands_length permutation_mem
  have sourceNodup : (seed.map Prod.fst).Nodup := by
    rw [sourceEq]
    exact centered_ligands_nodup
  have targetNodup : (seed.map Prod.snd).Nodup :=
    targetPermutation.nodup_iff.mpr centered_ligands_nodup
  have sourceMem : ∀ source ∈ seed.map Prod.fst, source ∈ vertices := by
    intro source sourceMember
    apply mem_oddConstitutionVertices_of_mem_center_ligands
    rw [← sourceEq]
    exact sourceMember
  have targetMem : ∀ pair ∈ seed, pair.2 ∈ vertices := by
    intro pair pairMember
    apply mem_oddConstitutionVertices_of_mem_center_ligands
    apply targetPermutation.mem_iff.mp
    exact List.mem_map.mpr ⟨pair, pairMember, rfl⟩
  exact {
    odd := odd
    partition_preserving := partition_preserving
    vertices_nodup := by
      exact eraseDups_nodup_nat _
    source_coverage := oddConstitutionRemaining_append_sources_perm vertices seed
      (eraseDups_nodup_nat _) sourceNodup sourceMem
    seed_embedding := mol.constitutionPartialEmbedding_of_seed_valid targetNodup targetMem seed_valid }

/-- Every accepted enumerated permutation automatically carries the complete well-formed finite
search frame; the only molecular-frame premise is uniqueness of center plus the four ligands. -/
theorem oddConstitutionPermutationCarrier_of_accepted
    {mol : RawMolecule} {center : Nat} {ligands permutation : List Nat}
    {sameGroup : Nat → Nat → Bool}
    (ligands_length : ligands.length = 4)
    (centered_ligands_nodup : (center :: ligands).Nodup)
    (permutation_mem : permutation ∈ List.permutations (List.range 4))
    (accepted :
      oddConstitutionPermutationAccepted mol center ligands sameGroup permutation = true) :
    OddConstitutionPermutationCarrier mol center ligands sameGroup permutation := by
  have odd : RawMolecule.permutationIsEven permutation = false := by
    cases evenEq : RawMolecule.permutationIsEven permutation with
    | false => rfl
    | true =>
        unfold oddConstitutionPermutationAccepted oddConstitutionPermutationStep at accepted
        rw [evenEq] at accepted
        simp at accepted
  have partitionPreserving :
      (List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) = true := by
    cases groupedEq :
        (List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) with
    | false =>
        unfold oddConstitutionPermutationAccepted oddConstitutionPermutationStep at accepted
        rw [odd, groupedEq] at accepted
        simp at accepted
    | true => rfl
  let seed := oddConstitutionSeed center ligands permutation
  let seedValid := seed.all fun pair =>
    mol.sameConstitutionAtom pair.1 pair.2 &&
      mol.constitutionMappingConsistent mol.localizedMancudeEdges (seed.erase pair) pair.1 pair.2
  have seedValidEq : seedValid = true := by
    cases validEq : seedValid with
    | false =>
        unfold oddConstitutionPermutationAccepted oddConstitutionPermutationStep at accepted
        rw [odd, partitionPreserving] at accepted
        simp only [Bool.not_true, Bool.or_false] at accepted
        rw [show
          ((oddConstitutionSeed center ligands permutation).all fun pair =>
              mol.sameConstitutionAtom pair.1 pair.2 &&
                mol.constitutionMappingConsistent mol.localizedMancudeEdges
                  ((oddConstitutionSeed center ligands permutation).erase pair) pair.1 pair.2) =
            false by exact validEq] at accepted
        simp at accepted
    | true => rfl
  exact oddConstitutionPermutationCarrier_of_seed_valid ligands_length centered_ligands_nodup
    permutation_mem odd partitionPreserving (by simpa [seed, seedValid] using seedValidEq)

/-- An independently witnessed seeded bijection supplies the production seed-validity facts and
therefore the same concrete candidate carrier. -/
theorem oddConstitutionPermutationCarrier_of_automorphism
    {mol : RawMolecule} {center : Nat} {ligands permutation : List Nat}
    {sameGroup : Nat → Nat → Bool}
    (ligands_length : ligands.length = 4)
    (centered_ligands_nodup : (center :: ligands).Nodup)
    (permutation_mem : permutation ∈ List.permutations (List.range 4))
    (odd : RawMolecule.permutationIsEven permutation = false)
    (partition_preserving :
      (List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) = true)
    (automorphism :
      mol.HasSeededConstitutionAutomorphism mol.localizedMancudeEdges
        (oddConstitutionVertices mol center ligands)
        (oddConstitutionSeed center ligands permutation)) :
    OddConstitutionPermutationCarrier mol center ligands sameGroup permutation := by
  let vertices := oddConstitutionVertices mol center ligands
  let seed := oddConstitutionSeed center ligands permutation
  rcases automorphism with ⟨fullMapping, bijection, extendsSeed⟩
  have targetPermutation : (seed.map Prod.snd).Perm (center :: ligands) :=
    oddConstitutionSeed_map_snd_perm center ligands permutation ligands_length permutation_mem
  have targetNodup : (seed.map Prod.snd).Nodup :=
    targetPermutation.nodup_iff.mpr centered_ligands_nodup
  have targetMem : ∀ pair ∈ seed, pair.2 ∈ vertices := by
    intro pair pairMember
    apply mem_oddConstitutionVertices_of_mem_center_ligands
    apply targetPermutation.mem_iff.mp
    exact List.mem_map.mpr ⟨pair, pairMember, rfl⟩
  have seedEmbedding :
      mol.ConstitutionPartialEmbedding mol.localizedMancudeEdges vertices seed := {
    target_nodup := targetNodup
    target_mem := targetMem
    atom_preserving := by
      intro pair pairMem
      exact bijection.atom_preserving pair (extendsSeed pair pairMem)
    bond_preserving := by
      intro leftPair leftMem rightPair rightMem
      exact bijection.bond_preserving leftPair (extendsSeed leftPair leftMem)
        rightPair (extendsSeed rightPair rightMem) }
  exact oddConstitutionPermutationCarrier_of_seed_valid ligands_length centered_ligands_nodup
    permutation_mem odd partition_preserving (by
      simpa [vertices, seed] using seedEmbedding.seed_valid)

/-- On a well-formed candidate carrier, the status-free production acceptance Boolean is exactly
the independent existence of a seeded constitution-preserving bijection. -/
theorem oddConstitutionPermutationAccepted_eq_true_iff
    {mol : RawMolecule} {center : Nat} {ligands : List Nat}
    {sameGroup : Nat → Nat → Bool} {permutation : List Nat}
    (carrier : OddConstitutionPermutationCarrier mol center ligands sameGroup permutation) :
    oddConstitutionPermutationAccepted mol center ligands sameGroup permutation = true ↔
      mol.HasSeededConstitutionAutomorphism mol.localizedMancudeEdges
        (oddConstitutionVertices mol center ligands)
          (oddConstitutionSeed center ligands permutation) := by
  let vertices := oddConstitutionVertices mol center ligands
  let seed := oddConstitutionSeed center ligands permutation
  let remaining := oddConstitutionRemaining vertices seed
  have seedValid := carrier.seed_embedding.seed_valid
  have searchIff := mol.searchConstitutionAutomorphismExact_eq_true_iff
    mol.localizedMancudeEdges vertices remaining seed carrier.vertices_nodup
      carrier.source_coverage carrier.seed_embedding
  have acceptedEq :
      oddConstitutionPermutationAccepted mol center ligands sameGroup permutation =
        mol.searchConstitutionAutomorphismExact mol.localizedMancudeEdges vertices remaining seed := by
    unfold oddConstitutionPermutationAccepted oddConstitutionPermutationStep
    rw [carrier.odd, carrier.partition_preserving]
    simp only [Bool.not_true, Bool.or_false]
    rw [seedValid]
    cases searchResult :
        mol.searchConstitutionAutomorphismExact mol.localizedMancudeEdges vertices remaining seed <;>
      simp
  rw [acceptedEq]
  exact searchIff

/-- The outer odd-topology search is exactly existential enumeration over all four-position
permutations. Early termination at `some true` is extensionally equal to `List.any` of the
status-free acceptance predicate. -/
theorem oddTopologyDecision_eq_some_any
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some ((List.permutations (List.range 4)).any fun permutation =>
        oddConstitutionPermutationAccepted mol node.atom frame.ligands
          (fun left right =>
            rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq)
          permutation) := by
  let sameGroup := fun left right =>
    rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq
  let step := oddConstitutionPermutationStep mol node.atom frame.ligands sameGroup
  let accepted := fun permutation =>
    oddConstitutionPermutationAccepted mol node.atom frame.ligands sameGroup permutation
  have stepEq : ∀ status permutation,
      step (some status) permutation = some (status || accepted permutation) := by
    intro status permutation
    cases status with
    | true => simp [step, oddConstitutionPermutationStep]
    | false =>
        have resultSome : (step (some false) permutation).isSome := by
          apply oddConstitutionPermutationStep_isSome
          rfl
        rcases Option.isSome_iff_exists.mp resultSome with ⟨result, resultEq⟩
        have acceptedEq : accepted permutation = result := by
          simp [accepted, oddConstitutionPermutationAccepted, step, resultEq]
        simpa [acceptedEq] using resultEq
  have foldEq : ∀ (permutations : List (List Nat)) status,
      permutations.foldl step (some status) =
        some (status || permutations.any accepted) := by
    intro permutations
    induction permutations with
    | nil => intro status; simp
    | cons permutation remaining inductionHypothesis =>
        intro status
        simp only [List.foldl_cons, stepEq]
        rw [inductionHypothesis]
        simp [Bool.or_assoc]
  have productionEq :
      hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands sameGroup =
        (List.permutations (List.range 4)).foldl step (some false) := by
    unfold hasOddConstitutionAutomorphismAtCenter
    rw [KernelPermutationEnumeration.kernelPermutations_eq_permutations]
    rw [frame.ligands_length]
    have fourBne : (4 != 4) = false := by decide
    rw [fourBne]
    rfl
  rw [show
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands sameGroup by rfl,
    productionEq]
  simpa [sameGroup, accepted] using
    (foldEq (List.permutations (List.range 4)) false)

/-- A positive topology decision is equivalent to an explicitly accepted member of the exhaustive
four-position permutation list. -/
theorem oddTopologyDecision_eq_true_iff
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some true ↔
      ∃ permutation,
        permutation ∈ List.permutations (List.range 4) ∧
        oddConstitutionPermutationAccepted mol node.atom frame.ligands
          (fun left right =>
            rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq)
          permutation = true := by
  rw [frame.oddTopologyDecision_eq_some_any]
  simp

/-- Exact chemical meaning of a positive Rule-6 topology decision: an enumerated odd permutation
preserves the pre-Rule-6 partition and extends to a constitution-preserving bijection of the full
centered carrier. This includes a possible lone-pair phantom in that carrier. -/
theorem oddTopologyDecision_eq_true_iff_seeded_bijection
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (centered_ligands_nodup : (node.atom :: frame.ligands).Nodup) :
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some true ↔
      ∃ permutation,
        permutation ∈ List.permutations (List.range 4) ∧
        RawMolecule.permutationIsEven permutation = false ∧
        (List.range 4).all (fun index =>
          rule6CompareAt? (mol := mol) state fuel roots index
              (permutation.getD index 0) == some Ordering.eq) = true ∧
        mol.HasSeededConstitutionAutomorphism mol.localizedMancudeEdges
          (oddConstitutionVertices mol node.atom frame.ligands)
          (oddConstitutionSeed node.atom frame.ligands permutation) := by
  rw [frame.oddTopologyDecision_eq_true_iff]
  constructor
  · rintro ⟨permutation, permutationMem, accepted⟩
    let carrier := oddConstitutionPermutationCarrier_of_accepted frame.ligands_length
      centered_ligands_nodup permutationMem accepted
    have automorphism := (oddConstitutionPermutationAccepted_eq_true_iff carrier).mp accepted
    exact ⟨permutation, permutationMem, carrier.odd, carrier.partition_preserving, automorphism⟩
  · rintro ⟨permutation, permutationMem, odd, partitionPreserving, automorphism⟩
    let carrier : OddConstitutionPermutationCarrier mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq)
        permutation :=
      oddConstitutionPermutationCarrier_of_automorphism
        (sameGroup := fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq)
        frame.ligands_length centered_ligands_nodup permutationMem odd partitionPreserving
        automorphism
    exact ⟨permutation, permutationMem,
      (oddConstitutionPermutationAccepted_eq_true_iff carrier).mpr automorphism⟩

/-- Certified written-neighbour exactness discharges the last carrier-uniqueness premise, giving
the topology Boolean's independent constitutional-bijection meaning directly on the production
Rule-6 frame. -/
theorem oddTopologyDecision_eq_true_iff_seeded_bijection_of_writtenNeighborExact
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) :
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some true ↔
      ∃ permutation,
        permutation ∈ List.permutations (List.range 4) ∧
        RawMolecule.permutationIsEven permutation = false ∧
        (List.range 4).all (fun index =>
          rule6CompareAt? (mol := mol) state fuel roots index
              (permutation.getD index 0) == some Ordering.eq) = true ∧
        mol.HasSeededConstitutionAutomorphism mol.localizedMancudeEdges
          (oddConstitutionVertices mol node.atom frame.ligands)
          (oddConstitutionSeed node.atom frame.ligands permutation) := by
  apply frame.oddTopologyDecision_eq_true_iff_seeded_bijection
  rw [frame.ligands_eq]
  exact centered_ligandsWithLonePair_nodup mol writtenExact node.atom frame.spec frame.atom_spec

/-- The independent mathematical proposition decided by the production Rule-6 topology search.
It asks for an explicitly enumerated odd permutation that preserves the complete pre-Rule-6
partition and extends to a constitution-preserving bijection of the full centered carrier. -/
def HasOddPartitionPreservingConstitutionAutomorphism
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) : Prop :=
  ∃ permutation,
    permutation ∈ List.permutations (List.range 4) ∧
    RawMolecule.permutationIsEven permutation = false ∧
    (List.range 4).all (fun index =>
      rule6CompareAt? (mol := mol) state fuel roots index
          (permutation.getD index 0) == some Ordering.eq) = true ∧
    mol.HasSeededConstitutionAutomorphism mol.localizedMancudeEdges
      (oddConstitutionVertices mol node.atom frame.ligands)
      (oddConstitutionSeed node.atom frame.ligands permutation)

/-- On a chemically exact written-neighbour representation, the production positive result is
exactly the independent odd partition-preserving constitutional-automorphism proposition. -/
theorem oddTopologyDecision_eq_true_iff_hasOddPartitionPreservingAutomorphism
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) :
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some true ↔
      frame.HasOddPartitionPreservingConstitutionAutomorphism := by
  simpa [HasOddPartitionPreservingConstitutionAutomorphism] using
    frame.oddTopologyDecision_eq_true_iff_seeded_bijection_of_writtenNeighborExact writtenExact

/-- On an exact four-ligand frame the constitutional-topology search is total: it returns either
`some false` or `some true`, never the malformed-frame result `none`.  This theorem does not choose
which Boolean is chemically correct. -/
theorem oddTopologyDecision_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∃ odd,
      hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some odd := by
  let sameGroup := fun left right =>
    rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq
  let mancudeEdges := mol.localizedMancudeEdges
  let vertices := oddConstitutionVertices mol node.atom frame.ligands
  let step := fun (status : Option Bool) permutation =>
    if status == some true || RawMolecule.permutationIsEven permutation ||
        !(List.range 4).all (fun index => sameGroup index (permutation.getD index 0)) then
      status
    else
      let ligandMapping := (List.range 4).map fun index =>
        (frame.ligands.getD index 0,
          frame.ligands.getD (permutation.getD index 0) 0)
      let seed := (node.atom, node.atom) :: ligandMapping
      let seedValid := seed.all fun pair =>
        mol.sameConstitutionAtom pair.1 pair.2 &&
          mol.constitutionMappingConsistent mancudeEdges (seed.erase pair) pair.1 pair.2
      if !seedValid then status else
        let remaining := vertices.filter fun atom => !(seed.map Prod.fst).contains atom
        if mol.searchConstitutionAutomorphismExact mancudeEdges vertices remaining seed then
          some true
        else status
  have stepSome : ∀ status permutation, status.isSome → (step status permutation).isSome := by
    intro status permutation statusSome
    simp only [step]
    split
    · exact statusSome
    · split
      · exact statusSome
      · split
        · rfl
        · exact statusSome
  have foldSome : ∀ (permutations : List (List Nat)) (status : Option Bool), status.isSome →
      (permutations.foldl step status).isSome := by
    intro permutations
    induction permutations with
    | nil => intro status statusSome; exact statusSome
    | cons permutation remaining inductionHypothesis =>
        intro status statusSome
        simp only [List.foldl_cons]
        exact inductionHypothesis (step status permutation)
          (stepSome status permutation statusSome)
  have resultSome :
      ((List.permutations (List.range 4)).foldl step (some false)).isSome :=
    foldSome (List.permutations (List.range 4)) (some false) rfl
  rcases Option.isSome_iff_exists.mp resultSome with ⟨odd, resultEq⟩
  refine ⟨odd, ?_⟩
  simpa [hasOddConstitutionAutomorphismAtCenter,
    KernelPermutationEnumeration.kernelPermutations_eq_permutations, frame.ligands_length,
    sameGroup, mancudeEdges, vertices, step] using resultEq

/-- The negative production result has an equally exact meaning: no odd permutation preserving
the pre-Rule-6 partition extends to a constitutional automorphism.  Thus a chemically meaningful
negative result is a theorem, not a Boolean premise that downstream users must trust. -/
theorem oddTopologyDecision_eq_false_iff_no_hasOddPartitionPreservingAutomorphism
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) :
    hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
        (fun left right =>
          rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some false ↔
      ¬ frame.HasOddPartitionPreservingConstitutionAutomorphism := by
  have positive :=
    frame.oddTopologyDecision_eq_true_iff_hasOddPartitionPreservingAutomorphism writtenExact
  constructor
  · intro resultFalse hasOdd
    have resultTrue := positive.mpr hasOdd
    rw [resultFalse] at resultTrue
    contradiction
  · intro noOdd
    rcases frame.oddTopologyDecision_exists with ⟨odd, result⟩
    cases odd with
    | false => exact result
    | true => exact False.elim (noOdd (positive.mp result))

/-- Once the chemically substantive odd-topology rejection is supplied, structural branching
support constructs the complete production `Rule6FrameCertificate`; all of its former sort,
adjacency, and sixteen-pair partition fields are theorems rather than assumptions. -/
def toRule6FrameCertificateOfOddFalse
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (comparisons : Rule6InitialAdjacentDerivation (mol := mol) state fuel roots sorted adjacent)
    (adjacent_not_lt : some Ordering.lt ∉ adjacent)
    (partition : Rule6InitialCompletePartitionCertificate (mol := mol) state fuel roots sorted
      adjacent)
    (odd_false : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some false) :
    Rule6FrameCertificate (mol := mol) state fuel node roots where
  spec := frame.spec
  parity := frame.parity
  ligands := frame.ligands
  sorted := sorted
  adjacent := adjacent
  groupCount := rule6GroupCount adjacent
  atom_spec := frame.atom_spec
  tetrahedral := frame.tetrahedral
  ligands_eq := frame.ligands_eq
  ligands_length := frame.ligands_length
  roots_length := frame.roots_length
  ranking := sorting
  comparisons := comparisons
  adjacent_not_lt := adjacent_not_lt
  partition := partition
  groupCount_eq := rfl
  odd_false := odd_false

/-- Negative odd topology is now the only additional premise needed to construct a complete
production Rule-6 frame from the structural descriptor-bearing branching frame. -/
theorem rule6FrameCertificate_nonempty_of_odd_false
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (odd_false : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
        some false) :
    Nonempty (Rule6FrameCertificate (mol := mol) state fuel node roots) := by
  rcases frame.initial_four_position_complete_partition_exists with
    ⟨sorted, adjacent, sorting, comparisons, adjacentNotLt, ⟨partition⟩⟩
  exact ⟨frame.toRule6FrameCertificateOfOddFalse sorting comparisons adjacentNotLt partition
    odd_false⟩

/-- An independently stated absence of an odd partition-preserving constitutional automorphism
constructs the complete production Rule-6 frame.  No unproved equality about the executable
topology search remains at this boundary. -/
theorem rule6FrameCertificate_nonempty_of_no_hasOddPartitionPreservingAutomorphism
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact)
    (noOdd : ¬ frame.HasOddPartitionPreservingConstitutionAutomorphism) :
    Nonempty (Rule6FrameCertificate (mol := mol) state fuel node roots) := by
  apply frame.rule6FrameCertificate_nonempty_of_odd_false
  exact
    (frame.oddTopologyDecision_eq_false_iff_no_hasOddPartitionPreservingAutomorphism
      writtenExact).mpr noOdd

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
