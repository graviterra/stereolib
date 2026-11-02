import TetraStereo.OneCenter.LocalizedTrackedSortSourcePairFidelity
import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RawMolecule












































/-! ## Independent source pair count -/

/-- Independent source count of unordered enantiomorphic pairs, restated only to fix the
direction used below: `rank` increases with CIP priority, and the actual tracked occurrence sort
emits the highest-priority cursor first, so a priority-ordered cursor list is strictly decreasing
in `rank`.

The six terms enumerate the six unordered pairs of four ligand positions exactly once; the
definition does not mention any sort, comparator, or comparison history. -/
theorem sourceCount_eq_adjacent_of_descending
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2) :
    sourceEnantiomorphicPairCount enantiomorphic =
      (if enantiomorphic 0 1 then 1 else 0) +
      (if enantiomorphic 1 2 then 1 else 0) +
      (if enantiomorphic 2 3 then 1 else 0) := by
  have h02 : ¬ enantiomorphic 0 2 := by
    intro h
    exact source.convex 0 2 1 h (Or.inr ⟨h21, h10⟩)
  have h03 : ¬ enantiomorphic 0 3 := by
    intro h
    exact source.convex 0 3 1 h (Or.inr ⟨lt_trans h32 h21, h10⟩)
  have h13 : ¬ enantiomorphic 1 3 := by
    intro h
    exact source.convex 1 3 2 h (Or.inr ⟨h32, h21⟩)
  unfold sourceEnantiomorphicPairCount
  by_cases e01 : enantiomorphic 0 1 <;>
    by_cases e12 : enantiomorphic 1 2 <;>
    by_cases e23 : enantiomorphic 2 3 <;>
    simp [e01, e12, e23, h02, h03, h13]

/-- Three priority-ordered positions admit at most two enantiomorphic pairs: the matching field
forbids both the pair `(0,1)` and the pair `(1,2)` (or `(1,2)` and `(2,3)`) simultaneously. -/
theorem sourceCount_le_two_of_descending
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2) :
    sourceEnantiomorphicPairCount enantiomorphic ≤ 2 := by
  rw [sourceCount_eq_adjacent_of_descending source h10 h21 h32]
  by_cases e01 : enantiomorphic 0 1
  · by_cases e12 : enantiomorphic 1 2
    · have hsame : (0 : Fin 4) = 2 :=
        source.matching 1 0 2 (source.symmetric 0 1 e01) e12
      exact absurd hsame (by decide)
    · by_cases e23 : enantiomorphic 2 3 <;> simp [e01, e12, e23]
  · by_cases e12 : enantiomorphic 1 2 <;>
      by_cases e23 : enantiomorphic 2 3 <;>
      simp [e01, e12, e23]

/-- The source count is odd exactly when the four ligands carry exactly one enantiomorphic pair. -/
theorem sourceCount_odd_iff_one_of_descending
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2) :
    sourceEnantiomorphicPairCount enantiomorphic % 2 = 1 ↔
      sourceEnantiomorphicPairCount enantiomorphic = 1 := by
  have hle := sourceCount_le_two_of_descending source h10 h21 h32
  have hcases : sourceEnantiomorphicPairCount enantiomorphic = 0 ∨
      sourceEnantiomorphicPairCount enantiomorphic = 1 ∨
      sourceEnantiomorphicPairCount enantiomorphic = 2 := by omega
  rcases hcases with h | h | h <;> rw [h]
  all_goals decide

/-- The raw evaluators' uppercase test (even pseudo count) is false exactly when the source has
exactly one enantiomorphic pair. -/
theorem sourceCount_uppercase_false_iff_one_of_descending
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2) :
    (sourceEnantiomorphicPairCount enantiomorphic % 2 == 0) = false ↔
      sourceEnantiomorphicPairCount enantiomorphic = 1 := by
  have hle := sourceCount_le_two_of_descending source h10 h21 h32
  have hcases : sourceEnantiomorphicPairCount enantiomorphic = 0 ∨
      sourceEnantiomorphicPairCount enantiomorphic = 1 ∨
      sourceEnantiomorphicPairCount enantiomorphic = 2 := by omega
  rcases hcases with h | h | h <;> rw [h]
  all_goals decide







theorem classifyTetrahedralRSPseudo_sourceCount_iff
    {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (descriptor : RS) :
    classifyTetrahedralRSPseudo descriptor (sourceEnantiomorphicPairCount enantiomorphic) =
        .pseudoasymmetric (pseudoRSOfRS descriptor) ↔
      sourceEnantiomorphicPairCount enantiomorphic = 1 := by
  unfold classifyTetrahedralRSPseudo
  by_cases h : sourceEnantiomorphicPairCount enantiomorphic = 1 <;> simp [h]

/-! ## The exact final adjacent trace -/

/-- One comparison required by source agreement: strict source rank ordering and the independent
enantiomorphism bit.  The ordering component is `compare` of the two source ranks; it is not a
desired sort outcome. -/
def rawTraceDecision (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic] (first second : Fin 4) : OccurrenceComparison :=
  { ordering := compare (rank first) (rank second)
    pseudo := decide (enantiomorphic first second) }

/-- The three final adjacent decisions on a four-cursor priority-ordered list. -/
def rawAdjacentDecisionTrace (rank : Fin 4 → ℕ)
    (enantiomorphic : Fin 4 → Fin 4 → Prop) [DecidableRel enantiomorphic] :
    List OccurrenceComparison :=
  [rawTraceDecision rank enantiomorphic 0 1,
   rawTraceDecision rank enantiomorphic 1 2,
   rawTraceDecision rank enantiomorphic 2 3]

/-- The same three decisions with their actual cursor endpoints, in the shape produced by
`FrameRuntime.adjacent?`. -/
def rawAdjacentPairs (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (cursors : Fin 4 → CanonicalRerootCursor)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic] : List (OccurrenceComparedPair mol state fuel) :=
  [ { left := cursors 0, right := cursors 1,
      decision := rawTraceDecision rank enantiomorphic 0 1 },
    { left := cursors 1, right := cursors 2,
      decision := rawTraceDecision rank enantiomorphic 1 2 },
    { left := cursors 2, right := cursors 3,
      decision := rawTraceDecision rank enantiomorphic 2 3 } ]

/-- Actual-comparator agreement for the three final adjacent pairs of a four-position embedding.

The comparator is the actual production comparator under test.  Each ordered pair must succeed,
return the comparison of the independent source ranks, and return the independent enantiomorphism
relation as its `pseudo` flag.  This is the only comparator hypothesis; no sorted list, desired
count, or pair placement is included. -/
def RawAdjacentComparatorAgrees
    (compareAt : Fin 4 → Fin 4 → Option OccurrenceComparison)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic] : Prop :=
  (compareAt 0 1 = some (rawTraceDecision rank enantiomorphic 0 1)) ∧
  (compareAt 1 2 = some (rawTraceDecision rank enantiomorphic 1 2)) ∧
  (compareAt 2 3 = some (rawTraceDecision rank enantiomorphic 2 3))

/-- A four-position embedding has pairwise distinct entries.  This records the "four distinct
ligand positions" part of the chemical model; the parity argument itself is combinatorial and
does not consume it. -/
theorem cursorEmbedding_pairwise_ne
    {cursors : Fin 4 → CanonicalRerootCursor} (distinct : Function.Injective cursors) :
    cursors 0 ≠ cursors 1 ∧ cursors 1 ≠ cursors 2 ∧ cursors 2 ≠ cursors 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro equal
    exact (by decide : (0 : Fin 4) ≠ 1) (distinct equal)
  · intro equal
    exact (by decide : (1 : Fin 4) ≠ 2) (distinct equal)
  · intro equal
    exact (by decide : (2 : Fin 4) ≠ 3) (distinct equal)

theorem rawAdjacentPairs_decisions
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (cursors : Fin 4 → CanonicalRerootCursor)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic] :
    (rawAdjacentPairs mol state fuel cursors rank enantiomorphic).map
        (fun pair => pair.decision) = rawAdjacentDecisionTrace rank enantiomorphic := by
  simp [rawAdjacentPairs, rawAdjacentDecisionTrace]

/-- The three trace decisions are strictly ordered, hence pass the raw evaluators' no-tie gate. -/
theorem rawAdjacentDecisionTrace_all_strict
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2) :
    (rawAdjacentDecisionTrace rank enantiomorphic).all
        (fun decision => decision.ordering != Ordering.eq) = true := by
  have c01 : compare (rank 0) (rank 1) = Ordering.gt := Nat.compare_eq_gt.mpr h10
  have c12 : compare (rank 1) (rank 2) = Ordering.gt := Nat.compare_eq_gt.mpr h21
  have c23 : compare (rank 2) (rank 3) = Ordering.gt := Nat.compare_eq_gt.mpr h32
  unfold rawAdjacentDecisionTrace rawTraceDecision
  simp [c01, c12, c23]

/-- Counting the `pseudo` decisions of the final adjacent trace equals the independent six-pair
source count.  This is the combinatorial core: convexity moves every source pair into one of the
three adjacent slots. -/
theorem rawAdjacentDecisionTrace_pseudoCount
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2) :
    ((rawAdjacentDecisionTrace rank enantiomorphic).filter
        (fun decision => decision.pseudo)).length =
      sourceEnantiomorphicPairCount enantiomorphic := by
  have h02 : ¬ enantiomorphic 0 2 := by
    intro h
    exact source.convex 0 2 1 h (Or.inr ⟨h21, h10⟩)
  have h03 : ¬ enantiomorphic 0 3 := by
    intro h
    exact source.convex 0 3 1 h (Or.inr ⟨lt_trans h32 h21, h10⟩)
  have h13 : ¬ enantiomorphic 1 3 := by
    intro h
    exact source.convex 1 3 2 h (Or.inr ⟨h32, h21⟩)
  unfold rawAdjacentDecisionTrace rawTraceDecision sourceEnantiomorphicPairCount
  by_cases e01 : enantiomorphic 0 1 <;>
    by_cases e12 : enantiomorphic 1 2 <;>
    by_cases e23 : enantiomorphic 2 3 <;>
    simp [e01, e12, e23, h02, h03, h13]

/-! ## The actual legacy adjacent traversal -/

/-- The actual legacy raw adjacent traversal on the four-cursor priority list succeeds and
returns exactly the source trace.  Only the actual comparator equations are used. -/
theorem compareOccurrenceAdjacentPairsAuthoritative?_four_of_agrees
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (cursors : Fin 4 → CanonicalRerootCursor)
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => compareOccurrenceBranchesComplete? mol state fuel (cursors i) (cursors j))
      rank enantiomorphic) :
    compareOccurrenceAdjacentPairsAuthoritative? mol state fuel
        [cursors 0, cursors 1, cursors 2, cursors 3] =
      some (rawAdjacentDecisionTrace rank enantiomorphic) := by
  obtain ⟨h01, h12, h23⟩ := agrees
  simp [compareOccurrenceAdjacentPairsAuthoritative?, rawAdjacentDecisionTrace, rawTraceDecision,
    h01, h12, h23]

/-- The actual framed adjacent traversal on the four-cursor priority list succeeds and returns
exactly the source trace, with both cursor endpoints retained. -/
theorem frameRuntime_adjacent?_four_of_agrees
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (cursors : Fin 4 → CanonicalRerootCursor)
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => FrameRuntime.decisionComplete? mol profile true state fuel
        (cursors i) (cursors j)) rank enantiomorphic) :
    FrameRuntime.adjacent? mol profile true state fuel
        [cursors 0, cursors 1, cursors 2, cursors 3] =
      some (rawAdjacentPairs mol state fuel cursors rank enantiomorphic) := by
  obtain ⟨h01, h12, h23⟩ := agrees
  simp [FrameRuntime.adjacent?, FramedCompleteRuntime.adjacentComplete?, rawAdjacentPairs,
    rawTraceDecision, h01, h12, h23]

/-- **Actual legacy adjacency output and count.**  The actual function succeeds and the number of
`pseudo` decisions in its exact output equals the independent six-pair source count. -/
theorem compareOccurrenceAdjacentPairsAuthoritative?_four_count
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (cursors : Fin 4 → CanonicalRerootCursor)
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2)
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => compareOccurrenceBranchesComplete? mol state fuel (cursors i) (cursors j))
      rank enantiomorphic) :
    ∃ decisions : List OccurrenceComparison,
      compareOccurrenceAdjacentPairsAuthoritative? mol state fuel
          [cursors 0, cursors 1, cursors 2, cursors 3] = some decisions ∧
      (decisions.filter fun decision => decision.pseudo).length =
        sourceEnantiomorphicPairCount enantiomorphic := by
  refine ⟨rawAdjacentDecisionTrace rank enantiomorphic, ?_, ?_⟩
  · exact compareOccurrenceAdjacentPairsAuthoritative?_four_of_agrees mol state fuel cursors agrees
  · exact rawAdjacentDecisionTrace_pseudoCount source h10 h21 h32

/-- **Actual framed adjacency output and count.**  The actual function succeeds and the number of
`pseudo` decisions among its exact final pairs equals the independent six-pair source count. -/
theorem frameRuntime_adjacent?_four_count
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (cursors : Fin 4 → CanonicalRerootCursor)
    {rank : Fin 4 → ℕ} {enantiomorphic : Fin 4 → Fin 4 → Prop}
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2)
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => FrameRuntime.decisionComplete? mol profile true state fuel
        (cursors i) (cursors j)) rank enantiomorphic) :
    ∃ pairs : List (OccurrenceComparedPair mol state fuel),
      FrameRuntime.adjacent? mol profile true state fuel
          [cursors 0, cursors 1, cursors 2, cursors 3] = some pairs ∧
      ((pairs.map (fun pair => pair.decision)).filter
          (fun decision => decision.pseudo)).length =
        sourceEnantiomorphicPairCount enantiomorphic := by
  refine ⟨rawAdjacentPairs mol state fuel cursors rank enantiomorphic, ?_, ?_⟩
  · exact frameRuntime_adjacent?_four_of_agrees mol profile state fuel cursors agrees
  · rw [rawAdjacentPairs_decisions]
    exact rawAdjacentDecisionTrace_pseudoCount source h10 h21 h32

/-! ## Connecting the actual legacy fact evaluator -/

/-- Evaluate the actual legacy fact evaluator once every pipeline component, including the
actual adjacent output, is fixed.  This is a statement about the production code, not a
replacement callback: the decisions are exactly what
`compareOccurrenceAdjacentPairsAuthoritative?` returned. -/
theorem legacyOccurrenceFactAuthoritative?_eq_some_of_decisions
    {mol : RawMolecule} {fuel : ℕ} {state : OccurrenceAuxState}
    {node : RawMolecule.CanonicalBranchNode}
    {spec : AtomSpec} {parity : TetrahedralInputParity}
    {roots : List CanonicalRerootCursor}
    {sorted : List CanonicalRerootCursor × ℕ} {positions : List ℕ}
    {decisions : List OccurrenceComparison}
    (hatom : mol.atomAt? node.atom = some spec)
    (hparity : spec.tetrahedral? = some parity)
    (hframe : occurrenceLigandFrame? mol node = some roots)
    (hsort : sortOccurrencesTrackedAuthoritative? mol state fuel roots = some sorted)
    (hpositions : (sorted.1.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (hdecisions : compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted.1 =
      some decisions)
    (hstrict : decisions.all (fun decision => decision.ordering != Ordering.eq) = true) :
    legacyOccurrenceFactAuthoritative? mol fuel state node =
      some { key := canonicalOccurrenceKey node
             atom := node.atom
             descriptor := RawMolecule.descriptorOfParity parity
               (RawMolecule.permutationIsEven positions)
             uppercase := (decisions.filter fun decision => decision.pseudo).length % 2 == 0
             priorityPositions := positions } := by
  have allStrict := List.all_eq_true.mp hstrict
  simp [legacyOccurrenceFactAuthoritative?, hatom, hparity, hframe, hsort, hpositions,
    hdecisions]
  intro decision member
  simpa using allStrict decision member

/-- **Actual legacy final-adjacent source fidelity.**

For four distinct cursors emitted by the actual tracked occurrence sort in strict source-priority
order, if the actual legacy comparator agrees with the independent source on the three final
adjacent pairs, then the actual raw evaluator emits the record whose `uppercase` field is the
parity of the independent six-pair source count.

The sorted-list equation `hlist` is an explicit premise.  Deriving the raw tracked sort's order
from the comparator trace is the remaining bridge described in the module report. -/
theorem legacyOccurrenceFactAuthoritative?_uppercase_of_source
    {mol : RawMolecule} {fuel : ℕ} {state : OccurrenceAuxState}
    {node : RawMolecule.CanonicalBranchNode}
    {spec : AtomSpec} {parity : TetrahedralInputParity}
    {roots : List CanonicalRerootCursor}
    {sorted : List CanonicalRerootCursor × ℕ} {positions : List ℕ}
    (cursors : Fin 4 → CanonicalRerootCursor)
    (distinct : Function.Injective cursors)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2)
    (hatom : mol.atomAt? node.atom = some spec)
    (hparity : spec.tetrahedral? = some parity)
    (hframe : occurrenceLigandFrame? mol node = some roots)
    (hsort : sortOccurrencesTrackedAuthoritative? mol state fuel roots = some sorted)
    (hlist : sorted.1 = [cursors 0, cursors 1, cursors 2, cursors 3])
    (hpositions : (sorted.1.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => compareOccurrenceBranchesComplete? mol state fuel (cursors i) (cursors j))
      rank enantiomorphic) :
    legacyOccurrenceFactAuthoritative? mol fuel state node =
      some { key := canonicalOccurrenceKey node
             atom := node.atom
             descriptor := RawMolecule.descriptorOfParity parity
               (RawMolecule.permutationIsEven positions)
             uppercase := (sourceEnantiomorphicPairCount enantiomorphic % 2 == 0)
             priorityPositions := positions } := by
  have hpairwise := cursorEmbedding_pairwise_ne distinct
  have hadj : compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted.1 =
      some (rawAdjacentDecisionTrace rank enantiomorphic) := by
    rw [hlist]
    exact compareOccurrenceAdjacentPairsAuthoritative?_four_of_agrees mol state fuel cursors agrees
  have hstrict := rawAdjacentDecisionTrace_all_strict (rank := rank)
    (enantiomorphic := enantiomorphic) h10 h21 h32
  have hcount := rawAdjacentDecisionTrace_pseudoCount (source := source) h10 h21 h32
  rw [legacyOccurrenceFactAuthoritative?_eq_some_of_decisions (decisions :=
    rawAdjacentDecisionTrace rank enantiomorphic) hatom hparity hframe hsort hpositions hadj
    hstrict, hcount]

/-- **Actual legacy final-adjacent source fidelity, observed-fact form.** -/
theorem legacyOccurrenceFactAuthoritative?_fact_uppercase_of_source
    {mol : RawMolecule} {fuel : ℕ} {state : OccurrenceAuxState}
    {node : RawMolecule.CanonicalBranchNode}
    {spec : AtomSpec} {parity : TetrahedralInputParity}
    {roots : List CanonicalRerootCursor}
    {sorted : List CanonicalRerootCursor × ℕ} {positions : List ℕ}
    {fact : OccurrenceAuxFact}
    (cursors : Fin 4 → CanonicalRerootCursor)
    (distinct : Function.Injective cursors)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2)
    (hatom : mol.atomAt? node.atom = some spec)
    (hparity : spec.tetrahedral? = some parity)
    (hframe : occurrenceLigandFrame? mol node = some roots)
    (hsort : sortOccurrencesTrackedAuthoritative? mol state fuel roots = some sorted)
    (hlist : sorted.1 = [cursors 0, cursors 1, cursors 2, cursors 3])
    (hpositions : (sorted.1.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => compareOccurrenceBranchesComplete? mol state fuel (cursors i) (cursors j))
      rank enantiomorphic)
    (fact_eq : legacyOccurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.uppercase = (sourceEnantiomorphicPairCount enantiomorphic % 2 == 0) := by
  have hpairwise := cursorEmbedding_pairwise_ne distinct
  have hrecord := legacyOccurrenceFactAuthoritative?_uppercase_of_source cursors distinct rank
    enantiomorphic source h10 h21 h32 hatom hparity hframe hsort hlist hpositions agrees
  rw [fact_eq] at hrecord
  have hfact : fact =
      { key := canonicalOccurrenceKey node
        atom := node.atom
        descriptor := RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions)
        uppercase := (sourceEnantiomorphicPairCount enantiomorphic % 2 == 0)
        priorityPositions := positions } := Option.some.inj hrecord
  rw [hfact]

/-! ## Connecting the actual framed fact evaluator -/

/-- Evaluate the actual framed fact evaluator once every pipeline component, including the
actual `FrameRuntime.adjacent?` output, is fixed. -/
theorem framedOccurrenceFactAuthoritative?_eq_some_of_decisions
    {mol : RawMolecule} {fuel : ℕ} {state : OccurrenceAuxState}
    {node : RawMolecule.CanonicalBranchNode} {profile : FrameRuntime.Profile}
    {spec : AtomSpec} {parity : TetrahedralInputParity}
    {roots : List CanonicalRerootCursor}
    {sorted : List CanonicalRerootCursor × ℕ} {positions : List ℕ}
    {decisions : List OccurrenceComparison}
    (hprofile : FrameRuntime.profile? mol node = some profile)
    (hatom : mol.atomAt? node.atom = some spec)
    (hparity : spec.tetrahedral? = some parity)
    (hframe : occurrenceLigandFrame? mol node = some roots)
    (hsort : FrameRuntime.trackedSort? mol profile true state fuel roots = some sorted)
    (hpositions : (sorted.1.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (hdecisions : (FrameRuntime.adjacent? mol profile true state fuel sorted.1).map
        (fun pairs => pairs.map OccurrenceComparedPair.decision) = some decisions)
    (hstrict : decisions.all (fun decision => decision.ordering != Ordering.eq) = true) :
    framedOccurrenceFactAuthoritative? mol fuel state node =
      some { key := canonicalOccurrenceKey node
             atom := node.atom
             descriptor := RawMolecule.descriptorOfParity parity
               (RawMolecule.permutationIsEven positions)
             uppercase := (decisions.filter fun decision => decision.pseudo).length % 2 == 0
             priorityPositions := positions } := by
  have allStrict := List.all_eq_true.mp hstrict
  simp [framedOccurrenceFactAuthoritative?, hprofile, hatom, hparity, hframe, hsort,
    hpositions, hdecisions]
  intro decision member
  simpa using allStrict decision member

/-- **Actual framed final-adjacent source fidelity.**

The framed evaluator's actual `FrameRuntime.trackedSort?` and actual `FrameRuntime.adjacent?` are
used.  As in the legacy case, the sorted-list equation is an explicit premise and comparator
agreement is a separate hypothesis. -/
theorem framedOccurrenceFactAuthoritative?_uppercase_of_source
    {mol : RawMolecule} {fuel : ℕ} {state : OccurrenceAuxState}
    {node : RawMolecule.CanonicalBranchNode} {profile : FrameRuntime.Profile}
    {spec : AtomSpec} {parity : TetrahedralInputParity}
    {roots : List CanonicalRerootCursor}
    {sorted : List CanonicalRerootCursor × ℕ} {positions : List ℕ}
    (cursors : Fin 4 → CanonicalRerootCursor)
    (distinct : Function.Injective cursors)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2)
    (hprofile : FrameRuntime.profile? mol node = some profile)
    (hatom : mol.atomAt? node.atom = some spec)
    (hparity : spec.tetrahedral? = some parity)
    (hframe : occurrenceLigandFrame? mol node = some roots)
    (hsort : FrameRuntime.trackedSort? mol profile true state fuel roots = some sorted)
    (hlist : sorted.1 = [cursors 0, cursors 1, cursors 2, cursors 3])
    (hpositions : (sorted.1.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => FrameRuntime.decisionComplete? mol profile true state fuel
        (cursors i) (cursors j)) rank enantiomorphic) :
    framedOccurrenceFactAuthoritative? mol fuel state node =
      some { key := canonicalOccurrenceKey node
             atom := node.atom
             descriptor := RawMolecule.descriptorOfParity parity
               (RawMolecule.permutationIsEven positions)
             uppercase := (sourceEnantiomorphicPairCount enantiomorphic % 2 == 0)
             priorityPositions := positions } := by
  have hpairwise := cursorEmbedding_pairwise_ne distinct
  have hadj : FrameRuntime.adjacent? mol profile true state fuel sorted.1 =
      some (rawAdjacentPairs mol state fuel cursors rank enantiomorphic) := by
    rw [hlist]
    exact frameRuntime_adjacent?_four_of_agrees mol profile state fuel cursors agrees
  have hdecisions : (FrameRuntime.adjacent? mol profile true state fuel sorted.1).map
      (fun pairs => pairs.map OccurrenceComparedPair.decision) =
        some (rawAdjacentDecisionTrace rank enantiomorphic) := by
    simp [hadj, rawAdjacentPairs_decisions]
  have hstrict := rawAdjacentDecisionTrace_all_strict (rank := rank)
    (enantiomorphic := enantiomorphic) h10 h21 h32
  have hcount := rawAdjacentDecisionTrace_pseudoCount (source := source) h10 h21 h32
  rw [framedOccurrenceFactAuthoritative?_eq_some_of_decisions (decisions :=
    rawAdjacentDecisionTrace rank enantiomorphic) hprofile hatom hparity hframe hsort
    hpositions hdecisions hstrict, hcount]

/-- **Actual framed final-adjacent source fidelity, observed-fact form.** -/
theorem framedOccurrenceFactAuthoritative?_fact_uppercase_of_source
    {mol : RawMolecule} {fuel : ℕ} {state : OccurrenceAuxState}
    {node : RawMolecule.CanonicalBranchNode} {profile : FrameRuntime.Profile}
    {spec : AtomSpec} {parity : TetrahedralInputParity}
    {roots : List CanonicalRerootCursor}
    {sorted : List CanonicalRerootCursor × ℕ} {positions : List ℕ}
    {fact : OccurrenceAuxFact}
    (cursors : Fin 4 → CanonicalRerootCursor)
    (distinct : Function.Injective cursors)
    (rank : Fin 4 → ℕ) (enantiomorphic : Fin 4 → Fin 4 → Prop)
    [DecidableRel enantiomorphic]
    (source : SourceEnantiomorphicPriorityStructure rank enantiomorphic)
    (h10 : rank 1 < rank 0) (h21 : rank 2 < rank 1) (h32 : rank 3 < rank 2)
    (hprofile : FrameRuntime.profile? mol node = some profile)
    (hatom : mol.atomAt? node.atom = some spec)
    (hparity : spec.tetrahedral? = some parity)
    (hframe : occurrenceLigandFrame? mol node = some roots)
    (hsort : FrameRuntime.trackedSort? mol profile true state fuel roots = some sorted)
    (hlist : sorted.1 = [cursors 0, cursors 1, cursors 2, cursors 3])
    (hpositions : (sorted.1.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions)
    (agrees : RawAdjacentComparatorAgrees
      (fun i j => FrameRuntime.decisionComplete? mol profile true state fuel
        (cursors i) (cursors j)) rank enantiomorphic)
    (fact_eq : framedOccurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.uppercase = (sourceEnantiomorphicPairCount enantiomorphic % 2 == 0) := by
  have hpairwise := cursorEmbedding_pairwise_ne distinct
  have hrecord := framedOccurrenceFactAuthoritative?_uppercase_of_source cursors distinct rank
    enantiomorphic source h10 h21 h32 hprofile hatom hparity hframe hsort hlist hpositions
    agrees
  rw [fact_eq] at hrecord
  have hfact : fact =
      { key := canonicalOccurrenceKey node
        atom := node.atom
        descriptor := RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions)
        uppercase := (sourceEnantiomorphicPairCount enantiomorphic % 2 == 0)
        priorityPositions := positions } := Option.some.inj hrecord
  rw [hfact]

end TetraStereo.OneCenter

/-! ## Kernel-authority exports -/

assert_kernel_only TetraStereo.OneCenter.sourceCount_eq_adjacent_of_descending
assert_kernel_only TetraStereo.OneCenter.sourceCount_le_two_of_descending
assert_kernel_only TetraStereo.OneCenter.sourceCount_odd_iff_one_of_descending
assert_kernel_only TetraStereo.OneCenter.sourceCount_uppercase_false_iff_one_of_descending
assert_kernel_only TetraStereo.OneCenter.classifyTetrahedralRSPseudo_sourceCount_iff
assert_kernel_only TetraStereo.OneCenter.rawTraceDecision
assert_kernel_only TetraStereo.OneCenter.rawAdjacentDecisionTrace
assert_kernel_only TetraStereo.OneCenter.rawAdjacentPairs
assert_kernel_only TetraStereo.OneCenter.RawAdjacentComparatorAgrees
assert_kernel_only TetraStereo.OneCenter.rawAdjacentPairs_decisions
assert_kernel_only TetraStereo.OneCenter.rawAdjacentDecisionTrace_all_strict
assert_kernel_only TetraStereo.OneCenter.rawAdjacentDecisionTrace_pseudoCount
assert_kernel_only TetraStereo.OneCenter.compareOccurrenceAdjacentPairsAuthoritative?_four_of_agrees
assert_kernel_only TetraStereo.OneCenter.frameRuntime_adjacent?_four_of_agrees
assert_kernel_only TetraStereo.OneCenter.compareOccurrenceAdjacentPairsAuthoritative?_four_count
assert_kernel_only TetraStereo.OneCenter.frameRuntime_adjacent?_four_count
assert_kernel_only TetraStereo.OneCenter.legacyOccurrenceFactAuthoritative?_eq_some_of_decisions
assert_kernel_only TetraStereo.OneCenter.legacyOccurrenceFactAuthoritative?_uppercase_of_source
assert_kernel_only TetraStereo.OneCenter.legacyOccurrenceFactAuthoritative?_fact_uppercase_of_source
assert_kernel_only TetraStereo.OneCenter.framedOccurrenceFactAuthoritative?_eq_some_of_decisions
assert_kernel_only TetraStereo.OneCenter.framedOccurrenceFactAuthoritative?_uppercase_of_source
assert_kernel_only TetraStereo.OneCenter.framedOccurrenceFactAuthoritative?_fact_uppercase_of_source
assert_kernel_only TetraStereo.OneCenter.cursorEmbedding_pairwise_ne
