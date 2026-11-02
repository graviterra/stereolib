import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

/-!
# Structural completeness of promoted Rule 6 on bounded branching ligands

The existing branching completeness theorem proves that the production Rules-1--5 comparator
terminates on recursively supported descriptor-bearing trees.  Rule 6 recursively reorders the
same children after promoting one reference atom, so it needs a separate termination proof.

The hypotheses below are unary hierarchy facts, not a table of successful pair comparisons:
every supported cursor has a neutral legacy conflict gate and the same bounded Rule-4b reference
arity at each depth.  Under those facts, both the ordinary prefix and the promoted Rule-6 suffix
are total on every supported pair.
-/

open RawMolecule
open ProductionCIPRerootComparatorLaws
open ProductionCIPBranchingOccurrenceComparatorCompleteness
open ProductionCIPDescriptorBranchingCompleteness
open DeclarativeCIP.ProductionOccurrenceRules456

/-- The sphere-major Rule-6 traversal terminates on a bounded supported branching frontier once
its recursive child-ordering callback is total on the next smaller depth. -/
theorem compareOccurrenceRule6_branching_exists (mol : RawMolecule)
    (rankFuel : Nat)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, before left right = some ordering)
    (reference : Nat) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → BranchingFrontierSupport mol fuel pairs →
      ∃ ordering, compareOccurrenceRule6 mol before reference fuel pairs = some ordering
  | 0, pairs, _, support => by
      have withinCap := support.length_le_cap
      cases labels : compareOccurrenceRule6PairLabels reference pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceRule6, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceRule6, labels]; omega⟩
      | eq =>
          have nextEq := branchingFrontier_nextOccurrence_zero_eq_nil support before before
          exact ⟨.eq, by
            simp [compareOccurrenceRule6, labels, nextEq]
            omega⟩
  | fuel + 1, pairs, fuelLe, support => by
      have withinCap := support.length_le_cap
      cases labels : compareOccurrenceRule6PairLabels reference pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceRule6, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceRule6, labels]; omega⟩
      | eq =>
          have lowerLe : fuel ≤ rankFuel := by omega
          rcases branchingFrontier_nextOccurrence_exists support lowerLe before before
              beforeTotal beforeTotal with ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil => exact ⟨.eq, by
              simp [compareOccurrenceRule6, labels, nextEq]
              omega⟩
          | cons pair rest =>
              rcases compareOccurrenceRule6_branching_exists mol rankFuel before beforeTotal
                  reference fuel (pair :: rest) (by omega) nextSupport with
                ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceRule6, labels, nextEq, decisionEq]
                omega⟩

/-- Structural facts sufficient for ordinary and promoted comparisons throughout one branching
hierarchy.  No field contains a successful pair-comparison result. -/
structure DescriptorRule6HierarchySupport (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel arity : Nat) : Prop where
  frontier_envelope : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap
  rule4b_arity_le : arity ≤ 2
  gate_neutral : ∀ depth cursor,
    depth ≤ fuel → BranchingCursorSupport mol depth cursor →
      RootRelativeGateNeutral mol depth cursor
  rule4b_uniform : ∀ depth cursor,
    depth ≤ fuel → BranchingCursorSupport mol depth cursor →
      (occurrenceRule4bReferences mol state depth [cursor]).length = arity

namespace DescriptorRule6HierarchySupport

/-- Rules 1--5 terminate at every depth of a structurally supported Rule-6 hierarchy. -/
theorem ordinary_comparison_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel arity depth : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel arity)
    (depth_le : depth ≤ fuel) (left right : CanonicalRerootCursor)
    (leftSupport : BranchingCursorSupport mol depth left)
    (rightSupport : BranchingCursorSupport mol depth right) :
    ∃ comparison, compareOccurrenceBranches? mol state depth left right = some comparison := by
  have width : 3 ^ depth ≤ RawMolecule.defaultBranchWidthCap :=
    le_trans (Nat.pow_le_pow_right (by omega) depth_le) hierarchy.frontier_envelope
  exact compareOccurrenceBranches?_descriptor_branching_exists mol state depth arity left right
    width leftSupport rightSupport (hierarchy.gate_neutral depth left depth_le leftSupport)
    hierarchy.rule4b_arity_le
    (hierarchy.rule4b_uniform depth left depth_le leftSupport)
    (hierarchy.rule4b_uniform depth right depth_le rightSupport)

/-- Rules 1--5 followed by dynamic Rule-6 reference promotion terminate on every supported pair
in the hierarchy.  The proof is by the actual decreasing production fuel. -/
theorem promoted_comparison_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel arity : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel arity)
    (reference : Nat) :
    ∀ depth, depth ≤ fuel → ∀ left right,
      BranchingCursorSupport mol depth left → BranchingCursorSupport mol depth right →
        ∃ decision,
          compareOccurrenceBranchesThroughRule6At? mol state reference depth left right =
            some decision
  | 0, _, left, right, leftSupport, rightSupport => by
      rcases hierarchy.ordinary_comparison_exists (by omega) left right leftSupport rightSupport
        with ⟨prior, priorEq⟩
      by_cases tied : prior.ordering = Ordering.eq
      · let ordering := compare
          (if left.node.atom == reference then 1 else 0)
          (if right.node.atom == reference then 1 else 0)
        exact ⟨{ ordering := ordering, pseudo := ordering != Ordering.eq }, by
          simp [compareOccurrenceBranchesThroughRule6At?, priorEq, tied, ordering]⟩
      · exact ⟨{ ordering := prior.ordering, pseudo := false }, by
          simp [compareOccurrenceBranchesThroughRule6At?, priorEq, tied]⟩
  | depth + 1, depth_le, left, right, leftSupport, rightSupport => by
      rcases hierarchy.ordinary_comparison_exists depth_le left right leftSupport rightSupport
        with ⟨prior, priorEq⟩
      by_cases tied : prior.ordering = Ordering.eq
      · have lower_le : depth ≤ fuel := by omega
        let before := fun a b =>
          (compareOccurrenceBranchesThroughRule6At? mol state reference depth a b).map
            Rule6TrackedDecision.ordering
        have beforeTotal : ∀ childLeft childRight,
            BranchingCursorSupport mol depth childLeft →
            BranchingCursorSupport mol depth childRight →
            ∃ ordering, before childLeft childRight = some ordering := by
          intro childLeft childRight childLeftSupport childRightSupport
          rcases hierarchy.promoted_comparison_exists reference depth lower_le
              childLeft childRight childLeftSupport childRightSupport with ⟨decision, decisionEq⟩
          exact ⟨decision.ordering, by simp [before, decisionEq]⟩
        have width : 3 ^ (depth + 1) ≤ RawMolecule.defaultBranchWidthCap :=
          le_trans (Nat.pow_le_pow_right (by omega) depth_le) hierarchy.frontier_envelope
        have frontier : BranchingFrontierSupport mol (depth + 1) [(left, right)] :=
          ⟨by simpa using And.intro leftSupport rightSupport, by simpa using width⟩
        rcases compareOccurrenceRule6_branching_exists mol depth before beforeTotal reference
            (depth + 1) [(left, right)] (by omega) frontier with ⟨ordering, orderingEq⟩
        exact ⟨{ ordering := ordering, pseudo := ordering != Ordering.eq }, by
          simp [compareOccurrenceBranchesThroughRule6At?, priorEq, tied, before, orderingEq]⟩
      · exact ⟨{ ordering := prior.ordering, pseudo := false }, by
          simp [compareOccurrenceBranchesThroughRule6At?, priorEq, tied]⟩

end DescriptorRule6HierarchySupport

/-- A descriptor-bearing four-ligand branching frame whose unary support facts extend through
every recursive depth needed by Rule 6. -/
structure DescriptorBranchingRule6CIPFrame (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    extends DescriptorBranchingCIPFrame (mol := mol) state fuel node roots where
  ligands : List Nat
  ligands_eq : ligands = mol.ligandsWithLonePair node.atom
  ligands_length : ligands.length = 4
  hierarchy_gate_neutral : ∀ depth cursor,
    depth ≤ fuel → BranchingCursorSupport mol depth cursor →
      RootRelativeGateNeutral mol depth cursor
  hierarchy_rule4b_uniform : ∀ depth cursor,
    depth ≤ fuel → BranchingCursorSupport mol depth cursor →
      (occurrenceRule4bReferences mol state depth [cursor]).length = rule4b_arity

namespace DescriptorBranchingRule6CIPFrame

def hierarchy
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    DescriptorRule6HierarchySupport mol state fuel frame.rule4b_arity where
  frontier_envelope := frame.frontier_envelope
  rule4b_arity_le := frame.rule4b_arity_le
  gate_neutral := frame.hierarchy_gate_neutral
  rule4b_uniform := frame.hierarchy_rule4b_uniform

/-- Every promoted Rule-6 comparison between generated ligand roots succeeds from recursive unary
support; no pairwise success table is assumed. -/
theorem promoted_comparison_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (reference : Nat) {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ decision,
      compareOccurrenceBranchesThroughRule6At? mol state reference fuel left right =
        some decision :=
  frame.hierarchy.promoted_comparison_exists reference fuel (by omega) left right
    (frame.support left left_mem) (frame.support right right_mem)

/-- A ligand position resolves to an actual cursor in the exact production frame. -/
def PositionInFrame
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (_frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (position : Nat) : Prop :=
  ∃ cursor, roots[position]? = some cursor

/-- A list contains only resolvable positions in the exact production frame. -/
def PositionsInFrame
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (positions : List Nat) : Prop :=
  ∀ position, position ∈ positions → frame.PositionInFrame position

/-- The ordinary Rules-1--5 position callback also succeeds for every two resolvable positions. -/
theorem compare_initial_positions_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {leftPosition rightPosition : Nat}
    (left_valid : frame.PositionInFrame leftPosition)
    (right_valid : frame.PositionInFrame rightPosition) :
    ∃ decision,
      compareRule6InitialPositions? (mol := mol) state fuel roots leftPosition rightPosition =
        some decision := by
  rcases left_valid with ⟨left, leftEq⟩
  rcases right_valid with ⟨right, rightEq⟩
  have leftMem : left ∈ roots := List.mem_iff_getElem?.2 ⟨leftPosition, leftEq⟩
  have rightMem : right ∈ roots := List.mem_iff_getElem?.2 ⟨rightPosition, rightEq⟩
  rcases frame.toDescriptorBranchingCIPFrame.comparison_exists leftMem rightMem with
    ⟨decision, decisionEq⟩
  exact ⟨decision, by
    simp [compareRule6InitialPositions?, leftEq, rightEq, decisionEq]⟩

/-- The fail-closed initial Rules-1--5 insertion succeeds and preserves the exact frame. -/
theorem insert_initial_position_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {candidate : Nat} (candidate_valid : frame.PositionInFrame candidate) :
    ∀ input, frame.PositionsInFrame input →
      ∃ output,
        insertRule6InitialPosition? (mol := mol) state fuel roots candidate input = some output ∧
        frame.PositionsInFrame output
  | [], _ => ⟨[candidate], rfl, by
      intro position member
      simpa using (show position = candidate from List.mem_singleton.mp member) ▸
        candidate_valid⟩
  | head :: tail, input_valid => by
      have head_valid := input_valid head (by simp)
      have tail_valid : frame.PositionsInFrame tail := by
        intro position member
        exact input_valid position (by simp [member])
      rcases frame.compare_initial_positions_exists candidate_valid head_valid with
        ⟨decision, decisionEq⟩
      by_cases is_lt : decision.ordering = Ordering.lt
      · rcases frame.insert_initial_position_exists candidate_valid tail tail_valid with
          ⟨inserted, insertedEq, insertedValid⟩
        refine ⟨head :: inserted, ?_, ?_⟩
        · simp [insertRule6InitialPosition?, decisionEq, is_lt, insertedEq]
        · intro position member
          rcases List.mem_cons.mp member with rfl | member
          · exact head_valid
          · exact insertedValid position member
      · refine ⟨candidate :: head :: tail, ?_, ?_⟩
        · simp [insertRule6InitialPosition?, decisionEq, is_lt]
        · intro position member
          simp only [List.mem_cons] at member
          rcases member with rfl | rfl | member
          · exact candidate_valid
          · exact head_valid
          · exact tail_valid position member

/-- The exact fail-closed initial insertion sort succeeds on any resolvable position list. -/
theorem sort_initial_positions_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∀ input, frame.PositionsInFrame input →
      ∃ output,
        sortRule6InitialPositions? (mol := mol) state fuel roots input = some output ∧
        frame.PositionsInFrame output
  | [], _ => ⟨[], rfl, by simp [PositionsInFrame]⟩
  | position :: positions, input_valid => by
      have position_valid := input_valid position (by simp)
      have positions_valid : frame.PositionsInFrame positions := by
        intro candidate member
        exact input_valid candidate (by simp [member])
      rcases frame.sort_initial_positions_exists positions positions_valid with
        ⟨sorted, sortedEq, sortedValid⟩
      rcases frame.insert_initial_position_exists position_valid sorted sortedValid with
        ⟨output, outputEq, outputValid⟩
      exact ⟨output, by
        simp [sortRule6InitialPositions?, sortedEq, outputEq], outputValid⟩

/-- The adjacent traversal succeeds on every resolvable initial order. -/
theorem initial_adjacent_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∀ input, frame.PositionsInFrame input →
      ∃ adjacent,
        compareRule6InitialAdjacent? (mol := mol) state fuel roots input = some adjacent
  | [], _ => ⟨[], rfl⟩
  | [position], _ => ⟨[], rfl⟩
  | left :: right :: remaining, input_valid => by
      have left_valid := input_valid left (by simp)
      have right_valid := input_valid right (by simp)
      have tail_valid : frame.PositionsInFrame (right :: remaining) := by
        intro position member
        exact input_valid position (by simp at member ⊢; exact Or.inr member)
      rcases frame.compare_initial_positions_exists left_valid right_valid with
        ⟨decision, decisionEq⟩
      rcases frame.initial_adjacent_exists (right :: remaining) tail_valid with
        ⟨deeper, deeperEq⟩
      exact ⟨some decision.ordering :: deeper, by
        simp [compareRule6InitialAdjacent?, decisionEq, deeperEq]⟩

/-- The position-indexed production callback succeeds whenever all three indices resolve in the
certified ligand and cursor frames. -/
theorem compare_positions_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {referencePosition leftPosition rightPosition reference : Nat}
    (reference_eq : frame.ligands[referencePosition]? = some reference)
    (left_valid : frame.PositionInFrame leftPosition)
    (right_valid : frame.PositionInFrame rightPosition) :
    ∃ decision,
      comparePositionsThroughRule6? (mol := mol) state fuel roots frame.ligands
          referencePosition leftPosition rightPosition = some decision := by
  rcases left_valid with ⟨left, leftEq⟩
  rcases right_valid with ⟨right, rightEq⟩
  have leftMem : left ∈ roots := List.mem_iff_getElem?.2 ⟨leftPosition, leftEq⟩
  have rightMem : right ∈ roots := List.mem_iff_getElem?.2 ⟨rightPosition, rightEq⟩
  rcases frame.promoted_comparison_exists reference leftMem rightMem with
    ⟨decision, decisionEq⟩
  exact ⟨decision, by
    simp [comparePositionsThroughRule6?, reference_eq, leftEq, rightEq, decisionEq]⟩

/-- Promoted insertion cannot fail on resolvable positions, and it preserves resolvability. -/
theorem insert_promoted_position_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {referencePosition reference candidate : Nat}
    (reference_eq : frame.ligands[referencePosition]? = some reference)
    (candidate_valid : frame.PositionInFrame candidate) :
    ∀ input, frame.PositionsInFrame input →
      ∃ output,
        insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots frame.ligands
          referencePosition candidate input = some output ∧
        frame.PositionsInFrame output.1
  | [], _ => by
      exact ⟨([candidate], 0, true), rfl, by
        intro position member
        simpa using (show position = candidate from List.mem_singleton.mp member) ▸
          candidate_valid⟩
  | low :: remaining, input_valid => by
      have low_valid := input_valid low (by simp)
      have remaining_valid : frame.PositionsInFrame remaining := by
        intro position member
        exact input_valid position (by simp [member])
      rcases frame.compare_positions_exists reference_eq low_valid candidate_valid with
        ⟨decision, decisionEq⟩
      cases orderingEq : decision.ordering with
      | lt =>
          rcases frame.insert_promoted_position_exists reference_eq candidate_valid remaining
              remaining_valid with ⟨deeper, deeperEq, deeperValid⟩
          refine ⟨(low :: deeper.1,
              (if decision.pseudo then 1 else 0) + deeper.2.1, deeper.2.2), ?_, ?_⟩
          · simp [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq, deeperEq]
          · intro position member
            rcases List.mem_cons.mp member with rfl | member
            · exact low_valid
            · exact deeperValid position member
      | eq =>
          refine ⟨(candidate :: low :: remaining,
              (if decision.pseudo then 1 else 0), false), ?_, ?_⟩
          · simp [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq]
          · intro position member
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | member
            · exact candidate_valid
            · exact low_valid
            · exact remaining_valid position member
      | gt =>
          refine ⟨(candidate :: low :: remaining,
              (if decision.pseudo then 1 else 0), true), ?_, ?_⟩
          · simp [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq]
          · intro position member
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | member
            · exact candidate_valid
            · exact low_valid
            · exact remaining_valid position member

/-- The exact `foldlM` used by production Rule 6 cannot fail on a list of resolvable candidates.
The accumulated promoted order remains within the same exact four-cursor frame. -/
theorem fold_promoted_positions_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {referencePosition reference : Nat}
    (reference_eq : frame.ligands[referencePosition]? = some reference) :
    ∀ candidates accumulator,
      frame.PositionsInFrame candidates → frame.PositionsInFrame accumulator.1 →
      ∃ output,
        candidates.foldlM (fun current candidate => do
          let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
            frame.ligands referencePosition candidate current.1
          some (inserted.1, current.2.1 + inserted.2.1,
            current.2.2 && inserted.2.2)) accumulator = some output ∧
        frame.PositionsInFrame output.1
  | [], accumulator, _, accumulator_valid => ⟨accumulator, rfl, accumulator_valid⟩
  | candidate :: remaining, accumulator, candidates_valid, accumulator_valid => by
      have candidate_valid := candidates_valid candidate (by simp)
      have remaining_valid : frame.PositionsInFrame remaining := by
        intro position member
        exact candidates_valid position (by simp [member])
      rcases frame.insert_promoted_position_exists reference_eq candidate_valid accumulator.1
          accumulator_valid with ⟨inserted, insertedEq, insertedValid⟩
      let next := (inserted.1, accumulator.2.1 + inserted.2.1,
        accumulator.2.2 && inserted.2.2)
      rcases frame.fold_promoted_positions_exists reference_eq remaining next remaining_valid
          insertedValid with ⟨output, outputEq, outputValid⟩
      refine ⟨output, ?_, outputValid⟩
      rw [List.foldlM_cons, insertedEq]
      simpa only [next] using outputEq

/-- Complete promoted ranking succeeds for every resolvable start order and reference position.
This reaches the actual four-way Rule-6 ranking carrier, not merely its pairwise comparator. -/
theorem promoted_ranking_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {referencePosition reference : Nat}
    (reference_eq : frame.ligands[referencePosition]? = some reference)
    (start : List Nat) (start_valid : frame.PositionsInFrame start) :
    ∃ ranking,
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots frame.ligands
        start referencePosition = some ranking := by
  have emptyValid : frame.PositionsInFrame [] := by simp [PositionsInFrame]
  rcases frame.fold_promoted_positions_exists reference_eq start ([], 0, true)
      start_valid emptyValid with ⟨output, outputEq, _⟩
  refine ⟨{ positions := output.1.reverse
            pseudoComparisons := output.2.1
            unique := output.2.2 }, ?_⟩
  unfold rankOccurrencePositionsThroughRule6Tracked?
  rw [outputEq]
  rfl

/-- Every numeric position below four resolves in the exact four-root production frame. -/
theorem positionInFrame_of_lt_four
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (position : Nat) (position_lt : position < 4) : frame.PositionInFrame position := by
  have bound : position < roots.length := by simpa [frame.roots_length] using position_lt
  exact ⟨roots[position], List.getElem?_eq_getElem bound⟩

/-- The complete initial four-position Rules-1--5 sort and adjacent traversal cannot fail from
the optional comparison machinery on a structurally supported Rule-6 frame. -/
theorem initial_four_position_partition_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∃ sorted adjacent,
      sortRule6InitialPositions? (mol := mol) state fuel roots (List.range 4) = some sorted ∧
      compareRule6InitialAdjacent? (mol := mol) state fuel roots sorted = some adjacent := by
  have rangeValid : frame.PositionsInFrame (List.range 4) := by
    intro position member
    exact frame.positionInFrame_of_lt_four position (List.mem_range.mp member)
  rcases frame.sort_initial_positions_exists (List.range 4) rangeValid with
    ⟨sorted, sortedEq, sortedValid⟩
  rcases frame.initial_adjacent_exists sorted sortedValid with ⟨adjacent, adjacentEq⟩
  exact ⟨sorted, adjacent, sortedEq, adjacentEq⟩

/-- Production Rule-6 ranking is structurally total for any permutation-like four-position start
list: every listed position is required only to lie below four. -/
theorem promoted_four_position_ranking_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4) :
    ∃ ranking,
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots frame.ligands
        start referencePosition = some ranking := by
  have reference_bound : referencePosition < frame.ligands.length := by
    simpa [frame.ligands_length] using reference_lt
  let reference := frame.ligands[referencePosition]
  have reference_eq : frame.ligands[referencePosition]? = some reference :=
    List.getElem?_eq_getElem reference_bound
  apply frame.promoted_ranking_exists reference_eq start
  intro position member
  exact frame.positionInFrame_of_lt_four position (start_lt position member)

/-- Proof-relevant execution evidence for every optional stage of the production Rule-6 carrier.

Unlike bare equations saying that the option-valued functions returned `some`, this object records
the independent inductive derivations of the initial sort and adjacent traversal. It also records
a complete promoted-ranking trace for every one of the four possible reference positions. -/
structure StructuralExecutionCertificate
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) where
  sorted : List Nat
  adjacent : List (Option Ordering)
  initial_sort : SortRule6InitialDerivation (mol := mol) state fuel roots
    (List.range 4) sorted
  initial_adjacent : Rule6InitialAdjacentDerivation (mol := mol) state fuel roots
    sorted adjacent
  promoted_trace : ∀ referencePosition, referencePosition < 4 →
    ∃ ranking,
      PromotedRankingTrace (mol := mol) state fuel roots frame.ligands sorted
        referencePosition ranking

/-- Structural branching support produces proof-relevant traces for the literal initial and
promoted Rule-6 execution, not merely successful option equations. -/
theorem structuralExecutionCertificate_nonempty
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    Nonempty (StructuralExecutionCertificate frame) := by
  rcases frame.initial_four_position_partition_exists with
    ⟨sorted, adjacent, sortedEq, adjacentEq⟩
  let initialSort := sortRule6InitialDerivation_of_production state fuel roots
    (List.range 4) sorted sortedEq
  let initialAdjacent := rule6InitialAdjacentDerivation_of_production state fuel roots
    sorted adjacent adjacentEq
  refine ⟨{ sorted := sorted
            adjacent := adjacent
            initial_sort := initialSort
            initial_adjacent := initialAdjacent
            promoted_trace := ?_ }⟩
  intro referencePosition reference_lt
  have sorted_lt : ∀ position, position ∈ sorted → position < 4 := by
    intro position member
    exact List.mem_range.mp (initialSort.perm.mem_iff.mp member)
  rcases frame.promoted_four_position_ranking_exists referencePosition reference_lt
      sorted sorted_lt with ⟨ranking, rankingEq⟩
  exact ⟨ranking,
    promotedRankingTrace_complete state fuel roots frame.ligands sorted referencePosition
      ranking rankingEq⟩

end DescriptorBranchingRule6CIPFrame

/-! ## Cyclic incoming specialization -/

/-- Rule-6-complete descriptor-bearing branching support for a cyclic incoming center.

The cyclic equations identify the production roots as real incoming occurrences of the same
cyclic center.  The inherited hierarchy certificate supplies the corresponding neutral-gate and
uniform descriptor-reference facts at every recursively visited depth. -/
structure CyclicIncomingDescriptorBranchingRule6CIPFrame (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    extends DescriptorBranchingRule6CIPFrame mol state fuel node roots where
  center_cyclic : mol.atomLiesInCycle fuel node.atom = true
  incoming_frame : ∀ root, root ∈ roots → root.previous? = some node

namespace CyclicIncomingDescriptorBranchingRule6CIPFrame

/-- Dynamic Rule-6 comparison is total on every pair of roots in the cyclic incoming frame. -/
theorem promoted_comparison_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CyclicIncomingDescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (reference : Nat) {left right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (right_mem : right ∈ roots) :
    ∃ decision,
      compareOccurrenceBranchesThroughRule6At? mol state reference fuel left right =
        some decision :=
  frame.toDescriptorBranchingRule6CIPFrame.promoted_comparison_exists
    reference left_mem right_mem

/-- The initial four-position partition traversal is total for cyclic incoming frames. -/
theorem initial_four_position_partition_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CyclicIncomingDescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∃ sorted adjacent,
      sortRule6InitialPositions? (mol := mol) state fuel roots (List.range 4) = some sorted ∧
      compareRule6InitialAdjacent? (mol := mol) state fuel roots sorted = some adjacent :=
  frame.toDescriptorBranchingRule6CIPFrame.initial_four_position_partition_exists

/-- Complete promoted four-position ranking is total for cyclic incoming frames. -/
theorem promoted_four_position_ranking_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CyclicIncomingDescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4) :
    ∃ ranking,
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots frame.ligands
        start referencePosition = some ranking :=
  frame.toDescriptorBranchingRule6CIPFrame.promoted_four_position_ranking_exists
    referencePosition reference_lt start start_lt

/-- Cyclic incoming frames inherit the same proof-relevant initial and promoted execution
certificate while retaining their cyclic-center and incoming-root equations. -/
theorem structuralExecutionCertificate_nonempty
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : CyclicIncomingDescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    Nonempty (DescriptorBranchingRule6CIPFrame.StructuralExecutionCertificate
      frame.toDescriptorBranchingRule6CIPFrame) :=
  frame.toDescriptorBranchingRule6CIPFrame.structuralExecutionCertificate_nonempty

end CyclicIncomingDescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
