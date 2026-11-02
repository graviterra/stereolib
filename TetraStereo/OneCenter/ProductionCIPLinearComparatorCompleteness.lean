import TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws

/-! Structural completeness of the production constitutional comparator on bounded linear
ligand digraphs. -/

open RawMolecule

def linearPaddingCursor (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    CanonicalRerootCursor :=
  { node := mol.canonicalPhantom cursor.node.atom (cursor.node.rule1bRootDistance + 1) }

inductive LinearCursorSupport (mol : RawMolecule) : Nat → CanonicalRerootCursor → Prop
  | terminal (fuel : Nat) (cursor : CanonicalRerootCursor)
      (label : ∃ value, mol.canonicalRule1aLabel? cursor.node = some value)
      (isTerminal : cursorTerminal mol cursor = true) :
      LinearCursorSupport mol fuel cursor
  | step (fuel : Nat) (cursor child : CanonicalRerootCursor)
      (label : ∃ value, mol.canonicalRule1aLabel? cursor.node = some value)
      (children : cursor.children mol = [child])
      (childSupport : LinearCursorSupport mol fuel child) :
      LinearCursorSupport mol (fuel + 1) cursor

theorem LinearCursorSupport.label {mol : RawMolecule} {fuel : Nat}
    {cursor : CanonicalRerootCursor} (support : LinearCursorSupport mol fuel cursor) :
    ∃ value, mol.canonicalRule1aLabel? cursor.node = some value := by
  cases support with
  | terminal _ _ label _ => exact label
  | step _ _ _ label _ _ => exact label

theorem LinearCursorSupport.zero_terminal {mol : RawMolecule}
    {cursor : CanonicalRerootCursor} (support : LinearCursorSupport mol 0 cursor) :
    cursorTerminal mol cursor = true := by
  cases support with
  | terminal _ _ _ terminal => exact terminal

theorem linearPaddingCursor_support (mol : RawMolecule) (fuel : Nat)
    (cursor : CanonicalRerootCursor) :
    LinearCursorSupport mol fuel (linearPaddingCursor mol cursor) := by
  apply LinearCursorSupport.terminal
  · simp [linearPaddingCursor, RawMolecule.canonicalRule1aLabel?,
      RawMolecule.canonicalPhantom]
  · simp [linearPaddingCursor, cursorTerminal, RawMolecule.canonicalPhantom,
      CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf]

theorem linearPaddingCursor_terminal (mol : RawMolecule)
    (cursor : CanonicalRerootCursor) :
    cursorTerminal mol (linearPaddingCursor mol cursor) = true := by
  exact (linearPaddingCursor_support mol 0 cursor).zero_terminal

theorem rankedCursorChildren?_eq_of_linear_terminal (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor)
    (terminal : cursorTerminal mol cursor = true) :
    rankedCursorChildren? mol before cursor =
      some (List.replicate 3 (linearPaddingCursor mol cursor)) := by
  have children := cursor_children_eq_nil_of_terminal mol cursor terminal
  simp [rankedCursorChildren?, children, sortCursorsBy?, linearPaddingCursor]

theorem rankedCursorChildren?_eq_of_linear_step (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor child : CanonicalRerootCursor) (children : cursor.children mol = [child]) :
    rankedCursorChildren? mol before cursor =
      some (child :: List.replicate 2 (linearPaddingCursor mol cursor)) := by
  simp [rankedCursorChildren?, children, sortCursorsBy?, insertCursorBy?, linearPaddingCursor]

abbrev LinearCursorPair := CanonicalRerootCursor × CanonicalRerootCursor

inductive LinearFrontierSupport (mol : RawMolecule) (fuel : Nat) :
    List LinearCursorPair → Prop
  | nil : LinearFrontierSupport mol fuel []
  | main (left right : CanonicalRerootCursor) (tail : List LinearCursorPair)
      (leftSupport : LinearCursorSupport mol fuel left)
      (rightSupport : LinearCursorSupport mol fuel right)
      (tailLength : tail.length ≤ 2)
      (tailSupport : ∀ pair, pair ∈ tail →
        LinearCursorSupport mol fuel pair.1 ∧
        LinearCursorSupport mol fuel pair.2 ∧
        cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true) :
      LinearFrontierSupport mol fuel ((left, right) :: tail)

theorem LinearFrontierSupport.length_le_three {mol : RawMolecule} {fuel : Nat}
    {pairs : List LinearCursorPair} (support : LinearFrontierSupport mol fuel pairs) :
    pairs.length ≤ 3 := by
  cases support with
  | nil => simp
  | main _ _ tail _ _ tailLength _ => simp; omega

theorem compareCanonicalNodeRule?_exists_of_linear_support (mol : RawMolecule)
    (rule : CanonicalRuleStage) (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftSupport : LinearCursorSupport mol fuel left)
    (rightSupport : LinearCursorSupport mol fuel right) :
    ∃ ordering, mol.compareCanonicalNodeRule? rule left.node right.node = some ordering := by
  cases rule with
  | rule1a =>
      rcases leftSupport.label with ⟨leftLabel, leftEq⟩
      rcases rightSupport.label with ⟨rightLabel, rightEq⟩
      exact ⟨compareCIPAtomicLabel leftLabel rightLabel, by
        simp [RawMolecule.compareCanonicalNodeRule?, leftEq, rightEq]⟩
  | rule1b => exact ⟨_, rfl⟩
  | rule2 => exact ⟨_, rfl⟩

theorem compareCursorPairLabels_exists_of_all_linear_support (mol : RawMolecule)
    (rule : CanonicalRuleStage) (fuel : Nat) :
    ∀ pairs : List LinearCursorPair,
      (∀ pair, pair ∈ pairs →
        LinearCursorSupport mol fuel pair.1 ∧ LinearCursorSupport mol fuel pair.2) →
      ∃ ordering, compareCursorPairLabels mol rule pairs = some ordering
  | [], _ => ⟨.eq, rfl⟩
  | pair :: rest, support => by
      have head := support pair (by simp)
      rcases compareCanonicalNodeRule?_exists_of_linear_support mol rule fuel
          pair.1 pair.2 head.1 head.2 with ⟨decision, decisionEq⟩
      cases decision with
      | lt => exact ⟨.lt, by simp [compareCursorPairLabels, decisionEq]⟩
      | gt => exact ⟨.gt, by simp [compareCursorPairLabels, decisionEq]⟩
      | eq =>
          rcases compareCursorPairLabels_exists_of_all_linear_support mol rule fuel rest
              (fun candidate member => support candidate (by simp [member])) with
            ⟨tailDecision, tailEq⟩
          exact ⟨tailDecision, by simp [compareCursorPairLabels, decisionEq, tailEq]⟩

theorem LinearFrontierSupport.compareLabels_exists {mol : RawMolecule}
    {fuel : Nat} {pairs : List LinearCursorPair}
    (support : LinearFrontierSupport mol fuel pairs) (rule : CanonicalRuleStage) :
    ∃ ordering, compareCursorPairLabels mol rule pairs = some ordering := by
  cases support with
  | nil => exact ⟨.eq, rfl⟩
  | main left right tail leftSupport rightSupport tailLength tailSupport =>
      have allSupport : ∀ pair, pair ∈ ((left, right) :: tail) →
          LinearCursorSupport mol fuel pair.1 ∧ LinearCursorSupport mol fuel pair.2 := by
        intro pair member
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact ⟨leftSupport, rightSupport⟩
        · exact ⟨(tailSupport pair tailMember).1, (tailSupport pair tailMember).2.1⟩
      exact compareCursorPairLabels_exists_of_all_linear_support
        mol rule fuel ((left, right) :: tail) allSupport

theorem cursor_not_terminal_of_children_singleton (mol : RawMolecule)
    (cursor child : CanonicalRerootCursor) (children : cursor.children mol = [child]) :
    cursorTerminal mol cursor = false := by
  cases terminalEq : cursorTerminal mol cursor with
  | false => rfl
  | true =>
      have nilEq := cursor_children_eq_nil_of_terminal mol cursor terminalEq
      rw [children] at nilEq
      contradiction

theorem nextCursorPairs?_terminal_list_eq_nil (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∀ pairs : List LinearCursorPair,
      (∀ pair, pair ∈ pairs →
        cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true) →
      nextCursorPairs? mol before pairs = some []
  | [], _ => rfl
  | pair :: pairs, terminal => by
      have head := terminal pair (by simp)
      have tail : ∀ candidate, candidate ∈ pairs →
          cursorTerminal mol candidate.1 = true ∧
          cursorTerminal mol candidate.2 = true := by
        intro candidate member
        exact terminal candidate (by simp [member])
      simp [nextCursorPairs?, nextCursorPairs?_terminal_list_eq_nil mol before pairs tail,
        head.1, head.2]

theorem LinearFrontierSupport.next_exists {mol : RawMolecule} {fuel : Nat}
    {pairs : List LinearCursorPair} (support : LinearFrontierSupport mol (fuel + 1) pairs)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∃ next, nextCursorPairs? mol before pairs = some next ∧
      LinearFrontierSupport mol fuel next := by
  cases support with
  | nil => exact ⟨[], rfl, .nil⟩
  | main left right tail leftSupport rightSupport tailLength tailSupport =>
      have tailNext : nextCursorPairs? mol before tail = some [] :=
        nextCursorPairs?_terminal_list_eq_nil mol before tail (by
          intro pair member
          exact ⟨(tailSupport pair member).2.2.1, (tailSupport pair member).2.2.2⟩)
      cases leftSupport with
      | terminal _ _ leftLabel leftTerminal =>
          cases rightSupport with
          | terminal _ _ rightLabel rightTerminal =>
              exact ⟨[], by simp [nextCursorPairs?, tailNext, leftTerminal, rightTerminal], .nil⟩
          | step _ _ rightChild rightLabel rightChildren rightChildSupport =>
              let leftPad := linearPaddingCursor mol left
              let rightPad := linearPaddingCursor mol right
              let next : List LinearCursorPair :=
                [(leftPad, rightChild), (leftPad, rightPad), (leftPad, rightPad)]
              have leftRank := rankedCursorChildren?_eq_of_linear_terminal
                mol before left leftTerminal
              have rightRank := rankedCursorChildren?_eq_of_linear_step
                mol before right rightChild rightChildren
              have rightNotTerminal :=
                cursor_not_terminal_of_children_singleton mol right rightChild rightChildren
              refine ⟨next, ?_, ?_⟩
              · simp [nextCursorPairs?, tailNext, leftTerminal, rightChildren,
                  rightNotTerminal, leftRank, rightRank, next, leftPad, rightPad]
              · refine .main leftPad rightChild [(leftPad, rightPad), (leftPad, rightPad)]
                  (linearPaddingCursor_support mol fuel left) rightChildSupport (by simp) ?_
                intro pair member
                simp at member
                subst pair
                exact ⟨linearPaddingCursor_support mol fuel left,
                  linearPaddingCursor_support mol fuel right,
                  linearPaddingCursor_terminal mol left,
                  linearPaddingCursor_terminal mol right⟩
      | step _ _ leftChild leftLabel leftChildren leftChildSupport =>
          have leftNotTerminal :=
            cursor_not_terminal_of_children_singleton mol left leftChild leftChildren
          cases rightSupport with
          | terminal _ _ rightLabel rightTerminal =>
              let leftPad := linearPaddingCursor mol left
              let rightPad := linearPaddingCursor mol right
              let next : List LinearCursorPair :=
                [(leftChild, rightPad), (leftPad, rightPad), (leftPad, rightPad)]
              have leftRank := rankedCursorChildren?_eq_of_linear_step
                mol before left leftChild leftChildren
              have rightRank := rankedCursorChildren?_eq_of_linear_terminal
                mol before right rightTerminal
              refine ⟨next, ?_, ?_⟩
              · simp [nextCursorPairs?, tailNext, rightTerminal, leftChildren,
                  leftNotTerminal, leftRank, rightRank, next, leftPad, rightPad]
              · refine .main leftChild rightPad [(leftPad, rightPad), (leftPad, rightPad)]
                  leftChildSupport (linearPaddingCursor_support mol fuel right) (by simp) ?_
                intro pair member
                simp at member
                subst pair
                exact ⟨linearPaddingCursor_support mol fuel left,
                  linearPaddingCursor_support mol fuel right,
                  linearPaddingCursor_terminal mol left,
                  linearPaddingCursor_terminal mol right⟩
          | step _ _ rightChild rightLabel rightChildren rightChildSupport =>
              let leftPad := linearPaddingCursor mol left
              let rightPad := linearPaddingCursor mol right
              let next : List LinearCursorPair :=
                [(leftChild, rightChild), (leftPad, rightPad), (leftPad, rightPad)]
              have leftRank := rankedCursorChildren?_eq_of_linear_step
                mol before left leftChild leftChildren
              have rightRank := rankedCursorChildren?_eq_of_linear_step
                mol before right rightChild rightChildren
              refine ⟨next, ?_, ?_⟩
              · simp [nextCursorPairs?, tailNext, leftChildren, rightChildren,
                  leftNotTerminal,
                  cursor_not_terminal_of_children_singleton mol right rightChild rightChildren,
                  leftRank, rightRank, next, leftPad, rightPad]
              · refine .main leftChild rightChild [(leftPad, rightPad), (leftPad, rightPad)]
                  leftChildSupport rightChildSupport (by simp) ?_
                intro pair member
                simp at member
                subst pair
                exact ⟨linearPaddingCursor_support mol fuel left,
                  linearPaddingCursor_support mol fuel right,
                  linearPaddingCursor_terminal mol left,
                  linearPaddingCursor_terminal mol right⟩

theorem LinearFrontierSupport.next_zero_eq_nil {mol : RawMolecule}
    {pairs : List LinearCursorPair} (support : LinearFrontierSupport mol 0 pairs)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    nextCursorPairs? mol before pairs = some [] := by
  cases support with
  | nil => rfl
  | main left right tail leftSupport rightSupport tailLength tailSupport =>
      have leftTerminal := leftSupport.zero_terminal
      have rightTerminal := rightSupport.zero_terminal
      have tailNext : nextCursorPairs? mol before tail = some [] :=
        nextCursorPairs?_terminal_list_eq_nil mol before tail (by
          intro pair member
          exact ⟨(tailSupport pair member).2.2.1, (tailSupport pair member).2.2.2⟩)
      simp [nextCursorPairs?, tailNext, leftTerminal, rightTerminal]

theorem compareCursorRule_linear_exists (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (rule : CanonicalRuleStage) :
    ∀ fuel pairs, LinearFrontierSupport mol fuel pairs →
      ∃ ordering, compareCursorRule mol before rule fuel pairs = some ordering
  | 0, pairs, support => by
      rcases support.compareLabels_exists rule with ⟨labels, labelsEq⟩
      have width := support.length_le_three
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap := by
        simp [RawMolecule.defaultBranchWidthCap]
        omega
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq,
          RawMolecule.defaultBranchWidthCap, withinCap]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq,
          RawMolecule.defaultBranchWidthCap, withinCap]; omega⟩
      | eq =>
          have nextEq := support.next_zero_eq_nil before
          exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq,
            RawMolecule.defaultBranchWidthCap, withinCap]; omega⟩
  | fuel + 1, pairs, support => by
      rcases support.compareLabels_exists rule with ⟨labels, labelsEq⟩
      have width := support.length_le_three
      have withinCap : pairs.length ≤ RawMolecule.defaultBranchWidthCap := by
        simp [RawMolecule.defaultBranchWidthCap]
        omega
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq,
          RawMolecule.defaultBranchWidthCap, withinCap]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq,
          RawMolecule.defaultBranchWidthCap, withinCap]; omega⟩
      | eq =>
          rcases support.next_exists before with ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil => exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq,
              RawMolecule.defaultBranchWidthCap, withinCap]; omega⟩
          | cons pair rest =>
              rcases compareCursorRule_linear_exists mol before rule fuel (pair :: rest)
                  nextSupport with ⟨decision, decisionEq⟩
              exact ⟨decision, by simp [compareCursorRule, labelsEq, nextEq, decisionEq,
                RawMolecule.defaultBranchWidthCap, withinCap]; omega⟩

theorem compareCursorBranchAt_linear_supported_exists (mol : RawMolecule) (fuel : Nat)
    (left right : CanonicalRerootCursor)
    (leftSupport : LinearCursorSupport mol fuel left)
    (rightSupport : LinearCursorSupport mol fuel right) :
    ∃ ordering, compareCursorBranchAt mol fuel .rule2 left right = some ordering := by
  cases fuel with
  | zero =>
      rcases leftSupport.label with ⟨leftLabel, leftEq⟩
      rcases rightSupport.label with ⟨rightLabel, rightEq⟩
      simp only [compareCursorBranchAt, RawMolecule.compareCanonicalNodeThrough?,
        RawMolecule.compareCanonicalNodeRule?, leftEq, rightEq]
      cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel <;> simp [rule1aEq]
      cases mol.compareCanonicalNodeRule .rule1b left.node right.node <;> simp
  | succ fuel =>
      let before := compareCursorBranchAt mol fuel .rule2
      have frontier : LinearFrontierSupport mol (fuel + 1) [(left, right)] :=
        .main left right [] leftSupport rightSupport (by simp) (by simp)
      rcases compareCursorRule_linear_exists mol before .rule1a (fuel + 1)
          [(left, right)] frontier with ⟨rule1a, rule1aEq⟩
      rcases compareCursorRule_linear_exists mol before .rule1b (fuel + 1)
          [(left, right)] frontier with ⟨rule1b, rule1bEq⟩
      rcases compareCursorRule_linear_exists mol before .rule2 (fuel + 1)
          [(left, right)] frontier with ⟨rule2, rule2Eq⟩
      cases rule1a <;> cases rule1b <;> cases rule2 <;>
        simp [compareCursorBranchAt, before, rule1aEq, rule1bEq, rule2Eq]

end TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws
