import TetraStereo.OneCenter.ProductionCIPLinearComparatorCompleteness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws

/-! Structural completeness of the production constitutional comparator on bounded branching
ligand trees.  Unlike the linear case, child sorting invokes recursive sibling comparisons; those
calls are discharged from support at the strictly smaller subtree depth. -/

open RawMolecule

inductive BranchingCursorSupport (mol : RawMolecule) : Nat → CanonicalRerootCursor → Prop
  | terminal (fuel : Nat) (cursor : CanonicalRerootCursor)
      (label : ∃ value, mol.canonicalRule1aLabel? cursor.node = some value)
      (isTerminal : cursorTerminal mol cursor = true) :
      BranchingCursorSupport mol fuel cursor
  | branch (fuel : Nat) (cursor : CanonicalRerootCursor)
      (children : List CanonicalRerootCursor)
      (label : ∃ value, mol.canonicalRule1aLabel? cursor.node = some value)
      (childrenEq : cursor.children mol = children)
      (width : children.length ≤ 3)
      (childrenSupport : ∀ child, child ∈ children → BranchingCursorSupport mol fuel child) :
      BranchingCursorSupport mol (fuel + 1) cursor

theorem BranchingCursorSupport.label {mol : RawMolecule} {fuel : Nat}
    {cursor : CanonicalRerootCursor} (support : BranchingCursorSupport mol fuel cursor) :
    ∃ value, mol.canonicalRule1aLabel? cursor.node = some value := by
  cases support with
  | terminal _ _ label _ => exact label
  | branch _ _ _ label _ _ _ => exact label

theorem BranchingCursorSupport.zero_terminal {mol : RawMolecule}
    {cursor : CanonicalRerootCursor} (support : BranchingCursorSupport mol 0 cursor) :
    cursorTerminal mol cursor = true := by
  cases support with
  | terminal _ _ _ terminal => exact terminal

theorem BranchingCursorSupport.succ {mol : RawMolecule} {fuel : Nat}
    {cursor : CanonicalRerootCursor} (support : BranchingCursorSupport mol fuel cursor) :
    BranchingCursorSupport mol (fuel + 1) cursor := by
  induction support with
  | terminal fuel cursor label terminal => exact .terminal (fuel + 1) cursor label terminal
  | branch fuel cursor children label childrenEq width childrenSupport ih =>
      exact .branch (fuel + 1) cursor children label childrenEq width ih

theorem BranchingCursorSupport.mono {mol : RawMolecule} {smaller larger : Nat}
    {cursor : CanonicalRerootCursor} (support : BranchingCursorSupport mol smaller cursor)
    (le : smaller ≤ larger) : BranchingCursorSupport mol larger cursor := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  clear le
  induction extra with
  | zero => simpa using support
  | succ extra ih =>
      simpa [Nat.add_assoc] using BranchingCursorSupport.succ ih

/-- Every recursively supported linear cursor is a branching cursor with singleton child lists.
This makes the branching support class a strict structural extension of the linear one. -/
theorem LinearCursorSupport.toBranching {mol : RawMolecule} {fuel : Nat}
    {cursor : CanonicalRerootCursor} (support : LinearCursorSupport mol fuel cursor) :
    BranchingCursorSupport mol fuel cursor := by
  induction support with
  | terminal fuel cursor label terminal => exact .terminal fuel cursor label terminal
  | step fuel cursor child label children childSupport ih =>
      exact .branch fuel cursor [child] label children (by simp) (by
        intro candidate member
        simp at member
        subst candidate
        exact ih)

def branchingPaddingCursor (mol : RawMolecule) (cursor : CanonicalRerootCursor) :
    CanonicalRerootCursor :=
  linearPaddingCursor mol cursor

theorem branchingPaddingCursor_support (mol : RawMolecule) (fuel : Nat)
    (cursor : CanonicalRerootCursor) :
    BranchingCursorSupport mol fuel (branchingPaddingCursor mol cursor) := by
  apply BranchingCursorSupport.terminal
  · simp [branchingPaddingCursor, linearPaddingCursor,
      RawMolecule.canonicalRule1aLabel?, RawMolecule.canonicalPhantom]
  · exact linearPaddingCursor_terminal mol cursor

theorem insertCursorBy?_exists_of_supported
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (supported : CanonicalRerootCursor → Prop)
    (total : ∀ left right, supported left → supported right →
      ∃ ordering, before left right = some ordering)
    (candidate : CanonicalRerootCursor) (candidateSupport : supported candidate) :
    ∀ input, (∀ cursor, cursor ∈ input → supported cursor) →
      ∃ output,
        insertCursorBy? before candidate input = some output ∧
        (∀ cursor, cursor ∈ output → supported cursor) ∧
        output.length = input.length + 1
  | [], _ => ⟨[candidate], rfl, by simpa, rfl⟩
  | head :: tail, inputSupport => by
      have headSupport := inputSupport head (by simp)
      rcases total candidate head candidateSupport headSupport with ⟨ordering, orderingEq⟩
      cases ordering with
      | lt =>
          rcases insertCursorBy?_exists_of_supported before supported total candidate
              candidateSupport tail (fun cursor member => inputSupport cursor (by simp [member]))
            with ⟨deeper, deeperEq, deeperSupport, deeperLength⟩
          refine ⟨head :: deeper, ?_, ?_, ?_⟩
          · simp [insertCursorBy?, orderingEq, deeperEq]
          · intro cursor member
            rcases List.mem_cons.mp member with rfl | member
            · exact headSupport
            · exact deeperSupport cursor member
          · simp [deeperLength]
      | eq =>
          refine ⟨candidate :: head :: tail, ?_, ?_, by simp⟩
          · simp [insertCursorBy?, orderingEq]
          · intro cursor member
            simp at member
            rcases member with rfl | rfl | member
            · exact candidateSupport
            · exact headSupport
            · exact inputSupport cursor (by simp [member])
      | gt =>
          refine ⟨candidate :: head :: tail, ?_, ?_, by simp⟩
          · simp [insertCursorBy?, orderingEq]
          · intro cursor member
            simp at member
            rcases member with rfl | rfl | member
            · exact candidateSupport
            · exact headSupport
            · exact inputSupport cursor (by simp [member])

theorem sortCursorsBy?_exists_of_supported
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (supported : CanonicalRerootCursor → Prop)
    (total : ∀ left right, supported left → supported right →
      ∃ ordering, before left right = some ordering) :
    ∀ input, (∀ cursor, cursor ∈ input → supported cursor) →
      ∃ output,
        sortCursorsBy? before input = some output ∧
        (∀ cursor, cursor ∈ output → supported cursor) ∧
        output.length = input.length
  | [], _ => ⟨[], rfl, by simp, rfl⟩
  | head :: tail, inputSupport => by
      have headSupport := inputSupport head (by simp)
      rcases sortCursorsBy?_exists_of_supported before supported total tail
          (fun cursor member => inputSupport cursor (by simp [member])) with
        ⟨sorted, sortedEq, sortedSupport, sortedLength⟩
      rcases insertCursorBy?_exists_of_supported before supported total head headSupport sorted
          sortedSupport with ⟨output, outputEq, outputSupport, outputLength⟩
      refine ⟨output, ?_, outputSupport, ?_⟩
      · simp [sortCursorsBy?, sortedEq, outputEq]
      · calc
          output.length = sorted.length + 1 := outputLength
          _ = tail.length + 1 := by rw [sortedLength]
          _ = (head :: tail).length := by simp [Nat.add_comm]

theorem rankedCursorChildren?_exists_of_branching_support (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : Nat) (cursor : CanonicalRerootCursor)
    (support : BranchingCursorSupport mol (fuel + 1) cursor)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, before left right = some ordering) :
    ∃ ranked,
      rankedCursorChildren? mol before cursor = some ranked ∧
      ranked.length = 3 ∧
      ∀ child, child ∈ ranked → BranchingCursorSupport mol fuel child := by
  cases support with
  | terminal _ _ label terminal =>
      let padding := branchingPaddingCursor mol cursor
      refine ⟨List.replicate 3 padding, ?_, by simp, ?_⟩
      · simpa [padding, branchingPaddingCursor] using
          rankedCursorChildren?_eq_of_linear_terminal mol before cursor terminal
      · intro child member
        have : child = padding := List.eq_of_mem_replicate member
        subst child
        exact branchingPaddingCursor_support mol fuel cursor
  | branch _ _ children label childrenEq width childrenSupport =>
      rcases sortCursorsBy?_exists_of_supported before
          (BranchingCursorSupport mol fuel) beforeTotal children childrenSupport with
        ⟨sorted, sortedEq, sortedSupport, sortedLength⟩
      let padding := branchingPaddingCursor mol cursor
      let ranked := sorted ++ List.replicate (3 - sorted.length) padding
      have notTooWide : ¬ 3 < children.length := Nat.not_lt_of_ge width
      refine ⟨ranked, ?_, ?_, ?_⟩
      · simp [rankedCursorChildren?, childrenEq, notTooWide, sortedEq,
          ranked, padding, branchingPaddingCursor, linearPaddingCursor]
      · simp [ranked, sortedLength]
        omega
      · intro child member
        rcases List.mem_append.mp member with sortedMember | paddingMember
        · exact sortedSupport child sortedMember
        · have : child = padding := List.eq_of_mem_replicate paddingMember
          subst child
          exact branchingPaddingCursor_support mol fuel cursor

abbrev BranchingCursorPair := CanonicalRerootCursor × CanonicalRerootCursor

theorem nextCursorPairs?_exists_of_branching_support (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : Nat)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ pairs,
      (∀ pair, pair ∈ pairs →
        BranchingCursorSupport mol (fuel + 1) pair.1 ∧
        BranchingCursorSupport mol (fuel + 1) pair.2) →
      ∃ next,
        nextCursorPairs? mol before pairs = some next ∧
        (∀ pair, pair ∈ next →
          BranchingCursorSupport mol fuel pair.1 ∧
          BranchingCursorSupport mol fuel pair.2) ∧
        next.length ≤ 3 * pairs.length
  | [], _ => ⟨[], rfl, by simp, by simp⟩
  | pair :: pairs, support => by
      have headSupport := support pair (by simp)
      have tailSupport : ∀ candidate, candidate ∈ pairs →
          BranchingCursorSupport mol (fuel + 1) candidate.1 ∧
          BranchingCursorSupport mol (fuel + 1) candidate.2 := by
        intro candidate member
        exact support candidate (by simp [member])
      rcases nextCursorPairs?_exists_of_branching_support mol before fuel beforeTotal pairs
          tailSupport with ⟨rest, restEq, restSupport, restLength⟩
      by_cases bothTerminal :
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true
      · refine ⟨rest, ?_, restSupport, ?_⟩
        · simp [nextCursorPairs?, restEq, bothTerminal]
        · simp only [List.length_cons]
          omega
      · rcases rankedCursorChildren?_exists_of_branching_support mol before fuel pair.1
            headSupport.1 beforeTotal with
          ⟨left, leftEq, leftLength, leftSupport⟩
        rcases rankedCursorChildren?_exists_of_branching_support mol before fuel pair.2
            headSupport.2 beforeTotal with
          ⟨right, rightEq, rightLength, rightSupport⟩
        refine ⟨left.zip right ++ rest, ?_, ?_, ?_⟩
        · simp [nextCursorPairs?, restEq, bothTerminal, leftEq, rightEq]
        · intro candidate member
          rcases List.mem_append.mp member with zipped | tail
          · have components := List.of_mem_zip zipped
            exact ⟨leftSupport candidate.1 components.1,
              rightSupport candidate.2 components.2⟩
          · exact restSupport candidate tail
        · simp [List.length_zip, leftLength, rightLength]
          omega

structure BranchingFrontierSupport (mol : RawMolecule) (fuel : Nat)
    (pairs : List BranchingCursorPair) : Prop where
  cursors : ∀ pair, pair ∈ pairs →
    BranchingCursorSupport mol fuel pair.1 ∧ BranchingCursorSupport mol fuel pair.2
  budget : pairs.length * 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap

theorem BranchingFrontierSupport.length_le_cap {mol : RawMolecule} {fuel : Nat}
    {pairs : List BranchingCursorPair} (support : BranchingFrontierSupport mol fuel pairs) :
    pairs.length ≤ RawMolecule.defaultBranchWidthCap := by
  have oneLe : 1 ≤ 3 ^ fuel := one_le_pow₀ (by omega)
  calc
    pairs.length = pairs.length * 1 := by simp
    _ ≤ pairs.length * 3 ^ fuel := Nat.mul_le_mul_left pairs.length oneLe
    _ ≤ RawMolecule.defaultBranchWidthCap := support.budget

theorem BranchingFrontierSupport.compareLabels_exists {mol : RawMolecule} {fuel : Nat}
    {pairs : List BranchingCursorPair} (support : BranchingFrontierSupport mol fuel pairs)
    (rule : CanonicalRuleStage) :
    ∃ ordering, compareCursorPairLabels mol rule pairs = some ordering := by
  have nodeTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, mol.compareCanonicalNodeRule? rule left.node right.node = some ordering := by
    intro left right leftSupport rightSupport
    cases rule with
    | rule1a =>
        rcases leftSupport.label with ⟨leftLabel, leftEq⟩
        rcases rightSupport.label with ⟨rightLabel, rightEq⟩
        exact ⟨compareCIPAtomicLabel leftLabel rightLabel, by
          simp [RawMolecule.compareCanonicalNodeRule?, leftEq, rightEq]⟩
    | rule1b => exact ⟨_, rfl⟩
    | rule2 => exact ⟨_, rfl⟩
  have listTotal : ∀ input : List BranchingCursorPair,
      (∀ pair, pair ∈ input →
        BranchingCursorSupport mol fuel pair.1 ∧ BranchingCursorSupport mol fuel pair.2) →
      ∃ ordering, compareCursorPairLabels mol rule input = some ordering := by
    intro input
    induction input with
    | nil => intro _; exact ⟨.eq, rfl⟩
    | cons pair rest ih =>
        intro allSupport
        have head := allSupport pair (by simp)
        rcases nodeTotal pair.1 pair.2 head.1 head.2 with ⟨decision, decisionEq⟩
        cases decision with
        | lt => exact ⟨.lt, by simp [compareCursorPairLabels, decisionEq]⟩
        | gt => exact ⟨.gt, by simp [compareCursorPairLabels, decisionEq]⟩
        | eq =>
            rcases ih (fun candidate member => allSupport candidate (by simp [member])) with
              ⟨tailDecision, tailEq⟩
            exact ⟨tailDecision, by simp [compareCursorPairLabels, decisionEq, tailEq]⟩
  exact listTotal pairs support.cursors

theorem BranchingFrontierSupport.next_exists {mol : RawMolecule} {fuel rankFuel : Nat}
    {pairs : List BranchingCursorPair}
    (support : BranchingFrontierSupport mol (fuel + 1) pairs)
    (fuelLe : fuel ≤ rankFuel)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, before left right = some ordering) :
    ∃ next, nextCursorPairs? mol before pairs = some next ∧
      BranchingFrontierSupport mol fuel next := by
  have localTotal : ∀ left right,
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, before left right = some ordering := by
    intro left right leftSupport rightSupport
    exact beforeTotal left right (leftSupport.mono fuelLe) (rightSupport.mono fuelLe)
  rcases nextCursorPairs?_exists_of_branching_support mol before fuel localTotal pairs
      support.cursors with ⟨next, nextEq, nextSupport, nextLength⟩
  refine ⟨next, nextEq, ⟨nextSupport, ?_⟩⟩
  calc
    next.length * 3 ^ fuel ≤ (3 * pairs.length) * 3 ^ fuel :=
      Nat.mul_le_mul_right (3 ^ fuel) nextLength
    _ = pairs.length * 3 ^ (fuel + 1) := by
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ RawMolecule.defaultBranchWidthCap := support.budget

theorem BranchingFrontierSupport.next_zero_eq_nil {mol : RawMolecule}
    {pairs : List BranchingCursorPair} (support : BranchingFrontierSupport mol 0 pairs)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    nextCursorPairs? mol before pairs = some [] := by
  exact nextCursorPairs?_terminal_list_eq_nil mol before pairs (by
    intro pair member
    have pairSupport := support.cursors pair member
    exact ⟨pairSupport.1.zero_terminal, pairSupport.2.zero_terminal⟩)

theorem compareCursorRule_branching_exists (mol : RawMolecule) (rankFuel : Nat)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, before left right = some ordering)
    (rule : CanonicalRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → BranchingFrontierSupport mol fuel pairs →
      ∃ ordering, compareCursorRule mol before rule fuel pairs = some ordering
  | 0, pairs, _, support => by
      rcases support.compareLabels_exists rule with ⟨labels, labelsEq⟩
      have withinCap := support.length_le_cap
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq]; omega⟩
      | eq =>
          have nextEq := support.next_zero_eq_nil before
          exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq]; omega⟩
  | fuel + 1, pairs, fuelLe, support => by
      rcases support.compareLabels_exists rule with ⟨labels, labelsEq⟩
      have withinCap := support.length_le_cap
      have lowerLe : fuel ≤ rankFuel := by omega
      cases labels with
      | lt => exact ⟨.lt, by simp [compareCursorRule, labelsEq]; omega⟩
      | gt => exact ⟨.gt, by simp [compareCursorRule, labelsEq]; omega⟩
      | eq =>
          rcases support.next_exists lowerLe before beforeTotal with
            ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil => exact ⟨.eq, by simp [compareCursorRule, labelsEq, nextEq]; omega⟩
          | cons pair rest =>
              rcases compareCursorRule_branching_exists mol rankFuel before beforeTotal rule fuel
                  (pair :: rest) (by omega) nextSupport with ⟨decision, decisionEq⟩
              exact ⟨decision, by simp [compareCursorRule, labelsEq, nextEq, decisionEq]; omega⟩

theorem compareCursorBranchAt_branching_supported_exists (mol : RawMolecule) :
    ∀ fuel left right,
      3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap →
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering, compareCursorBranchAt mol fuel .rule2 left right = some ordering
  | 0, left, right, _, leftSupport, rightSupport => by
      rcases leftSupport.label with ⟨leftLabel, leftEq⟩
      rcases rightSupport.label with ⟨rightLabel, rightEq⟩
      simp only [compareCursorBranchAt, RawMolecule.compareCanonicalNodeThrough?,
        RawMolecule.compareCanonicalNodeRule?, leftEq, rightEq]
      cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel <;> simp [rule1aEq]
      cases mol.compareCanonicalNodeRule .rule1b left.node right.node <;> simp
  | fuel + 1, left, right, width, leftSupport, rightSupport => by
      have lowerWidth : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap := by
        calc
          3 ^ fuel ≤ 3 ^ (fuel + 1) := by
            exact Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ RawMolecule.defaultBranchWidthCap := width
      let before := compareCursorBranchAt mol fuel .rule2
      have beforeTotal : ∀ siblingLeft siblingRight,
          BranchingCursorSupport mol fuel siblingLeft →
          BranchingCursorSupport mol fuel siblingRight →
          ∃ ordering, before siblingLeft siblingRight = some ordering := by
        intro siblingLeft siblingRight siblingLeftSupport siblingRightSupport
        exact compareCursorBranchAt_branching_supported_exists mol fuel siblingLeft siblingRight
          lowerWidth siblingLeftSupport siblingRightSupport
      have frontier : BranchingFrontierSupport mol (fuel + 1) [(left, right)] :=
        ⟨by simpa using And.intro leftSupport rightSupport, by simpa using width⟩
      rcases compareCursorRule_branching_exists mol fuel before beforeTotal .rule1a
          (fuel + 1) [(left, right)] (by omega) frontier with ⟨rule1a, rule1aEq⟩
      rcases compareCursorRule_branching_exists mol fuel before beforeTotal .rule1b
          (fuel + 1) [(left, right)] (by omega) frontier with ⟨rule1b, rule1bEq⟩
      rcases compareCursorRule_branching_exists mol fuel before beforeTotal .rule2
          (fuel + 1) [(left, right)] (by omega) frontier with ⟨rule2, rule2Eq⟩
      cases rule1a <;> cases rule1b <;> cases rule2 <;>
        simp [compareCursorBranchAt, before, rule1aEq, rule1bEq, rule2Eq]

end TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws
