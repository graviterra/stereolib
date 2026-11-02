import TetraStereo.OneCenter.ProductionCIPLinearComparatorCompleteness
import TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness

/-! Structural completeness of the full production Rules-1--5 occurrence comparator on bounded,
acyclic, linear ligand digraphs with no auxiliary descriptor state. -/

open RawMolecule
open ProductionCIPRerootComparatorLaws
open ProductionCIPOccurrenceDescriptorComparatorLaws

theorem linearFrontier_descriptorLabels_empty_eq {mol : RawMolecule}
    {fuel : Nat} {pairs : List LinearCursorPair}
    (_support : LinearFrontierSupport mol fuel pairs) (stage : RawDescriptorRuleStage) :
    compareOccurrenceDescriptorPairLabels [] stage pairs = .eq := by
  clear _support
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp [compareOccurrenceDescriptorPairLabels, occurrenceNodePriority,
        OccurrenceAuxState.factAt?, ih]

theorem occurrenceRule4bReferences_empty (mol : RawMolecule) :
    ∀ fuel frontier, occurrenceRule4bReferences mol [] fuel frontier = [] := by
  intro fuel
  induction fuel with
  | zero => intro frontier; rfl
  | succ fuel ih =>
      intro frontier
      cases frontier with
      | nil => rfl
      | cons cursor cursors =>
          simp [occurrenceRule4bReferences, OccurrenceAuxState.factAt?, ih]

theorem nextOccurrenceDescriptorPairs?_terminal_list_eq_nil (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∀ pairs : List LinearCursorPair,
      (∀ pair, pair ∈ pairs →
        cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true) →
      nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some []
  | [], _ => rfl
  | pair :: pairs, terminal => by
      have head := terminal pair (by simp)
      have tail : ∀ candidate, candidate ∈ pairs →
          cursorTerminal mol candidate.1 = true ∧
          cursorTerminal mol candidate.2 = true := by
        intro candidate member
        exact terminal candidate (by simp [member])
      simp [nextOccurrenceDescriptorPairs?,
        nextOccurrenceDescriptorPairs?_terminal_list_eq_nil
          mol beforeLeft beforeRight pairs tail, head.1, head.2]

theorem linearFrontier_nextOccurrence_eq_nextCursor
    {mol : RawMolecule} {fuel : Nat} {pairs : List LinearCursorPair}
    (support : LinearFrontierSupport mol fuel pairs)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs =
      nextCursorPairs? mol beforeLeft pairs := by
  cases support with
  | nil => rfl
  | main left right tail leftSupport rightSupport tailLength tailSupport =>
      have tailTerminal : ∀ pair, pair ∈ tail →
          cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true := by
        intro pair member
        exact ⟨(tailSupport pair member).2.2.1, (tailSupport pair member).2.2.2⟩
      have occurrenceTail := nextOccurrenceDescriptorPairs?_terminal_list_eq_nil
        mol beforeLeft beforeRight tail tailTerminal
      have cursorTail := nextCursorPairs?_terminal_list_eq_nil
        mol beforeLeft tail tailTerminal
      cases leftSupport with
      | terminal _ _ leftLabel leftTerminal =>
          cases rightSupport with
          | terminal _ _ rightLabel rightTerminal =>
              simp [nextOccurrenceDescriptorPairs?, nextCursorPairs?, occurrenceTail, cursorTail,
                leftTerminal, rightTerminal]
          | step _ _ rightChild rightLabel rightChildren rightChildSupport =>
              have rightNotTerminal :=
                cursor_not_terminal_of_children_singleton mol right rightChild rightChildren
              have leftOccurrenceRank := rankedCursorChildren?_eq_of_linear_terminal
                mol beforeLeft left leftTerminal
              have leftCursorRank := leftOccurrenceRank
              have rightOccurrenceRank := rankedCursorChildren?_eq_of_linear_step
                mol beforeRight right rightChild rightChildren
              have rightCursorRank := rankedCursorChildren?_eq_of_linear_step
                mol beforeLeft right rightChild rightChildren
              simp [nextOccurrenceDescriptorPairs?, nextCursorPairs?, occurrenceTail, cursorTail,
                leftTerminal, rightNotTerminal, leftOccurrenceRank, leftCursorRank,
                rightOccurrenceRank, rightCursorRank]
      | step _ _ leftChild leftLabel leftChildren leftChildSupport =>
          have leftNotTerminal :=
            cursor_not_terminal_of_children_singleton mol left leftChild leftChildren
          cases rightSupport with
          | terminal _ _ rightLabel rightTerminal =>
              have leftOccurrenceRank := rankedCursorChildren?_eq_of_linear_step
                mol beforeLeft left leftChild leftChildren
              have leftCursorRank := leftOccurrenceRank
              have rightOccurrenceRank := rankedCursorChildren?_eq_of_linear_terminal
                mol beforeRight right rightTerminal
              have rightCursorRank := rankedCursorChildren?_eq_of_linear_terminal
                mol beforeLeft right rightTerminal
              simp [nextOccurrenceDescriptorPairs?, nextCursorPairs?, occurrenceTail, cursorTail,
                leftNotTerminal, rightTerminal, leftOccurrenceRank, leftCursorRank,
                rightOccurrenceRank, rightCursorRank]
          | step _ _ rightChild rightLabel rightChildren rightChildSupport =>
              have rightNotTerminal :=
                cursor_not_terminal_of_children_singleton mol right rightChild rightChildren
              have leftOccurrenceRank := rankedCursorChildren?_eq_of_linear_step
                mol beforeLeft left leftChild leftChildren
              have leftCursorRank := leftOccurrenceRank
              have rightOccurrenceRank := rankedCursorChildren?_eq_of_linear_step
                mol beforeRight right rightChild rightChildren
              have rightCursorRank := rankedCursorChildren?_eq_of_linear_step
                mol beforeLeft right rightChild rightChildren
              simp [nextOccurrenceDescriptorPairs?, nextCursorPairs?, occurrenceTail, cursorTail,
                leftNotTerminal, rightNotTerminal, leftOccurrenceRank, leftCursorRank,
                rightOccurrenceRank, rightCursorRank]

theorem linearFrontier_nextOccurrence_exists {mol : RawMolecule} {fuel : Nat}
    {pairs : List LinearCursorPair} (support : LinearFrontierSupport mol (fuel + 1) pairs)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∃ next, nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some next ∧
      LinearFrontierSupport mol fuel next := by
  rcases support.next_exists beforeLeft with ⟨next, nextEq, nextSupport⟩
  refine ⟨next, ?_, nextSupport⟩
  rw [linearFrontier_nextOccurrence_eq_nextCursor support beforeLeft beforeRight]
  exact nextEq

theorem linearFrontier_nextOccurrence_zero_eq_nil {mol : RawMolecule}
    {pairs : List LinearCursorPair} (support : LinearFrontierSupport mol 0 pairs)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs = some [] := by
  rw [linearFrontier_nextOccurrence_eq_nextCursor support beforeLeft beforeRight]
  exact support.next_zero_eq_nil beforeLeft

theorem compareOccurrenceDescriptorRule_linear_empty_eq (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, LinearFrontierSupport mol fuel pairs →
      compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight stage fuel pairs = some .eq
  | 0, pairs, support => by
      have labelsEq := linearFrontier_descriptorLabels_empty_eq support stage
      have nextEq := linearFrontier_nextOccurrence_zero_eq_nil support beforeLeft beforeRight
      have width := support.length_le_three
      simp [compareOccurrenceDescriptorRule, labelsEq, nextEq,
        RawMolecule.defaultBranchWidthCap]
      omega
  | fuel + 1, pairs, support => by
      have labelsEq := linearFrontier_descriptorLabels_empty_eq support stage
      have width := support.length_le_three
      rcases linearFrontier_nextOccurrence_exists support beforeLeft beforeRight with
        ⟨next, nextEq, nextSupport⟩
      cases next with
      | nil =>
          simp [compareOccurrenceDescriptorRule, labelsEq, nextEq,
            RawMolecule.defaultBranchWidthCap]
          omega
      | cons pair rest =>
          have deeper := compareOccurrenceDescriptorRule_linear_empty_eq
            mol beforeLeft beforeRight stage fuel (pair :: rest) nextSupport
          simp [compareOccurrenceDescriptorRule, labelsEq, nextEq, deeper,
            RawMolecule.defaultBranchWidthCap]
          omega

theorem compareOccurrenceDescriptorAtTiedRoot?_linear_empty_eq (mol : RawMolecule)
    (fuel : Nat) (stage : RawDescriptorRuleStage) (left right : CanonicalRerootCursor)
    (leftSupport : LinearCursorSupport mol fuel left)
    (rightSupport : LinearCursorSupport mol fuel right) :
    compareOccurrenceDescriptorAtTiedRoot? mol [] fuel stage left right = some .eq := by
  let beforeLeft := compareOccurrenceDescriptorBranchAt mol [] fuel stage.leftInternal
  let beforeRight := compareOccurrenceDescriptorBranchAt mol [] fuel stage.rightInternal
  have frontier : LinearFrontierSupport mol fuel [(left, right)] :=
    .main left right [] leftSupport rightSupport (by simp) (by simp)
  have compareEq : ∀ selected,
      compareOccurrenceDescriptorRule mol [] beforeLeft beforeRight selected fuel [(left, right)] =
        some .eq := by
    intro selected
    exact compareOccurrenceDescriptorRule_linear_empty_eq
      mol beforeLeft beforeRight selected fuel [(left, right)] frontier
  cases stage <;>
    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, compareEq]

inductive LinearCursorAcyclic (mol : RawMolecule) (cycleFuel : Nat) :
    CanonicalRerootCursor → Prop
  | terminal (cursor : CanonicalRerootCursor)
      (acyclic : mol.atomLiesInCycle cycleFuel cursor.node.atom = false)
      (isTerminal : cursorTerminal mol cursor = true) :
      LinearCursorAcyclic mol cycleFuel cursor
  | step (cursor child : CanonicalRerootCursor)
      (acyclic : mol.atomLiesInCycle cycleFuel cursor.node.atom = false)
      (children : cursor.children mol = [child])
      (childAcyclic : LinearCursorAcyclic mol cycleFuel child) :
      LinearCursorAcyclic mol cycleFuel cursor

theorem LinearCursorAcyclic.root {mol : RawMolecule} {cycleFuel : Nat}
    {cursor : CanonicalRerootCursor} (acyclic : LinearCursorAcyclic mol cycleFuel cursor) :
    mol.atomLiesInCycle cycleFuel cursor.node.atom = false := by
  cases acyclic with
  | terminal _ root _ => exact root
  | step _ _ root _ _ => exact root

structure AcyclicLinearCursorSupport (mol : RawMolecule) (fuel : Nat)
    (cursor : CanonicalRerootCursor) : Prop where
  linear : LinearCursorSupport mol fuel cursor
  acyclic : LinearCursorAcyclic mol fuel cursor

theorem compareOccurrenceBranches?_acyclic_linear_empty_eq_raw
    (mol : RawMolecule) (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftSupport : AcyclicLinearCursorSupport mol fuel left)
    (rightSupport : AcyclicLinearCursorSupport mol fuel right) :
    ∃ ordering,
      compareCursorBranchAt mol fuel .rule2 left right = some ordering ∧
      compareOccurrenceBranches? mol [] fuel left right = some { ordering := ordering } := by
  rcases compareCursorBranchAt_linear_supported_exists mol fuel left right
      leftSupport.linear rightSupport.linear with ⟨ordering, rawEq⟩
  have gateFalse : occurrenceRootsProvedAutomorphic mol fuel left right ordering = false := by
    simp [occurrenceRootsProvedAutomorphic, leftSupport.acyclic.root]
  have constitutionalEq : certifiedConstitutionalStage? mol fuel left right = some ordering := by
    simp [certifiedConstitutionalStage?, rawEq, gateFalse]
  refine ⟨ordering, rawEq, ?_⟩
  cases ordering with
  | lt => simp [compareOccurrenceBranches?, constitutionalEq]
  | gt => simp [compareOccurrenceBranches?, constitutionalEq]
  | eq =>
      have rule4aEq := compareOccurrenceDescriptorAtTiedRoot?_linear_empty_eq
        mol fuel .rule4a left right leftSupport.linear rightSupport.linear
      have rule5REq := compareOccurrenceDescriptorAtTiedRoot?_linear_empty_eq
        mol fuel (.rule5 .R .R) left right leftSupport.linear rightSupport.linear
      have rule5SEq := compareOccurrenceDescriptorAtTiedRoot?_linear_empty_eq
        mol fuel (.rule5 .S .S) left right leftSupport.linear rightSupport.linear
      have rule4bEq : compareOccurrenceRule4b? mol [] fuel left right = some .eq := by
        simp [compareOccurrenceRule4b?, occurrenceRule4bReferences_empty]
      have rule5Eq : compareOccurrenceRule5? mol [] fuel left right =
          some { ordering := .eq, pseudo := false } := by
        simp [compareOccurrenceRule5?, rule5REq, rule5SEq]
      simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq, rule5Eq]

end TetraStereo.OneCenter.ProductionCIPLinearOccurrenceComparatorCompleteness
