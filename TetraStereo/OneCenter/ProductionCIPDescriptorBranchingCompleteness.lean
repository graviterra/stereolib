import TetraStereo.OneCenter.ProductionCIPBranchingOccurrenceComparatorCompleteness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.ProductionCIPDescriptorBranchingCompleteness

/-! Completeness for descriptor-bearing bounded branching trees.  Descriptor priorities are
total; the remaining executable obligations are recursive child sorting, frontier capacity, and
Rule-4b reference-arity compatibility. -/

open RawMolecule
open ProductionCIPRerootComparatorLaws
open ProductionCIPLinearOccurrenceComparatorCompleteness
open ProductionCIPBranchingOccurrenceComparatorCompleteness

theorem compareOccurrenceDescriptorRule_branching_exists (mol : RawMolecule)
    (state : OccurrenceAuxState) (rankFuel : Nat)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, beforeRight left right = some ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → BranchingFrontierSupport mol fuel pairs →
      ∃ ordering,
        compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel pairs =
          some ordering
  | 0, pairs, _, support => by
      have withinCap := support.length_le_cap
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | eq =>
          have nextEq := branchingFrontier_nextOccurrence_zero_eq_nil
            support beforeLeft beforeRight
          exact ⟨.eq, by
            simp [compareOccurrenceDescriptorRule, labels, nextEq]
            omega⟩
  | fuel + 1, pairs, fuelLe, support => by
      have withinCap := support.length_le_cap
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorRule, labels]; omega⟩
      | eq =>
          have lowerLe : fuel ≤ rankFuel := by omega
          rcases branchingFrontier_nextOccurrence_exists support lowerLe beforeLeft beforeRight
              beforeLeftTotal beforeRightTotal with ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil => exact ⟨.eq, by
              simp [compareOccurrenceDescriptorRule, labels, nextEq]
              omega⟩
          | cons pair rest =>
              rcases compareOccurrenceDescriptorRule_branching_exists mol state rankFuel
                  beforeLeft beforeRight beforeLeftTotal beforeRightTotal stage fuel
                  (pair :: rest) (by omega) nextSupport with ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorRule, labels, nextEq, decisionEq]
                omega⟩

theorem compareOccurrenceDescriptorBranchAt_branching_exists (mol : RawMolecule)
    (state : OccurrenceAuxState) :
    ∀ fuel stage left right,
      3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap →
      BranchingCursorSupport mol fuel left → BranchingCursorSupport mol fuel right →
      ∃ ordering,
        compareOccurrenceDescriptorBranchAt mol state fuel stage left right = some ordering
  | 0, stage, left, right, width, leftSupport, rightSupport => by
      rcases compareCursorBranchAt_branching_supported_exists mol 0 left right width
          leftSupport rightSupport with ⟨constitutional, rawEq⟩
      have throughEq : mol.compareCanonicalNodeThrough? .rule2 left.node right.node =
          some constitutional := rawEq
      cases constitutional with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorBranchAt, throughEq]⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorBranchAt, throughEq]⟩
      | eq =>
          cases rule4a : compare
              (occurrenceNodePriority state .rule4a true left)
              (occurrenceNodePriority state .rule4a false right) with
          | lt => exact ⟨.lt, by
              cases stage <;>
                simp [compareOccurrenceDescriptorBranchAt, throughEq, rule4a]⟩
          | gt => exact ⟨.gt, by
              cases stage <;>
                simp [compareOccurrenceDescriptorBranchAt, throughEq, rule4a]⟩
          | eq =>
              cases stage with
              | rule4a => exact ⟨.eq, by
                  simp [compareOccurrenceDescriptorBranchAt, throughEq, rule4a]⟩
              | rule4b leftReference rightReference =>
                  let decision := compare
                    (occurrenceNodePriority state (.rule4b leftReference rightReference) true left)
                    (occurrenceNodePriority state (.rule4b leftReference rightReference) false right)
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAt, throughEq, rule4a, decision]⟩
              | rule4c =>
                  let decision := compare
                    (occurrenceNodePriority state .rule4c true left)
                    (occurrenceNodePriority state .rule4c false right)
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAt, throughEq, rule4a, decision]⟩
              | rule5 leftReference rightReference =>
                  let decision := compare
                    (occurrenceNodePriority state (.rule5 leftReference rightReference) true left)
                    (occurrenceNodePriority state (.rule5 leftReference rightReference) false right)
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAt, throughEq, rule4a, decision]⟩
  | fuel + 1, stage, left, right, width, leftSupport, rightSupport => by
      rcases compareCursorBranchAt_branching_supported_exists mol (fuel + 1) left right width
          leftSupport rightSupport with ⟨constitutional, rawEq⟩
      have lowerWidth : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap := by
        calc
          3 ^ fuel ≤ 3 ^ (fuel + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ RawMolecule.defaultBranchWidthCap := width
      let beforeLeft := compareOccurrenceDescriptorBranchAt mol state fuel stage.leftInternal
      let beforeRight := compareOccurrenceDescriptorBranchAt mol state fuel stage.rightInternal
      have beforeLeftTotal : ∀ childLeft childRight,
          BranchingCursorSupport mol fuel childLeft →
          BranchingCursorSupport mol fuel childRight →
          ∃ decision, beforeLeft childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        exact compareOccurrenceDescriptorBranchAt_branching_exists mol state fuel
          stage.leftInternal childLeft childRight lowerWidth childLeftSupport childRightSupport
      have beforeRightTotal : ∀ childLeft childRight,
          BranchingCursorSupport mol fuel childLeft →
          BranchingCursorSupport mol fuel childRight →
          ∃ decision, beforeRight childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        exact compareOccurrenceDescriptorBranchAt_branching_exists mol state fuel
          stage.rightInternal childLeft childRight lowerWidth childLeftSupport childRightSupport
      have frontier : BranchingFrontierSupport mol (fuel + 1) [(left, right)] :=
        ⟨by simpa using And.intro leftSupport rightSupport, by simpa using width⟩
      have compareExists : ∀ selected,
          ∃ decision,
            compareOccurrenceDescriptorRule mol state beforeLeft beforeRight selected (fuel + 1)
              [(left, right)] = some decision := by
        intro selected
        exact compareOccurrenceDescriptorRule_branching_exists mol state fuel
          beforeLeft beforeRight beforeLeftTotal beforeRightTotal selected (fuel + 1)
            [(left, right)] (by omega) frontier
      cases constitutional with
      | lt => exact ⟨.lt, by simp [compareOccurrenceDescriptorBranchAt, rawEq]⟩
      | gt => exact ⟨.gt, by simp [compareOccurrenceDescriptorBranchAt, rawEq]⟩
      | eq =>
          rcases compareExists .rule4a with ⟨rule4a, rule4aEq⟩
          cases rule4a with
          | lt => exact ⟨.lt, by
              simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                rule4aEq]⟩
          | gt => exact ⟨.gt, by
              simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                rule4aEq]⟩
          | eq =>
              cases stage with
              | rule4a => exact ⟨.eq, by
                  simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                    rule4aEq]⟩
              | rule4b leftReference rightReference =>
                  rcases compareExists (.rule4b leftReference rightReference) with
                    ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                      rule4aEq, decisionEq]⟩
              | rule4c =>
                  rcases compareExists .rule4c with ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                      rule4aEq, decisionEq]⟩
              | rule5 leftReference rightReference =>
                  rcases compareExists .rule4c with ⟨rule4c, rule4cEq⟩
                  cases rule4c with
                  | lt => exact ⟨.lt, by
                      simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                        rule4aEq, rule4cEq]⟩
                  | gt => exact ⟨.gt, by
                      simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                        rule4aEq, rule4cEq]⟩
                  | eq =>
                      rcases compareExists (.rule5 leftReference rightReference) with
                        ⟨decision, decisionEq⟩
                      exact ⟨decision, by
                        simp [compareOccurrenceDescriptorBranchAt, rawEq, beforeLeft, beforeRight,
                          rule4aEq, rule4cEq, decisionEq]⟩

theorem compareOccurrenceDescriptorAtTiedRoot?_branching_exists (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (stage : RawDescriptorRuleStage)
    (left right : CanonicalRerootCursor)
    (width : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftSupport : BranchingCursorSupport mol fuel left)
    (rightSupport : BranchingCursorSupport mol fuel right) :
    ∃ ordering,
      compareOccurrenceDescriptorAtTiedRoot? mol state fuel stage left right = some ordering := by
  let beforeLeft := compareOccurrenceDescriptorBranchAt mol state fuel stage.leftInternal
  let beforeRight := compareOccurrenceDescriptorBranchAt mol state fuel stage.rightInternal
  have beforeLeftTotal : ∀ childLeft childRight,
      BranchingCursorSupport mol fuel childLeft → BranchingCursorSupport mol fuel childRight →
      ∃ decision, beforeLeft childLeft childRight = some decision := by
    intro childLeft childRight childLeftSupport childRightSupport
    exact compareOccurrenceDescriptorBranchAt_branching_exists mol state fuel
      stage.leftInternal childLeft childRight width childLeftSupport childRightSupport
  have beforeRightTotal : ∀ childLeft childRight,
      BranchingCursorSupport mol fuel childLeft → BranchingCursorSupport mol fuel childRight →
      ∃ decision, beforeRight childLeft childRight = some decision := by
    intro childLeft childRight childLeftSupport childRightSupport
    exact compareOccurrenceDescriptorBranchAt_branching_exists mol state fuel
      stage.rightInternal childLeft childRight width childLeftSupport childRightSupport
  have frontier : BranchingFrontierSupport mol fuel [(left, right)] :=
    ⟨by simpa using And.intro leftSupport rightSupport, by simpa using width⟩
  have compareExists : ∀ selected,
      ∃ decision,
        compareOccurrenceDescriptorRule mol state beforeLeft beforeRight selected fuel
          [(left, right)] = some decision := by
    intro selected
    exact compareOccurrenceDescriptorRule_branching_exists mol state fuel beforeLeft beforeRight
      beforeLeftTotal beforeRightTotal selected fuel [(left, right)] (by omega) frontier
  rcases compareExists .rule4a with ⟨rule4a, rule4aEq⟩
  cases rule4a with
  | lt => exact ⟨.lt, by
      simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq]⟩
  | gt => exact ⟨.gt, by
      simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq]⟩
  | eq =>
      cases stage with
      | rule4a => exact ⟨.eq, by
          simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq]⟩
      | rule4b leftReference rightReference =>
          rcases compareExists (.rule4b leftReference rightReference) with
            ⟨decision, decisionEq⟩
          exact ⟨decision, by
            simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq,
              decisionEq]⟩
      | rule4c =>
          cases lowercase : state.any fun fact => !fact.uppercase with
          | false => exact ⟨.eq, by
              simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq,
                lowercase]⟩
          | true =>
              rcases compareExists .rule4c with ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq,
                  lowercase, decisionEq]⟩
      | rule5 leftReference rightReference =>
          cases lowercase : state.any fun fact => !fact.uppercase with
          | false =>
              rcases compareExists (.rule5 leftReference rightReference) with
                ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq,
                  lowercase, decisionEq]⟩
          | true =>
              rcases compareExists .rule4c with ⟨rule4c, rule4cEq⟩
              cases rule4c with
              | lt => exact ⟨.lt, by
                  simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq,
                    lowercase, rule4cEq]⟩
              | gt => exact ⟨.gt, by
                  simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq,
                    lowercase, rule4cEq]⟩
              | eq =>
                  rcases compareExists (.rule5 leftReference rightReference) with
                    ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, rule4cEq, decisionEq]⟩

theorem compareOccurrenceRule4cWithWitness_branching_exists (mol : RawMolecule)
    (state : OccurrenceAuxState) (rankFuel : Nat)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ left right,
      BranchingCursorSupport mol rankFuel left → BranchingCursorSupport mol rankFuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → BranchingFrontierSupport mol fuel pairs →
      ∃ decision,
        compareOccurrenceRule4cWithWitness mol state before before fuel pairs = some decision
  | 0, pairs, _, support => by
      have withinCap := support.length_le_cap
      cases labels : compareOccurrenceRule4cPairLabelsWithWitness state pairs with
      | mk ordering carrier =>
          cases ordering with
          | lt => exact ⟨{ ordering := .lt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitness, labels]
              omega⟩
          | gt => exact ⟨{ ordering := .gt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitness, labels]
              omega⟩
          | eq =>
              have nextEq := branchingFrontier_nextOccurrence_zero_eq_nil support before before
              exact ⟨{ ordering := .eq }, by
                simp [compareOccurrenceRule4cWithWitness, labels, nextEq]
                omega⟩
  | fuel + 1, pairs, fuelLe, support => by
      have withinCap := support.length_le_cap
      cases labels : compareOccurrenceRule4cPairLabelsWithWitness state pairs with
      | mk ordering carrier =>
          cases ordering with
          | lt => exact ⟨{ ordering := .lt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitness, labels]
              omega⟩
          | gt => exact ⟨{ ordering := .gt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitness, labels]
              omega⟩
          | eq =>
              have lowerLe : fuel ≤ rankFuel := by omega
              rcases branchingFrontier_nextOccurrence_exists support lowerLe before before
                  beforeTotal beforeTotal with ⟨next, nextEq, nextSupport⟩
              cases next with
              | nil => exact ⟨{ ordering := .eq }, by
                  simp [compareOccurrenceRule4cWithWitness, labels, nextEq]
                  omega⟩
              | cons pair rest =>
                  rcases compareOccurrenceRule4cWithWitness_branching_exists mol state rankFuel
                      before beforeTotal fuel (pair :: rest) (by omega) nextSupport with
                    ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceRule4cWithWitness, labels, nextEq, decisionEq]
                    omega⟩

theorem compareOccurrenceRule4b?_branching_exists_of_uniform_arity
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel arity : Nat)
    (left right : CanonicalRerootCursor)
    (width : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftSupport : BranchingCursorSupport mol fuel left)
    (rightSupport : BranchingCursorSupport mol fuel right)
    (arityLe : arity ≤ 2)
    (leftArity : (occurrenceRule4bReferences mol state fuel [left]).length = arity)
    (rightArity : (occurrenceRule4bReferences mol state fuel [right]).length = arity) :
    ∃ ordering, compareOccurrenceRule4b? mol state fuel left right = some ordering := by
  let leftRefs := occurrenceRule4bReferences mol state fuel [left]
  let rightRefs := occurrenceRule4bReferences mol state fuel [right]
  have leftLength : leftRefs.length = arity := leftArity
  have rightLength : rightRefs.length = arity := rightArity
  have tiedTotal : ∀ stage selectedLeft selectedRight,
      BranchingCursorSupport mol fuel selectedLeft →
      BranchingCursorSupport mol fuel selectedRight →
      ∃ ordering,
        compareOccurrenceDescriptorAtTiedRoot? mol state fuel stage selectedLeft selectedRight =
          some ordering := by
    intro stage selectedLeft selectedRight selectedLeftSupport selectedRightSupport
    exact compareOccurrenceDescriptorAtTiedRoot?_branching_exists mol state fuel stage
      selectedLeft selectedRight width selectedLeftSupport selectedRightSupport
  rcases (show arity = 0 ∨ arity = 1 ∨ arity = 2 by omega) with
    rfl | rfl | rfl
  · have leftNil : leftRefs = [] := List.length_eq_zero_iff.mp leftLength
    have rightNil : rightRefs = [] := List.length_eq_zero_iff.mp rightLength
    exact ⟨.eq, by simp [compareOccurrenceRule4b?, leftRefs, rightRefs, leftNil, rightNil]⟩
  · rcases List.length_eq_one_iff.mp leftLength with ⟨leftReference, leftEq⟩
    rcases List.length_eq_one_iff.mp rightLength with ⟨rightReference, rightEq⟩
    rcases tiedTotal (.rule4b leftReference rightReference) left right leftSupport rightSupport with
      ⟨decision, decisionEq⟩
    exact ⟨decision, by
      simp [compareOccurrenceRule4b?, leftRefs, rightRefs, leftEq, rightEq, decisionEq]⟩
  · rcases List.length_eq_two.mp leftLength with ⟨leftFirst, leftSecond, leftEq⟩
    rcases List.length_eq_two.mp rightLength with ⟨rightFirst, rightSecond, rightEq⟩
    change occurrenceRule4bReferences mol state fuel [left] =
      [leftFirst, leftSecond] at leftEq
    change occurrenceRule4bReferences mol state fuel [right] =
      [rightFirst, rightSecond] at rightEq
    rcases tiedTotal (.rule4b leftFirst leftSecond) left left leftSupport leftSupport with
      ⟨leftRankDecision, leftRankEq⟩
    rcases tiedTotal (.rule4b rightFirst rightSecond) right right rightSupport rightSupport with
      ⟨rightRankDecision, rightRankEq⟩
    have rankedLeft : ∃ ranked,
        rankOccurrenceRule4bReferences? mol state fuel left [leftFirst, leftSecond] = some ranked := by
      cases leftRankDecision with
      | lt => exact ⟨[leftSecond, leftFirst], by
          simp [rankOccurrenceRule4bReferences?, leftRankEq]⟩
      | eq => exact ⟨[leftFirst, leftSecond], by
          simp [rankOccurrenceRule4bReferences?, leftRankEq]⟩
      | gt => exact ⟨[leftFirst, leftSecond], by
          simp [rankOccurrenceRule4bReferences?, leftRankEq]⟩
    have rankedRight : ∃ ranked,
        rankOccurrenceRule4bReferences? mol state fuel right [rightFirst, rightSecond] =
          some ranked := by
      cases rightRankDecision with
      | lt => exact ⟨[rightSecond, rightFirst], by
          simp [rankOccurrenceRule4bReferences?, rightRankEq]⟩
      | eq => exact ⟨[rightFirst, rightSecond], by
          simp [rankOccurrenceRule4bReferences?, rightRankEq]⟩
      | gt => exact ⟨[rightFirst, rightSecond], by
          simp [rankOccurrenceRule4bReferences?, rightRankEq]⟩
    rcases rankedLeft with ⟨leftRanked, leftRankedEq⟩
    rcases rankedRight with ⟨rightRanked, rightRankedEq⟩
    rcases tiedTotal
        (.rule4b (leftRanked.getD 0 .R) (rightRanked.getD 0 .R)) left right
        leftSupport rightSupport with ⟨first, firstEq⟩
    change compareOccurrenceDescriptorAtTiedRoot? mol state fuel
      (.rule4b (leftRanked[0]?.getD .R) (rightRanked[0]?.getD .R)) left right =
        some first at firstEq
    cases first with
    | lt => exact ⟨.lt, by
        simp [compareOccurrenceRule4b?, leftEq, rightEq,
          leftRankedEq, rightRankedEq, firstEq]⟩
    | gt => exact ⟨.gt, by
        simp [compareOccurrenceRule4b?, leftEq, rightEq,
          leftRankedEq, rightRankedEq, firstEq]⟩
    | eq =>
        rcases tiedTotal
            (.rule4b (leftRanked.getD 1 .S) (rightRanked.getD 1 .S)) left right
            leftSupport rightSupport with ⟨second, secondEq⟩
        change compareOccurrenceDescriptorAtTiedRoot? mol state fuel
          (.rule4b (leftRanked[1]?.getD .S) (rightRanked[1]?.getD .S)) left right =
            some second at secondEq
        exact ⟨second, by
          simp [compareOccurrenceRule4b?, leftEq, rightEq,
            leftRankedEq, rightRankedEq, firstEq, secondEq]⟩

theorem compareOccurrenceRule5?_branching_exists
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor)
    (width : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftSupport : BranchingCursorSupport mol fuel left)
    (rightSupport : BranchingCursorSupport mol fuel right) :
    ∃ decision, compareOccurrenceRule5? mol state fuel left right = some decision := by
  rcases compareOccurrenceDescriptorAtTiedRoot?_branching_exists mol state fuel
      (.rule5 .R .R) left right width leftSupport rightSupport with ⟨cmpR, cmpREq⟩
  rcases compareOccurrenceDescriptorAtTiedRoot?_branching_exists mol state fuel
      (.rule5 .S .S) left right width leftSupport rightSupport with ⟨cmpS, cmpSEq⟩
  cases cmpR with
  | lt => exact ⟨{ ordering := .lt, pseudo := cmpS != .lt }, by
      simp [compareOccurrenceRule5?, cmpREq, cmpSEq]⟩
  | gt => exact ⟨{ ordering := .gt, pseudo := cmpS != .gt }, by
      simp [compareOccurrenceRule5?, cmpREq, cmpSEq]⟩
  | eq => exact ⟨{ ordering := .eq, pseudo := false }, by
      simp [compareOccurrenceRule5?, cmpREq, cmpSEq]⟩

/-- Unary, root-relative reasons why the legacy pairwise cyclic-automorphism gate cannot fire. -/
inductive RootRelativeGateNeutral (mol : RawMolecule) (fuel : Nat) :
    CanonicalRerootCursor → Prop
  | atomAcyclic (cursor : CanonicalRerootCursor)
      (acyclic : mol.atomLiesInCycle fuel cursor.node.atom = false) :
      RootRelativeGateNeutral mol fuel cursor
  | noPrevious (cursor : CanonicalRerootCursor) (none : cursor.previous? = none) :
      RootRelativeGateNeutral mol fuel cursor
  | nonReal (cursor : CanonicalRerootCursor)
      (provenance : cursor.node.provenance ≠ .realAtom) :
      RootRelativeGateNeutral mol fuel cursor
  | incomingCyclic (cursor : CanonicalRerootCursor) (root : CanonicalBranchNode)
      (previous : cursor.previous? = some root)
      (cyclic : mol.atomLiesInCycle fuel root.atom = true) :
      RootRelativeGateNeutral mol fuel cursor
  | noAutomorphicPartner (cursor : CanonicalRerootCursor) (root : CanonicalBranchNode)
      (previous : cursor.previous? = some root)
      (noSwap : ∀ other,
        mol.hasConstitutionAutomorphismSwapping root.atom cursor.node.atom other = false) :
      RootRelativeGateNeutral mol fuel cursor

theorem RootRelativeGateNeutral.gate_false {mol : RawMolecule} {fuel : Nat}
    {left : CanonicalRerootCursor} (neutral : RootRelativeGateNeutral mol fuel left)
    (right : CanonicalRerootCursor) (ordering : Ordering) :
    occurrenceRootsProvedAutomorphic mol fuel left right ordering = false := by
  cases neutral with
  | atomAcyclic acyclic =>
      simp [occurrenceRootsProvedAutomorphic, acyclic]
  | noPrevious none =>
      simp [occurrenceRootsProvedAutomorphic, none]
  | nonReal provenance =>
      cases leftPrevious : left.previous? <;>
        cases rightPrevious : right.previous? <;>
          simp [occurrenceRootsProvedAutomorphic, leftPrevious, rightPrevious, provenance]
  | incomingCyclic root previous cyclic =>
      cases rightPrevious : right.previous? <;>
        simp [occurrenceRootsProvedAutomorphic, previous, rightPrevious, cyclic]
  | noAutomorphicPartner root previous noSwap =>
      cases rightPrevious : right.previous? <;>
        simp [occurrenceRootsProvedAutomorphic, previous, rightPrevious, noSwap]

theorem compareOccurrenceBranches?_descriptor_branching_exists
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel arity : Nat)
    (left right : CanonicalRerootCursor)
    (width : 3 ^ fuel ≤ RawMolecule.defaultBranchWidthCap)
    (leftSupport : BranchingCursorSupport mol fuel left)
    (rightSupport : BranchingCursorSupport mol fuel right)
    (leftNeutral : RootRelativeGateNeutral mol fuel left)
    (arityLe : arity ≤ 2)
    (leftArity : (occurrenceRule4bReferences mol state fuel [left]).length = arity)
    (rightArity : (occurrenceRule4bReferences mol state fuel [right]).length = arity) :
    ∃ comparison, compareOccurrenceBranches? mol state fuel left right = some comparison := by
  rcases compareCursorBranchAt_branching_supported_exists mol fuel left right width
      leftSupport rightSupport with ⟨constitutional, rawEq⟩
  have gateFalse := leftNeutral.gate_false right constitutional
  have constitutionalEq : certifiedConstitutionalStage? mol fuel left right =
      some constitutional := by
    simp [certifiedConstitutionalStage?, rawEq, gateFalse]
  rcases compareOccurrenceDescriptorAtTiedRoot?_branching_exists mol state fuel .rule4a
      left right width leftSupport rightSupport with ⟨rule4a, rule4aEq⟩
  rcases compareOccurrenceRule4b?_branching_exists_of_uniform_arity mol state fuel arity
      left right width leftSupport rightSupport arityLe leftArity rightArity with
    ⟨rule4b, rule4bEq⟩
  rcases compareOccurrenceRule5?_branching_exists mol state fuel left right width
      leftSupport rightSupport with ⟨rule5, rule5Eq⟩
  cases lowercase : state.any fun fact => !fact.uppercase with
  | false =>
      cases constitutional with
      | lt => exact ⟨{ ordering := .lt }, by
          simp [compareOccurrenceBranches?, constitutionalEq]⟩
      | gt => exact ⟨{ ordering := .gt }, by
          simp [compareOccurrenceBranches?, constitutionalEq]⟩
      | eq =>
          cases rule4a with
          | lt => exact ⟨{ ordering := .lt }, by
              simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq]⟩
          | gt => exact ⟨{ ordering := .gt }, by
              simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq]⟩
          | eq =>
              cases rule4b with
              | lt => exact ⟨{ ordering := .lt }, by
                  simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq]⟩
              | gt => exact ⟨{ ordering := .gt }, by
                  simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq]⟩
              | eq => exact ⟨{ ordering := rule5.ordering, pseudo := rule5.pseudo }, by
                  simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq,
                    lowercase, rule5Eq]⟩
  | true =>
      let before := compareOccurrenceDescriptorBranchAt mol state fuel .rule4c
      have beforeTotal : ∀ childLeft childRight,
          BranchingCursorSupport mol fuel childLeft →
          BranchingCursorSupport mol fuel childRight →
          ∃ decision, before childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        exact compareOccurrenceDescriptorBranchAt_branching_exists mol state fuel .rule4c
          childLeft childRight width childLeftSupport childRightSupport
      have frontier : BranchingFrontierSupport mol fuel [(left, right)] :=
        ⟨by simpa using And.intro leftSupport rightSupport, by simpa using width⟩
      rcases compareOccurrenceRule4cWithWitness_branching_exists mol state fuel before beforeTotal
          fuel [(left, right)] (by omega) frontier with ⟨rule4c, rule4cEq⟩
      cases constitutional with
      | lt => exact ⟨{ ordering := .lt }, by
          simp [compareOccurrenceBranches?, constitutionalEq]⟩
      | gt => exact ⟨{ ordering := .gt }, by
          simp [compareOccurrenceBranches?, constitutionalEq]⟩
      | eq =>
          cases rule4a with
          | lt => exact ⟨{ ordering := .lt }, by
              simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq]⟩
          | gt => exact ⟨{ ordering := .gt }, by
              simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq]⟩
          | eq =>
              cases rule4b with
              | lt => exact ⟨{ ordering := .lt }, by
                  simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq]⟩
              | gt => exact ⟨{ ordering := .gt }, by
                  simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq]⟩
              | eq =>
                  cases rule4c with
                  | mk rule4cOrdering carrier =>
                      cases rule4cOrdering with
                      | lt => exact ⟨{ ordering := .lt, rule4cCarrier? := carrier }, by
                          simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq,
                            rule4bEq, lowercase, before, rule4cEq]⟩
                      | gt => exact ⟨{ ordering := .gt, rule4cCarrier? := carrier }, by
                          simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq,
                            rule4bEq, lowercase, before, rule4cEq]⟩
                      | eq => exact
                          ⟨{ ordering := rule5.ordering, pseudo := rule5.pseudo }, by
                            simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq,
                              rule4bEq, lowercase, before, rule4cEq, rule5Eq]⟩

end TetraStereo.OneCenter.ProductionCIPDescriptorBranchingCompleteness
