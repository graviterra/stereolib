import TetraStereo.OneCenter.CIPAuthoritativeRerootCompleteness
import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking
import TetraStereo.OneCenter.CIPAuthoritativeMancudeTotality
import TetraStereo.OneCenter.CIPAuthoritativeValenceBondingNumber

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.AuthoritativeCIPOccurrenceCompleteness

/-!
# Width-unbounded Rules-1a--5 occurrence completeness

This is the cap-free descriptor-stage counterpart of the structural Rule-6 theorem.  Descriptor
labels themselves are total; the genuine premises retained here are finite local cursor support
and exact uncapped Rule-1a observations.  The complete path inherits neither the production
automorphism-refusal gate nor the former Rule-4b reference-shape partiality.
-/

open RawMolecule
open AuthoritativeCIPRule6Completeness
open AuthoritativeCIPRerootCompleteness
open AuthoritativeCIPCursorSupport
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPValenceBondingNumber

/-- One descriptor rule terminates over an arbitrarily wide supported authoritative frontier. -/
theorem compareOccurrenceDescriptorRuleAuthoritative?_exists (mol : RawMolecule)
    (state : OccurrenceAuxState) (rankFuel : Nat)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeLeftTotal : ∀ left right,
      CursorSupport mol rankFuel left → CursorSupport mol rankFuel right →
      ∃ ordering, beforeLeft left right = some ordering)
    (beforeRightTotal : ∀ left right,
      CursorSupport mol rankFuel left → CursorSupport mol rankFuel right →
      ∃ ordering, beforeRight left right = some ordering)
    (stage : RawDescriptorRuleStage) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → FrontierSupport mol fuel pairs →
      ∃ ordering,
        compareOccurrenceDescriptorRuleAuthoritative? mol state beforeLeft beforeRight stage fuel
          pairs = some ordering
  | 0, pairs, _, support => by
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by
          simp [compareOccurrenceDescriptorRuleAuthoritative?, labels]⟩
      | gt => exact ⟨.gt, by
          simp [compareOccurrenceDescriptorRuleAuthoritative?, labels]⟩
      | eq =>
          have nextEq := nextOccurrenceDescriptorPairsAuthoritative?_zero_eq_nil mol beforeLeft
            beforeRight pairs support
          exact ⟨.eq, by
            simp [compareOccurrenceDescriptorRuleAuthoritative?, labels, nextEq]⟩
  | fuel + 1, pairs, fuelLe, support => by
      have lowerLe : fuel ≤ rankFuel := by omega
      have localLeftTotal : ∀ left right,
          CursorSupport mol fuel left → CursorSupport mol fuel right →
          ∃ ordering, beforeLeft left right = some ordering := by
        intro left right leftSupport rightSupport
        exact beforeLeftTotal left right (leftSupport.mono lowerLe) (rightSupport.mono lowerLe)
      have localRightTotal : ∀ left right,
          CursorSupport mol fuel left → CursorSupport mol fuel right →
          ∃ ordering, beforeRight left right = some ordering := by
        intro left right leftSupport rightSupport
        exact beforeRightTotal left right (leftSupport.mono lowerLe) (rightSupport.mono lowerLe)
      cases labels : compareOccurrenceDescriptorPairLabels state stage pairs with
      | lt => exact ⟨.lt, by
          simp [compareOccurrenceDescriptorRuleAuthoritative?, labels]⟩
      | gt => exact ⟨.gt, by
          simp [compareOccurrenceDescriptorRuleAuthoritative?, labels]⟩
      | eq =>
          rcases nextOccurrenceDescriptorPairsAuthoritative?_exists_of_support mol beforeLeft
              beforeRight fuel localLeftTotal localRightTotal pairs support with
            ⟨next, nextEq, nextSupport⟩
          cases next with
          | nil => exact ⟨.eq, by
              simp [compareOccurrenceDescriptorRuleAuthoritative?, labels, nextEq]⟩
          | cons pair rest =>
              rcases compareOccurrenceDescriptorRuleAuthoritative?_exists mol state rankFuel
                  beforeLeft beforeRight beforeLeftTotal beforeRightTotal stage fuel
                  (pair :: rest) (by omega) nextSupport with ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorRuleAuthoritative?, labels, nextEq, decisionEq]⟩

/-- Recursive descriptor comparison through any selected Rules-4a--5 stage is total on local
authoritative support. -/
theorem compareOccurrenceDescriptorBranchAtAuthoritative?_exists (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (labelSupported : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label) :
    ∀ fuel stage left right,
      CursorSupport mol fuel left → CursorSupport mol fuel right →
      ∃ ordering,
        compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage left right =
          some ordering
  | 0, stage, left, right, leftSupport, rightSupport => by
      rcases compareCursorBranchAtAuthoritative?_exists mol labelSupported 0 left right
          leftSupport rightSupport with ⟨constitutional, rawEq⟩
      have throughEq : mol.compareCanonicalNodeThroughAuthoritative? .rule2 left.node right.node =
          some constitutional := rawEq
      cases constitutional with
      | lt => exact ⟨.lt, by
          simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq]⟩
      | gt => exact ⟨.gt, by
          simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq]⟩
      | eq =>
          cases rule4a : compare
              (occurrenceNodePriority state .rule4a true left)
              (occurrenceNodePriority state .rule4a false right) with
          | lt => exact ⟨.lt, by
              cases stage <;>
                simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq, rule4a]⟩
          | gt => exact ⟨.gt, by
              cases stage <;>
                simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq, rule4a]⟩
          | eq =>
              cases stage with
              | rule4a => exact ⟨.eq, by
                  simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq, rule4a]⟩
              | rule4b leftReference rightReference =>
                  let decision := compare
                    (occurrenceNodePriority state (.rule4b leftReference rightReference) true left)
                    (occurrenceNodePriority state (.rule4b leftReference rightReference) false right)
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq, rule4a,
                      decision]⟩
              | rule4c =>
                  let decision := compare
                    (occurrenceNodePriority state .rule4c true left)
                    (occurrenceNodePriority state .rule4c false right)
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq, rule4a,
                      decision]⟩
              | rule5 leftReference rightReference =>
                  let decision := compare
                    (occurrenceNodePriority state (.rule5 leftReference rightReference) true left)
                    (occurrenceNodePriority state (.rule5 leftReference rightReference) false right)
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAtAuthoritative?, throughEq, rule4a,
                      decision]⟩
  | fuel + 1, stage, left, right, leftSupport, rightSupport => by
      rcases compareCursorBranchAtAuthoritative?_exists mol labelSupported (fuel + 1) left right
          leftSupport rightSupport with ⟨constitutional, rawEq⟩
      let beforeLeft :=
        compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.leftInternal
      let beforeRight :=
        compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.rightInternal
      have beforeLeftTotal : ∀ childLeft childRight,
          CursorSupport mol fuel childLeft → CursorSupport mol fuel childRight →
          ∃ decision, beforeLeft childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        exact compareOccurrenceDescriptorBranchAtAuthoritative?_exists mol state labelSupported
          fuel stage.leftInternal childLeft childRight childLeftSupport childRightSupport
      have beforeRightTotal : ∀ childLeft childRight,
          CursorSupport mol fuel childLeft → CursorSupport mol fuel childRight →
          ∃ decision, beforeRight childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        exact compareOccurrenceDescriptorBranchAtAuthoritative?_exists mol state labelSupported
          fuel stage.rightInternal childLeft childRight childLeftSupport childRightSupport
      have frontier : FrontierSupport mol (fuel + 1) [(left, right)] := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        subst pair
        exact ⟨leftSupport, rightSupport⟩
      have compareExists : ∀ selected,
          ∃ decision,
            compareOccurrenceDescriptorRuleAuthoritative? mol state beforeLeft beforeRight selected
              (fuel + 1) [(left, right)] = some decision := by
        intro selected
        exact compareOccurrenceDescriptorRuleAuthoritative?_exists mol state fuel beforeLeft
          beforeRight beforeLeftTotal beforeRightTotal selected (fuel + 1) [(left, right)]
          (by omega) frontier
      cases constitutional with
      | lt => exact ⟨.lt, by
          simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq]⟩
      | gt => exact ⟨.gt, by
          simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq]⟩
      | eq =>
          rcases compareExists .rule4a with ⟨rule4a, rule4aEq⟩
          cases rule4a with
          | lt => exact ⟨.lt, by
              simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                beforeRight, rule4aEq]⟩
          | gt => exact ⟨.gt, by
              simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                beforeRight, rule4aEq]⟩
          | eq =>
              cases stage with
              | rule4a => exact ⟨.eq, by
                  simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                    beforeRight, rule4aEq]⟩
              | rule4b leftReference rightReference =>
                  rcases compareExists (.rule4b leftReference rightReference) with
                    ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                      beforeRight, rule4aEq, decisionEq]⟩
              | rule4c =>
                  rcases compareExists .rule4c with ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                      beforeRight, rule4aEq, decisionEq]⟩
              | rule5 leftReference rightReference =>
                  rcases compareExists .rule4c with ⟨rule4c, rule4cEq⟩
                  cases rule4c with
                  | lt => exact ⟨.lt, by
                      simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                        beforeRight, rule4aEq, rule4cEq]⟩
                  | gt => exact ⟨.gt, by
                      simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                        beforeRight, rule4aEq, rule4cEq]⟩
                  | eq =>
                      rcases compareExists (.rule5 leftReference rightReference) with
                        ⟨decision, decisionEq⟩
                      exact ⟨decision, by
                        simp [compareOccurrenceDescriptorBranchAtAuthoritative?, rawEq, beforeLeft,
                          beforeRight, rule4aEq, rule4cEq, decisionEq]⟩

/-- Root-tied descriptor fallthrough is total on the same local support. -/
theorem compareOccurrenceDescriptorAtTiedRootAuthoritative?_exists (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (labelSupported : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (fuel : Nat) (stage : RawDescriptorRuleStage) (left right : CanonicalRerootCursor)
    (leftSupport : CursorSupport mol fuel left)
    (rightSupport : CursorSupport mol fuel right) :
    ∃ ordering,
      compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel stage left right =
        some ordering := by
  let beforeLeft :=
    compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.leftInternal
  let beforeRight :=
    compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel stage.rightInternal
  have beforeLeftTotal : ∀ childLeft childRight,
      CursorSupport mol fuel childLeft → CursorSupport mol fuel childRight →
      ∃ decision, beforeLeft childLeft childRight = some decision := by
    intro childLeft childRight childLeftSupport childRightSupport
    exact compareOccurrenceDescriptorBranchAtAuthoritative?_exists mol state labelSupported fuel
      stage.leftInternal childLeft childRight childLeftSupport childRightSupport
  have beforeRightTotal : ∀ childLeft childRight,
      CursorSupport mol fuel childLeft → CursorSupport mol fuel childRight →
      ∃ decision, beforeRight childLeft childRight = some decision := by
    intro childLeft childRight childLeftSupport childRightSupport
    exact compareOccurrenceDescriptorBranchAtAuthoritative?_exists mol state labelSupported fuel
      stage.rightInternal childLeft childRight childLeftSupport childRightSupport
  have frontier : FrontierSupport mol fuel [(left, right)] := by
    intro pair member
    have pairEq : pair = (left, right) := by simpa using member
    subst pair
    exact ⟨leftSupport, rightSupport⟩
  have compareExists : ∀ selected,
      ∃ decision,
        compareOccurrenceDescriptorRuleAuthoritative? mol state beforeLeft beforeRight selected fuel
          [(left, right)] = some decision := by
    intro selected
    exact compareOccurrenceDescriptorRuleAuthoritative?_exists mol state fuel beforeLeft
      beforeRight beforeLeftTotal beforeRightTotal selected fuel [(left, right)] (by omega)
      frontier
  rcases compareExists .rule4a with ⟨rule4a, rule4aEq⟩
  cases rule4a with
  | lt => exact ⟨.lt, by
      simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft, beforeRight,
        rule4aEq]⟩
  | gt => exact ⟨.gt, by
      simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft, beforeRight,
        rule4aEq]⟩
  | eq =>
      cases stage with
      | rule4a => exact ⟨.eq, by
          simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft, beforeRight,
            rule4aEq]⟩
      | rule4b leftReference rightReference =>
          rcases compareExists (.rule4b leftReference rightReference) with
            ⟨decision, decisionEq⟩
          exact ⟨decision, by
            simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft, beforeRight,
              rule4aEq, decisionEq]⟩
      | rule4c =>
          cases lowercase : state.any fun fact => !fact.uppercase with
          | false => exact ⟨.eq, by
              simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft, beforeRight,
                rule4aEq, lowercase]⟩
          | true =>
              rcases compareExists .rule4c with ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft, beforeRight,
                  rule4aEq, lowercase, decisionEq]⟩
      | rule5 leftReference rightReference =>
          cases lowercase : state.any fun fact => !fact.uppercase with
          | false =>
              rcases compareExists (.rule5 leftReference rightReference) with
                ⟨decision, decisionEq⟩
              exact ⟨decision, by
                simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft, beforeRight,
                  rule4aEq, lowercase, decisionEq]⟩
          | true =>
              rcases compareExists .rule4c with ⟨rule4c, rule4cEq⟩
              cases rule4c with
              | lt => exact ⟨.lt, by
                  simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft,
                    beforeRight, rule4aEq, lowercase, rule4cEq]⟩
              | gt => exact ⟨.gt, by
                  simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft,
                    beforeRight, rule4aEq, lowercase, rule4cEq]⟩
              | eq =>
                  rcases compareExists (.rule5 leftReference rightReference) with
                    ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceDescriptorAtTiedRootAuthoritative?, beforeLeft,
                      beforeRight, rule4aEq, lowercase, rule4cEq, decisionEq]⟩

/-- The proof-carrying Rule-4c traversal is total on an arbitrarily wide supported frontier. -/
theorem compareOccurrenceRule4cWithWitnessAuthoritative?_exists (mol : RawMolecule)
    (state : OccurrenceAuxState) (rankFuel : Nat)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (beforeTotal : ∀ left right,
      CursorSupport mol rankFuel left → CursorSupport mol rankFuel right →
      ∃ ordering, before left right = some ordering) :
    ∀ fuel pairs, fuel ≤ rankFuel + 1 → FrontierSupport mol fuel pairs →
      ∃ decision,
        compareOccurrenceRule4cWithWitnessAuthoritative? mol state before before fuel pairs =
          some decision
  | 0, pairs, _, support => by
      cases labels : compareOccurrenceRule4cPairLabelsWithWitness state pairs with
      | mk ordering carrier =>
          cases ordering with
          | lt => exact ⟨{ ordering := .lt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitnessAuthoritative?, labels]⟩
          | gt => exact ⟨{ ordering := .gt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitnessAuthoritative?, labels]⟩
          | eq =>
              have nextEq := nextOccurrenceDescriptorPairsAuthoritative?_zero_eq_nil mol before
                before pairs support
              exact ⟨{ ordering := .eq }, by
                simp [compareOccurrenceRule4cWithWitnessAuthoritative?, labels, nextEq]⟩
  | fuel + 1, pairs, fuelLe, support => by
      have lowerLe : fuel ≤ rankFuel := by omega
      have localTotal : ∀ left right,
          CursorSupport mol fuel left → CursorSupport mol fuel right →
          ∃ ordering, before left right = some ordering := by
        intro left right leftSupport rightSupport
        exact beforeTotal left right (leftSupport.mono lowerLe) (rightSupport.mono lowerLe)
      cases labels : compareOccurrenceRule4cPairLabelsWithWitness state pairs with
      | mk ordering carrier =>
          cases ordering with
          | lt => exact ⟨{ ordering := .lt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitnessAuthoritative?, labels]⟩
          | gt => exact ⟨{ ordering := .gt, carrier? := carrier }, by
              simp [compareOccurrenceRule4cWithWitnessAuthoritative?, labels]⟩
          | eq =>
              rcases nextOccurrenceDescriptorPairsAuthoritative?_exists_of_support mol before
                  before fuel localTotal localTotal pairs support with
                ⟨next, nextEq, nextSupport⟩
              cases next with
              | nil => exact ⟨{ ordering := .eq }, by
                  simp [compareOccurrenceRule4cWithWitnessAuthoritative?, labels, nextEq]⟩
              | cons pair rest =>
                  rcases compareOccurrenceRule4cWithWitnessAuthoritative?_exists mol state
                      rankFuel before beforeTotal fuel (pair :: rest) (by omega) nextSupport with
                    ⟨decision, decisionEq⟩
                  exact ⟨decision, by
                    simp [compareOccurrenceRule4cWithWitnessAuthoritative?, labels, nextEq,
                      decisionEq]⟩

/-- The Rule-4b reference search has exactly the four result shapes named by P-92.5.2.1:
no reference, one `R` reference, one `S` reference, or the tied pair `[R, S]`.  In particular,
the executable search can never manufacture an unsupported third reference. -/
theorem occurrenceRule4bReferences_shape (mol : RawMolecule) (state : OccurrenceAuxState) :
    ∀ fuel frontier,
      occurrenceRule4bReferences mol state fuel frontier = [] ∨
      occurrenceRule4bReferences mol state fuel frontier = [.R] ∨
      occurrenceRule4bReferences mol state fuel frontier = [.S] ∨
      occurrenceRule4bReferences mol state fuel frontier = [.R, .S]
  | 0, frontier => by
      simp [occurrenceRule4bReferences]
  | fuel + 1, [] => by
      simp [occurrenceRule4bReferences]
  | fuel + 1, cursor :: frontier => by
      simp only [occurrenceRule4bReferences]
      let senses := (cursor :: frontier).filterMap fun selected =>
        match selected.node.provenance, state.factAt? selected.node with
        | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
            if fact.uppercase then some fact.descriptor else none
        | _, _ => none
      let rCount := (senses.filter fun sense => sense == RS.R).length
      let sCount := (senses.filter fun sense => sense == RS.S).length
      change
        (if rCount + sCount != 0 then
            if sCount < rCount then [.R]
            else if rCount < sCount then [.S]
            else [.R, .S]
          else occurrenceRule4bReferences mol state fuel
            ((cursor :: frontier).flatMap fun selected => selected.children mol)) = [] ∨
        (if rCount + sCount != 0 then
            if sCount < rCount then [.R]
            else if rCount < sCount then [.S]
            else [.R, .S]
          else occurrenceRule4bReferences mol state fuel
            ((cursor :: frontier).flatMap fun selected => selected.children mol)) = [.R] ∨
        (if rCount + sCount != 0 then
            if sCount < rCount then [.R]
            else if rCount < sCount then [.S]
            else [.R, .S]
          else occurrenceRule4bReferences mol state fuel
            ((cursor :: frontier).flatMap fun selected => selected.children mol)) = [.S] ∨
        (if rCount + sCount != 0 then
            if sCount < rCount then [.R]
            else if rCount < sCount then [.S]
            else [.R, .S]
          else occurrenceRule4bReferences mol state fuel
            ((cursor :: frontier).flatMap fun selected => selected.children mol)) = [.R, .S]
      by_cases nonzero : rCount + sCount != 0
      · rw [if_pos nonzero]
        by_cases sBeforeR : sCount < rCount
        · rw [if_pos sBeforeR]
          exact Or.inr (Or.inl rfl)
        · rw [if_neg sBeforeR]
          by_cases rBeforeS : rCount < sCount
          · rw [if_pos rBeforeS]
            exact Or.inr (Or.inr (Or.inl rfl))
          · rw [if_neg rBeforeS]
            exact Or.inr (Or.inr (Or.inr rfl))
      · rw [if_neg nonzero]
        exact occurrenceRule4bReferences_shape mol state fuel
          ((cursor :: frontier).flatMap fun selected => selected.children mol)

/-- The Rule-4b reference search is intrinsically bounded by the two reference descriptors. -/
theorem occurrenceRule4bReferences_length_le_two (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (frontier : List CanonicalRerootCursor) :
    (occurrenceRule4bReferences mol state fuel frontier).length ≤ 2 := by
  rcases occurrenceRule4bReferences_shape mol state fuel frontier with
    empty | oneR | oneS | two
  · simp [empty]
  · simp [oneR]
  · simp [oneS]
  · simp [two]

/-- Authoritative Rule 4b is total when both roots expose the same supported reference arity. -/
theorem compareOccurrenceRule4bAuthoritative?_exists_of_uniform_arity
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (labelSupported : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (fuel arity : Nat) (left right : CanonicalRerootCursor)
    (leftSupport : CursorSupport mol fuel left)
    (rightSupport : CursorSupport mol fuel right)
    (arityLe : arity ≤ 2)
    (leftArity : (occurrenceRule4bReferences mol state fuel [left]).length = arity)
    (rightArity : (occurrenceRule4bReferences mol state fuel [right]).length = arity) :
    ∃ ordering, compareOccurrenceRule4bAuthoritative? mol state fuel left right = some ordering := by
  let leftRefs := occurrenceRule4bReferences mol state fuel [left]
  let rightRefs := occurrenceRule4bReferences mol state fuel [right]
  have leftLength : leftRefs.length = arity := leftArity
  have rightLength : rightRefs.length = arity := rightArity
  have tiedTotal : ∀ stage selectedLeft selectedRight,
      CursorSupport mol fuel selectedLeft → CursorSupport mol fuel selectedRight →
      ∃ ordering,
        compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel stage selectedLeft
          selectedRight = some ordering := by
    intro stage selectedLeft selectedRight selectedLeftSupport selectedRightSupport
    exact compareOccurrenceDescriptorAtTiedRootAuthoritative?_exists mol state labelSupported fuel
      stage selectedLeft selectedRight selectedLeftSupport selectedRightSupport
  rcases (show arity = 0 ∨ arity = 1 ∨ arity = 2 by omega) with rfl | rfl | rfl
  · have leftNil : leftRefs = [] := List.length_eq_zero_iff.mp leftLength
    have rightNil : rightRefs = [] := List.length_eq_zero_iff.mp rightLength
    exact ⟨.eq, by
      simp [compareOccurrenceRule4bAuthoritative?, leftRefs, rightRefs, leftNil, rightNil]⟩
  · rcases List.length_eq_one_iff.mp leftLength with ⟨leftReference, leftEq⟩
    rcases List.length_eq_one_iff.mp rightLength with ⟨rightReference, rightEq⟩
    rcases tiedTotal (.rule4b leftReference rightReference) left right leftSupport rightSupport with
      ⟨decision, decisionEq⟩
    exact ⟨decision, by
      simp [compareOccurrenceRule4bAuthoritative?, leftRefs, rightRefs, leftEq, rightEq,
        decisionEq]⟩
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
        rankOccurrenceRule4bReferencesAuthoritative? mol state fuel left
          [leftFirst, leftSecond] = some ranked := by
      cases leftRankDecision with
      | lt => exact ⟨[leftSecond, leftFirst], by
          simp [rankOccurrenceRule4bReferencesAuthoritative?, leftRankEq]⟩
      | eq => exact ⟨[leftFirst, leftSecond], by
          simp [rankOccurrenceRule4bReferencesAuthoritative?, leftRankEq]⟩
      | gt => exact ⟨[leftFirst, leftSecond], by
          simp [rankOccurrenceRule4bReferencesAuthoritative?, leftRankEq]⟩
    have rankedRight : ∃ ranked,
        rankOccurrenceRule4bReferencesAuthoritative? mol state fuel right
          [rightFirst, rightSecond] = some ranked := by
      cases rightRankDecision with
      | lt => exact ⟨[rightSecond, rightFirst], by
          simp [rankOccurrenceRule4bReferencesAuthoritative?, rightRankEq]⟩
      | eq => exact ⟨[rightFirst, rightSecond], by
          simp [rankOccurrenceRule4bReferencesAuthoritative?, rightRankEq]⟩
      | gt => exact ⟨[rightFirst, rightSecond], by
          simp [rankOccurrenceRule4bReferencesAuthoritative?, rightRankEq]⟩
    rcases rankedLeft with ⟨leftRanked, leftRankedEq⟩
    rcases rankedRight with ⟨rightRanked, rightRankedEq⟩
    rcases tiedTotal
        (.rule4b (leftRanked.getD 0 .R) (rightRanked.getD 0 .R)) left right
        leftSupport rightSupport with ⟨first, firstEq⟩
    change compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
      (.rule4b (leftRanked[0]?.getD .R) (rightRanked[0]?.getD .R)) left right =
        some first at firstEq
    cases first with
    | lt => exact ⟨.lt, by
        simp [compareOccurrenceRule4bAuthoritative?, leftEq, rightEq, leftRankedEq,
          rightRankedEq, firstEq]⟩
    | gt => exact ⟨.gt, by
        simp [compareOccurrenceRule4bAuthoritative?, leftEq, rightEq, leftRankedEq,
          rightRankedEq, firstEq]⟩
    | eq =>
        rcases tiedTotal
            (.rule4b (leftRanked.getD 1 .S) (rightRanked.getD 1 .S)) left right
            leftSupport rightSupport with ⟨second, secondEq⟩
        change compareOccurrenceDescriptorAtTiedRootAuthoritative? mol state fuel
          (.rule4b (leftRanked[1]?.getD .S) (rightRanked[1]?.getD .S)) left right =
            some second at secondEq
        exact ⟨second, by
          simp [compareOccurrenceRule4bAuthoritative?, leftEq, rightEq, leftRankedEq,
            rightRankedEq, firstEq, secondEq]⟩

/-- Exact Rule-4b totality boundary.  Since the search result is intrinsically one of the four
supported shapes, the comparator needs no common-cardinality premise.  Its only shape-level
obstruction is comparing absence on one side with presence on the other. -/
theorem compareOccurrenceRule4bAuthoritative?_exists_of_reference_existence_agreement
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (labelSupported : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftSupport : CursorSupport mol fuel left)
    (rightSupport : CursorSupport mol fuel right)
    (emptyIff : occurrenceRule4bReferences mol state fuel [left] = [] ↔
      occurrenceRule4bReferences mol state fuel [right] = []) :
    ∃ ordering, compareOccurrenceRule4bAuthoritative? mol state fuel left right = some ordering := by
  have uniform (arity : Nat) (arityLe : arity ≤ 2)
      (leftArity : (occurrenceRule4bReferences mol state fuel [left]).length = arity)
      (rightArity : (occurrenceRule4bReferences mol state fuel [right]).length = arity) :=
    compareOccurrenceRule4bAuthoritative?_exists_of_uniform_arity mol state labelSupported
      fuel arity left right leftSupport rightSupport arityLe leftArity rightArity
  rcases occurrenceRule4bReferences_shape mol state fuel [left] with
    leftEmpty | leftR | leftS | leftTwo
  · have rightEmpty := emptyIff.mp leftEmpty
    exact ⟨.eq, by simp [compareOccurrenceRule4bAuthoritative?, leftEmpty, rightEmpty]⟩
  · rcases occurrenceRule4bReferences_shape mol state fuel [right] with
      rightEmpty | rightR | rightS | rightTwo
    · have impossible := emptyIff.mpr rightEmpty
      simp [leftR] at impossible
    · exact uniform 1 (by omega) (by simp [leftR]) (by simp [rightR])
    · exact uniform 1 (by omega) (by simp [leftR]) (by simp [rightS])
    · exact ⟨.gt, by
        simp [compareOccurrenceRule4bAuthoritative?, leftR, rightTwo]⟩
  · rcases occurrenceRule4bReferences_shape mol state fuel [right] with
      rightEmpty | rightR | rightS | rightTwo
    · have impossible := emptyIff.mpr rightEmpty
      simp [leftS] at impossible
    · exact uniform 1 (by omega) (by simp [leftS]) (by simp [rightR])
    · exact uniform 1 (by omega) (by simp [leftS]) (by simp [rightS])
    · exact ⟨.gt, by
        simp [compareOccurrenceRule4bAuthoritative?, leftS, rightTwo]⟩
  · rcases occurrenceRule4bReferences_shape mol state fuel [right] with
      rightEmpty | rightR | rightS | rightTwo
    · have impossible := emptyIff.mpr rightEmpty
      simp [leftTwo] at impossible
    · exact ⟨.lt, by
        simp [compareOccurrenceRule4bAuthoritative?, leftTwo, rightR]⟩
    · exact ⟨.lt, by
        simp [compareOccurrenceRule4bAuthoritative?, leftTwo, rightS]⟩
    · exact uniform 2 (by omega) (by simp [leftTwo]) (by simp [rightTwo])

/-- The unrestricted Rule-4b shape extension is total on finite local support.  No compatibility
assumption remains: empty/nonempty shapes are decided directly, while the already proved supported
one/two-reference cases retain their exact descriptor comparisons. -/
theorem compareOccurrenceRule4bUnrestrictedAuthoritative?_exists
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (labelSupported : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftSupport : CursorSupport mol fuel left)
    (rightSupport : CursorSupport mol fuel right) :
    ∃ ordering,
      compareOccurrenceRule4bUnrestrictedAuthoritative? mol state fuel left right =
        some ordering := by
  by_cases leftEmpty : occurrenceRule4bReferences mol state fuel [left] = []
  · by_cases rightEmpty : occurrenceRule4bReferences mol state fuel [right] = []
    · exact ⟨.eq, by
        simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, leftEmpty, rightEmpty]⟩
    · rcases occurrenceRule4bReferences_shape mol state fuel [right] with
        rightNil | rightR | rightS | rightTwo
      · exact False.elim (rightEmpty rightNil)
      · exact ⟨.lt, by
          simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, leftEmpty, rightR]⟩
      · exact ⟨.lt, by
          simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, leftEmpty, rightS]⟩
      · exact ⟨.lt, by
          simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, leftEmpty, rightTwo]⟩
  · by_cases rightEmpty : occurrenceRule4bReferences mol state fuel [right] = []
    · rcases occurrenceRule4bReferences_shape mol state fuel [left] with
        leftNil | leftR | leftS | leftTwo
      · exact False.elim (leftEmpty leftNil)
      · exact ⟨.gt, by
          simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, leftR, rightEmpty]⟩
      · exact ⟨.gt, by
          simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, leftS, rightEmpty]⟩
      · exact ⟨.gt, by
          simp [compareOccurrenceRule4bUnrestrictedAuthoritative?, leftTwo, rightEmpty]⟩
    · have agreement : occurrenceRule4bReferences mol state fuel [left] = [] ↔
          occurrenceRule4bReferences mol state fuel [right] = [] := by
        constructor
        · intro impossible
          exact False.elim (leftEmpty impossible)
        · intro impossible
          exact False.elim (rightEmpty impossible)
      rcases
          compareOccurrenceRule4bAuthoritative?_exists_of_reference_existence_agreement mol state
            labelSupported fuel left right leftSupport rightSupport agreement with
        ⟨ordering, computed⟩
      have same : compareOccurrenceRule4bUnrestrictedAuthoritative? mol state fuel left right =
          compareOccurrenceRule4bAuthoritative? mol state fuel left right := by
        rcases occurrenceRule4bReferences_shape mol state fuel [left] with
          leftNil | leftR | leftS | leftTwo
        <;> rcases occurrenceRule4bReferences_shape mol state fuel [right] with
          rightNil | rightR | rightS | rightTwo
        <;> simp_all [compareOccurrenceRule4bUnrestrictedAuthoritative?,
          compareOccurrenceRule4bAuthoritative?]
      exact ⟨ordering, same.trans computed⟩

/-- Authoritative Rule 5 is total on finite local support. -/
theorem compareOccurrenceRule5Authoritative?_exists (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (labelSupported : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftSupport : CursorSupport mol fuel left)
    (rightSupport : CursorSupport mol fuel right) :
    ∃ decision, compareOccurrenceRule5Authoritative? mol state fuel left right = some decision := by
  rcases compareOccurrenceDescriptorAtTiedRootAuthoritative?_exists mol state labelSupported fuel
      (.rule5 .R .R) left right leftSupport rightSupport with ⟨cmpR, cmpREq⟩
  rcases compareOccurrenceDescriptorAtTiedRootAuthoritative?_exists mol state labelSupported fuel
      (.rule5 .S .S) left right leftSupport rightSupport with ⟨cmpS, cmpSEq⟩
  cases cmpR with
  | lt => exact ⟨{ ordering := .lt, pseudo := cmpS != .lt }, by
      simp [compareOccurrenceRule5Authoritative?, cmpREq, cmpSEq]⟩
  | gt => exact ⟨{ ordering := .gt, pseudo := cmpS != .gt }, by
      simp [compareOccurrenceRule5Authoritative?, cmpREq, cmpSEq]⟩
  | eq => exact ⟨{ ordering := .eq, pseudo := false }, by
      simp [compareOccurrenceRule5Authoritative?, cmpREq, cmpSEq]⟩

/-- Complete authoritative Rules-1a--5 occurrence comparison is total from local recursive
support and exact Rule-1a labels.  The old common-cardinality premise is unnecessary: one reference
has priority over two by P-92.5.2.1(c)(i), absence is the zero reference-count key class, and the
search itself can return no other shape. -/
theorem compareOccurrenceBranchesUnrestrictedAuthoritative?_exists
    (mol : RawMolecule) (state : OccurrenceAuxState)
    (labelSupported : ∀ depth cursor, CursorSupport mol depth cursor →
      ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label)
    (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftSupport : CursorSupport mol fuel left)
    (rightSupport : CursorSupport mol fuel right) :
    ∃ comparison,
      compareOccurrenceBranchesUnrestrictedAuthoritative? mol state fuel left right =
        some comparison := by
  rcases compareCursorBranchAtAuthoritative?_exists mol labelSupported fuel left right
      leftSupport rightSupport with ⟨constitutional, rawEq⟩
  rcases compareOccurrenceDescriptorAtTiedRootAuthoritative?_exists mol state labelSupported fuel
      .rule4a left right leftSupport rightSupport with ⟨rule4a, rule4aEq⟩
  rcases
      compareOccurrenceRule4bUnrestrictedAuthoritative?_exists mol state labelSupported fuel left
        right leftSupport rightSupport with
    ⟨rule4b, rule4bEq⟩
  rcases compareOccurrenceRule5Authoritative?_exists mol state labelSupported fuel left right
      leftSupport rightSupport with ⟨rule5, rule5Eq⟩
  cases lowercase : state.any fun fact => !fact.uppercase with
  | false =>
      cases constitutional with
      | lt => exact ⟨{ ordering := .lt }, by
          simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq]⟩
      | gt => exact ⟨{ ordering := .gt }, by
          simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq]⟩
      | eq =>
          cases rule4a with
          | lt => exact ⟨{ ordering := .lt }, by
              simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq]⟩
          | gt => exact ⟨{ ordering := .gt }, by
              simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq]⟩
          | eq =>
              cases rule4b with
              | lt => exact ⟨{ ordering := .lt }, by
                  simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq,
                    rule4bEq]⟩
              | gt => exact ⟨{ ordering := .gt }, by
                  simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq,
                    rule4bEq]⟩
              | eq => exact ⟨{ ordering := rule5.ordering, pseudo := rule5.pseudo }, by
                  simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq,
                    rule4bEq, lowercase, rule5Eq]⟩
  | true =>
      let before := compareOccurrenceDescriptorBranchAtAuthoritative? mol state fuel .rule4c
      have beforeTotal : ∀ childLeft childRight,
          CursorSupport mol fuel childLeft → CursorSupport mol fuel childRight →
          ∃ decision, before childLeft childRight = some decision := by
        intro childLeft childRight childLeftSupport childRightSupport
        exact compareOccurrenceDescriptorBranchAtAuthoritative?_exists mol state labelSupported
          fuel .rule4c childLeft childRight childLeftSupport childRightSupport
      have frontier : FrontierSupport mol fuel [(left, right)] := by
        intro pair member
        have pairEq : pair = (left, right) := by simpa using member
        subst pair
        exact ⟨leftSupport, rightSupport⟩
      rcases compareOccurrenceRule4cWithWitnessAuthoritative?_exists mol state fuel before
          beforeTotal fuel [(left, right)] (by omega) frontier with ⟨rule4c, rule4cEq⟩
      cases constitutional with
      | lt => exact ⟨{ ordering := .lt }, by
          simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq]⟩
      | gt => exact ⟨{ ordering := .gt }, by
          simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq]⟩
      | eq =>
          cases rule4a with
          | lt => exact ⟨{ ordering := .lt }, by
              simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq]⟩
          | gt => exact ⟨{ ordering := .gt }, by
              simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq]⟩
          | eq =>
              cases rule4b with
              | lt => exact ⟨{ ordering := .lt }, by
                  simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq,
                    rule4bEq]⟩
              | gt => exact ⟨{ ordering := .gt }, by
                  simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq, rule4aEq,
                    rule4bEq]⟩
              | eq =>
                  cases rule4c with
                  | mk rule4cOrdering carrier =>
                      cases rule4cOrdering with
                      | lt => exact ⟨{ ordering := .lt, rule4cCarrier? := carrier }, by
                          simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq,
                            rule4aEq, rule4bEq, lowercase, before, rule4cEq]⟩
                      | gt => exact ⟨{ ordering := .gt, rule4cCarrier? := carrier }, by
                          simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq,
                            rule4aEq, rule4bEq, lowercase, before, rule4cEq]⟩
                      | eq => exact
                          ⟨{ ordering := rule5.ordering, pseudo := rule5.pseudo }, by
                            simp [compareOccurrenceBranchesUnrestrictedAuthoritative?, rawEq,
                              rule4aEq, rule4bEq, lowercase, before, rule4cEq, rule5Eq]⟩

/-- Local chemical hierarchy facts sufficient for every uncapped Rules-1--6 comparison through a
selected maximum depth.  There is deliberately no frontier cardinality field, gate premise, or
Rule-4b arity/compatibility premise. -/
structure DescriptorRule6HierarchySupport (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : Nat) : Prop where
  mancude_rule1a_supported : MancudeRule1aSupported mol

/-- Construct the remaining unary Rule-1a hierarchy fact from the independent finite maximum
Kekulé-matching condition. -/
def DescriptorRule6HierarchySupport.ofLocalizedMancudeKekuleAdmissible
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (kekule : LocalizedMancudeKekuleAdmissible mol) :
    DescriptorRule6HierarchySupport mol state fuel where
  mancude_rule1a_supported :=
    mancudeRule1aSupported_of_localizedKekuleAdmissible mol wellFormed unique kekule

namespace DescriptorRule6HierarchySupport

/-- The hierarchy discharges the ordinary-stage premise required by uncapped Rule 6. -/
theorem ordinary_comparison_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel depth : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (left right : CanonicalRerootCursor)
    (leftSupport : CursorSupport mol depth left)
    (rightSupport : CursorSupport mol depth right) :
    ∃ comparison,
      compareOccurrenceBranchesUnrestrictedAuthoritative? mol state depth left right =
        some comparison := by
  have labelSupported : ∀ selectedDepth cursor,
      CursorSupport mol selectedDepth cursor →
        ∃ label, mol.canonicalRule1aLabelAuthoritative? cursor.node = some label := by
    intro selectedDepth cursor _support
    exact canonicalRule1aLabelAuthoritative?_exists mol hierarchy.mancude_rule1a_supported
      cursor.node
  exact compareOccurrenceBranchesUnrestrictedAuthoritative?_exists mol state
    labelSupported
    depth left right
    leftSupport rightSupport

/-- The complete authoritative Rules-1--6 comparison is total throughout the hierarchy.  This is
the cap-free structural endpoint: only local recursive support and unary chemical facts remain. -/
theorem promoted_comparison_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (reference : Nat) : ∀ depth, depth ≤ fuel → ∀ left right,
      CursorSupport mol depth left → CursorSupport mol depth right →
      ∃ decision,
        compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference depth
          left right = some decision := by
  have ordinaryTotal : ∀ depth, depth ≤ fuel → ∀ left right,
      CursorSupport mol depth left → CursorSupport mol depth right →
      ∃ comparison,
        compareOccurrenceBranchesUnrestrictedAuthoritative? mol state depth left right =
          some comparison := by
    intro depth depthLe left right leftSupport rightSupport
    exact hierarchy.ordinary_comparison_exists left right leftSupport rightSupport
  exact
    TetraStereo.OneCenter.AuthoritativeCIPRule6Completeness.compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_exists
      mol state fuel ordinaryTotal reference

/-- Molecule-level form of complete Rules-1a--6 totality.  A well-founded reroot ranking replaces
both explicit recursive `CursorSupport` arguments; callers need only establish that the selected
physical roots belong to the certified molecular occurrence domain and fit within the chosen
depth. -/
theorem promoted_comparison_exists_of_ranking
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel depth : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (ranking : CursorTerminationRanking mol) (reference : Nat)
    (depthLe : depth ≤ fuel) (left right : CanonicalRerootCursor)
    (leftEligible : ranking.eligible left) (rightEligible : ranking.eligible right)
    (leftCovered : ranking.height left ≤ depth)
    (rightCovered : ranking.height right ≤ depth) :
    ∃ decision,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference depth
        left right = some decision := by
  exact hierarchy.promoted_comparison_exists reference depth depthLe left right
    (ranking.cursorSupport_of_height_le depth left leftEligible leftCovered)
    (ranking.cursorSupport_of_height_le depth right rightEligible rightCovered)

/-- Molecule-level Rules-1a--6 totality on the canonical center tree.  Well-formed finite graph
structure and the local P-92 bonding-number-six predicate construct recursive support internally;
the theorem has no caller-supplied cursor ranking or recursive support hypothesis. -/
theorem promoted_comparison_exists_of_canonical_center
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel center : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol center)
    (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) (reference : Nat)
    (left right : CanonicalRerootCursor)
    (leftEligible : CanonicalCenterRerootCursor mol center left)
    (rightEligible : CanonicalCenterRerootCursor mol center right) :
    ∃ decision,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
        (2 * mol.atomCount + 1) left right = some decision := by
  exact hierarchy.promoted_comparison_exists reference (2 * mol.atomCount + 1) depthCovered
    left right
    (canonicalCenterCursorSupport centerBound wellFormed bonding leftEligible)
    (canonicalCenterCursorSupport centerBound wellFormed bonding rightEligible)

/-- Every directed pair of actual ligand cursors around a generated canonical occurrence has a
complete uncapped Rules-1a--6 result at the uniform molecule-size depth. -/
theorem promoted_occurrence_ligand_comparison_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel center : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (bonding : CanonicalCenterBondingNumberSix mol center)
    (depthCovered : 2 * mol.atomCount + 1 ≤ fuel) (reference : Nat)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol occurrence)
    (rightMember : right ∈ occurrenceLigandCursors mol occurrence) :
    ∃ decision,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
        (2 * mol.atomCount + 1) left right = some decision := by
  exact hierarchy.promoted_comparison_exists_of_canonical_center centerBound wellFormed bonding
    depthCovered reference left right
    (occurrenceLigandCursor_eligible occurrenceGenerated leftMember)
    (occurrenceLigandCursor_eligible occurrenceGenerated rightMember)

/-- Complete chemical/structural totality endpoint for the uncapped Rules-1a--6 comparator.

Every directed pair of actual molecule-derived ligands succeeds from:
* well-formed unique finite bond records;
* the parser-independent valence-table certificate;
* the independent maximum-Kekulé-matching condition for localized mancude components; and
* the derived P-92 bonding-number-six condition on the canonical center tree.

No recursive support, cursor ranking, successful comparison, Rule-4b compatibility, automorphism
gate, bonding-number proof, frontier bound, or operational fuel certificate is assumed. -/
theorem promoted_occurrence_ligand_comparison_exists_of_chemical_applicability
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique)
    (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (reference : Nat)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol occurrence)
    (rightMember : right ∈ occurrenceLigandCursors mol occurrence) :
    ∃ decision,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
        (2 * mol.atomCount + 1) left right = some decision := by
  let hierarchy : DescriptorRule6HierarchySupport mol state (2 * mol.atomCount + 1) :=
    .ofLocalizedMancudeKekuleAdmissible mol state (2 * mol.atomCount + 1)
      wellFormed unique kekule
  have bonding : CanonicalCenterBondingNumberSix mol center :=
    canonicalCenterBondingNumberSix_of_valence mol center centerBound wellFormed unique valence
  exact hierarchy.promoted_occurrence_ligand_comparison_exists centerBound wellFormed bonding
    (by rfl) reference occurrenceGenerated leftMember rightMember

/-- Certified chemistry intake discharges structural, uniqueness, valence, bonding-number, and
termination obligations.  The only additional Rule-1a premise is the explicit localized Kekulé
condition, which is intentionally not hidden inside structural certification. -/
theorem promoted_occurrence_ligand_comparison_exists_of_certified_normalization
    {state : OccurrenceAuxState} (certified : CertifiedChemistryNormalizationResult)
    {center : Nat} (centerBound : center < certified.result.parsed.atomCount)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed)
    (reference : Nat) {occurrence : CanonicalBranchNode}
    (occurrenceGenerated :
      CanonicalCenterTreeNode certified.result.parsed center occurrence)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors certified.result.parsed occurrence)
    (rightMember : right ∈ occurrenceLigandCursors certified.result.parsed occurrence) :
    ∃ decision,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          certified.result.parsed state reference
          (2 * certified.result.parsed.atomCount + 1) left right = some decision := by
  exact promoted_occurrence_ligand_comparison_exists_of_chemical_applicability centerBound
    certified.admissible.1 certified.admissible.2 certified.valenceOK kekule reference
    occurrenceGenerated leftMember rightMember

/-- The chemically scoped two-success endpoint theorem for complete uncapped Rules 1a--6.

The two successful premise comparisons and their compatible ordering composition determine the
endpoint result.  Endpoint *existence* is proved from molecular applicability above, so it is not
smuggled in as a third-success premise. -/
theorem promoted_occurrence_ligand_endpoint_of_two_success_of_chemical_applicability
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique)
    (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (reference : Nat)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    {left middle right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol occurrence)
    (_middleMember : middle ∈ occurrenceLigandCursors mol occurrence)
    (rightMember : right ∈ occurrenceLigandCursors mol occurrence)
    {leftMiddle middleRight : Rule6TrackedDecision} {composed : Ordering}
    (leftMiddleEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
        (2 * mol.atomCount + 1) left middle = some leftMiddle)
    (middleRightEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
        (2 * mol.atomCount + 1) middle right = some middleRight)
    (composition :
      AuthoritativeCIPOccurrenceDescriptorComparatorLaws.composeSuccessfulOrdering?
        leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference
          (2 * mol.atomCount + 1) left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases promoted_occurrence_ligand_comparison_exists_of_chemical_applicability centerBound
      wellFormed unique valence kekule reference occurrenceGenerated leftMember rightMember with
    ⟨leftRight, leftRightEq⟩
  refine ⟨leftRight, leftRightEq, ?_⟩
  exact
    AuthoritativeCIPRule6PromotedComparatorLaws.compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_compose_of_three_success
      mol state reference (2 * mol.atomCount + 1) leftMiddleEq middleRightEq leftRightEq composition

/-- Certified-input form of the chemical two-success theorem.  Its endpoint success remains a
derived conclusion; the certified record supplies all non-Rule-1a molecule obligations. -/
theorem promoted_occurrence_ligand_endpoint_of_two_success_of_certified_normalization
    {state : OccurrenceAuxState} (certified : CertifiedChemistryNormalizationResult)
    {center : Nat} (centerBound : center < certified.result.parsed.atomCount)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed)
    (reference : Nat) {occurrence : CanonicalBranchNode}
    (occurrenceGenerated :
      CanonicalCenterTreeNode certified.result.parsed center occurrence)
    {left middle right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors certified.result.parsed occurrence)
    (middleMember : middle ∈ occurrenceLigandCursors certified.result.parsed occurrence)
    (rightMember : right ∈ occurrenceLigandCursors certified.result.parsed occurrence)
    {leftMiddle middleRight : Rule6TrackedDecision} {composed : Ordering}
    (leftMiddleEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          certified.result.parsed state reference
          (2 * certified.result.parsed.atomCount + 1) left middle = some leftMiddle)
    (middleRightEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          certified.result.parsed state reference
          (2 * certified.result.parsed.atomCount + 1) middle right = some middleRight)
    (composition :
      AuthoritativeCIPOccurrenceDescriptorComparatorLaws.composeSuccessfulOrdering?
        leftMiddle.ordering middleRight.ordering = some composed) :
    ∃ leftRight,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          certified.result.parsed state reference
          (2 * certified.result.parsed.atomCount + 1) left right = some leftRight ∧
        leftRight.ordering = composed := by
  exact promoted_occurrence_ligand_endpoint_of_two_success_of_chemical_applicability centerBound
    certified.admissible.1 certified.admissible.2 certified.valenceOK kekule reference
    occurrenceGenerated leftMember middleMember rightMember leftMiddleEq middleRightEq composition

end DescriptorRule6HierarchySupport

end TetraStereo.OneCenter.AuthoritativeCIPOccurrenceCompleteness
