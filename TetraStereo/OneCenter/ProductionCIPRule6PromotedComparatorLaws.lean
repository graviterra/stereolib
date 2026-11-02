import TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
import TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRule6PromotedComparatorLaws

/-!
# Unary-key law for the promoted Rule-6 sphere traversal

The executable Rule-6 traversal compares one Boolean promotion label at every synchronized
occurrence, recursively sorting child frontiers with its supplied callback.  This module compiles
the same bounded traversal into one dense unary key per cursor.  Every successful executable
comparison is proved equal to comparison of those keys.  Since list lexicographic comparison is
lawful, successful Rule-6 sphere decisions therefore cannot form a non-transitive cycle.

The factor theorem is partial only in the honest sense: it does not turn a failed optional
traversal into a result.  Structural Rule-6 frames already supply that separate totality fact.
-/

open RawMolecule
open ProductionCIPOccurrenceDescriptorComparatorLaws
open ProductionCIPRule6BranchingCompleteness

/-- Unary label selected by Rule 6 at one occurrence. -/
def occurrenceRule6NodePriority (reference : Nat) (cursor : CanonicalRerootCursor) : Nat :=
  if cursor.node.atom == reference then 1 else 0

/-- Production's first-difference label scan is list-lexicographic comparison of unary labels. -/
theorem compareOccurrenceRule6PairLabels_eq_compareLex (reference : Nat)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) :
    compareOccurrenceRule6PairLabels reference pairs =
      List.compareLex compare
        (pairs.map fun pair => occurrenceRule6NodePriority reference pair.1)
        (pairs.map fun pair => occurrenceRule6NodePriority reference pair.2) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs inductionHypothesis =>
      simp only [compareOccurrenceRule6PairLabels, List.map_cons, List.compareLex_cons_cons]
      change (match compare
          (occurrenceRule6NodePriority reference pair.1)
          (occurrenceRule6NodePriority reference pair.2) with
        | .eq => compareOccurrenceRule6PairLabels reference pairs
        | decision => decision) =
          (match compare
            (occurrenceRule6NodePriority reference pair.1)
            (occurrenceRule6NodePriority reference pair.2) with
          | .eq => List.compareLex compare
              (pairs.map fun pair => occurrenceRule6NodePriority reference pair.1)
              (pairs.map fun pair => occurrenceRule6NodePriority reference pair.2)
          | decision => decision)
      cases headEq : compare (occurrenceRule6NodePriority reference pair.1)
          (occurrenceRule6NodePriority reference pair.2) <;>
        simp [inductionHypothesis]

/-- Dense unary Rule-6 key: breadth-first promotion labels after deterministic child ranking. -/
def DenseOccurrenceRule6Key := List Nat

def buildDenseOccurrenceRule6Key (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference fuel : Nat) (cursor : CanonicalRerootCursor) : DenseOccurrenceRule6Key :=
  (denseDescriptorFrontiers mol before fuel [cursor]).flatten.map
    (occurrenceRule6NodePriority reference)

def compareDenseOccurrenceRule6Keys :
    DenseOccurrenceRule6Key → DenseOccurrenceRule6Key → Ordering :=
  List.compareLex compare

theorem compareDenseOccurrenceRule6Keys_transCmp :
    Std.TransCmp compareDenseOccurrenceRule6Keys := by
  unfold compareDenseOccurrenceRule6Keys
  change Std.TransCmp (List.compareLex (compare : Nat → Nat → Ordering))
  infer_instance

abbrev DenseRule6Pair := CanonicalRerootCursor × CanonicalRerootCursor

def compareDenseRule6PairLabels (reference : Nat) (pairs : List DenseRule6Pair) : Ordering :=
  List.compareLex compare
    (pairs.map fun pair => occurrenceRule6NodePriority reference pair.1)
    (pairs.map fun pair => occurrenceRule6NodePriority reference pair.2)

/-- Totalized dense counterpart of `compareOccurrenceRule6`. -/
def compareDenseOccurrenceRule6 (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) : Nat → List DenseRule6Pair → Ordering
  | 0, pairs => compareDenseRule6PairLabels reference pairs
  | depth + 1, pairs =>
      match compareDenseRule6PairLabels reference pairs with
      | .eq => compareDenseOccurrenceRule6 mol beforeLeft beforeRight reference depth
          (denseNextDescriptorPairs mol beforeLeft beforeRight pairs)
      | decision => decision

/-- The dense recursive comparison is exactly comparison of flattened dense frontier labels. -/
theorem compareDenseOccurrenceRule6_eq_frontiers (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) : ∀ depth pairs,
    compareDenseOccurrenceRule6 mol beforeLeft beforeRight reference depth pairs =
      List.compareLex compare
        ((denseDescriptorFrontiers mol beforeLeft depth (pairs.map Prod.fst)).flatten.map
          (occurrenceRule6NodePriority reference))
        ((denseDescriptorFrontiers mol beforeRight depth (pairs.map Prod.snd)).flatten.map
          (occurrenceRule6NodePriority reference))
  | 0, pairs => by
      simp [compareDenseOccurrenceRule6, compareDenseRule6PairLabels,
        denseDescriptorFrontiers, Function.comp_def]
  | depth + 1, pairs => by
      have appendRule := compareLex_append_of_length_eq (compare : Nat → Nat → Ordering)
        ((pairs.map Prod.fst).map (occurrenceRule6NodePriority reference))
        ((pairs.map Prod.snd).map (occurrenceRule6NodePriority reference))
        ((denseDescriptorFrontiers mol beforeLeft depth
          (denseDescriptorNext mol beforeLeft (pairs.map Prod.fst))).flatten.map
            (occurrenceRule6NodePriority reference))
        ((denseDescriptorFrontiers mol beforeRight depth
          (denseDescriptorNext mol beforeRight (pairs.map Prod.snd))).flatten.map
            (occurrenceRule6NodePriority reference)) (by simp)
      have tail := compareDenseOccurrenceRule6_eq_frontiers mol beforeLeft beforeRight reference
        depth (denseNextDescriptorPairs mol beforeLeft beforeRight pairs)
      rw [denseNextDescriptorPairs_map_fst, denseNextDescriptorPairs_map_snd] at tail
      simp only [compareDenseOccurrenceRule6, denseDescriptorFrontiers, List.flatten_cons,
        List.map_append]
      rw [appendRule, tail]
      unfold compareDenseRule6PairLabels
      cases current : List.compareLex compare
          (List.map (fun pair => occurrenceRule6NodePriority reference pair.1) pairs)
          (List.map (fun pair => occurrenceRule6NodePriority reference pair.2) pairs) <;>
        simp [current, Function.comp_def]

/-- A terminal pair omitted by production is silent for the Rule-6 label comparison. -/
def Rule6PairSilent (mol : RawMolecule) (reference : Nat) (pair : DenseRule6Pair) : Prop :=
  cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true ∧
    compare (occurrenceRule6NodePriority reference pair.1)
      (occurrenceRule6NodePriority reference pair.2) = .eq

/-- The active production frontier is obtained from the dense frontier by erasing only silent
terminal pairs. -/
inductive ErasesSilentRule6Pairs (mol : RawMolecule) (reference : Nat) :
    List DenseRule6Pair → List DenseRule6Pair → Prop
  | nil : ErasesSilentRule6Pairs mol reference [] []
  | keep (pair : DenseRule6Pair) {active dense : List DenseRule6Pair}
      (tail : ErasesSilentRule6Pairs mol reference active dense) :
      ErasesSilentRule6Pairs mol reference (pair :: active) (pair :: dense)
  | erase (pair : DenseRule6Pair) {active dense : List DenseRule6Pair}
      (silent : Rule6PairSilent mol reference pair)
      (tail : ErasesSilentRule6Pairs mol reference active dense) :
      ErasesSilentRule6Pairs mol reference active (pair :: dense)

theorem ErasesSilentRule6Pairs.labels_eq
    {mol : RawMolecule} {reference : Nat} {active dense : List DenseRule6Pair}
    (related : ErasesSilentRule6Pairs mol reference active dense) :
    compareDenseRule6PairLabels reference active =
      compareDenseRule6PairLabels reference dense := by
  induction related with
  | nil => rfl
  | keep pair tail inductionHypothesis =>
      unfold compareDenseRule6PairLabels at inductionHypothesis ⊢
      simp only [List.map_cons, List.compareLex]
      cases compare (occurrenceRule6NodePriority reference pair.1)
          (occurrenceRule6NodePriority reference pair.2) <;> simp [inductionHypothesis]
  | erase pair silent tail inductionHypothesis =>
      unfold compareDenseRule6PairLabels at inductionHypothesis ⊢
      rcases silent with ⟨_, _, tied⟩
      simp [List.compareLex, tied, inductionHypothesis]

theorem ErasesSilentRule6Pairs.erase_all
    {mol : RawMolecule} {reference : Nat}
    (silentPairs : List DenseRule6Pair) {active dense : List DenseRule6Pair}
    (allSilent : ∀ pair, pair ∈ silentPairs → Rule6PairSilent mol reference pair)
    (tail : ErasesSilentRule6Pairs mol reference active dense) :
    ErasesSilentRule6Pairs mol reference active (silentPairs ++ dense) := by
  induction silentPairs with
  | nil => simpa using tail
  | cons pair pairs inductionHypothesis =>
      exact .erase pair (allSilent pair (by simp))
        (inductionHypothesis
          (fun candidate member => allSilent candidate (by simp [member])))

theorem ErasesSilentRule6Pairs.keep_all
    {mol : RawMolecule} {reference : Nat}
    (initial : List DenseRule6Pair) {active dense : List DenseRule6Pair}
    (tail : ErasesSilentRule6Pairs mol reference active dense) :
    ErasesSilentRule6Pairs mol reference (initial ++ active) (initial ++ dense) := by
  induction initial with
  | nil => simpa using tail
  | cons pair pairs inductionHypothesis => exact .keep pair inductionHypothesis

theorem ErasesSilentRule6Pairs.refl
    {mol : RawMolecule} {reference : Nat} : ∀ pairs,
    ErasesSilentRule6Pairs mol reference pairs pairs
  | [] => .nil
  | pair :: pairs => .keep pair (ErasesSilentRule6Pairs.refl pairs)

/-- Dense phantom children of a silent terminal pair remain silent. -/
theorem dense_silent_rule6_children_silent (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) (pair : DenseRule6Pair)
    (silent : Rule6PairSilent mol reference pair) :
    ∀ child, child ∈ denseNextDescriptorPairs mol beforeLeft beforeRight [pair] →
      Rule6PairSilent mol reference child := by
  rcases silent with ⟨leftTerminal, rightTerminal, tied⟩
  have leftChildren := denseDescriptorChildren_eq_replicate_of_terminal
    mol beforeLeft pair.1 leftTerminal
  have rightChildren := denseDescriptorChildren_eq_replicate_of_terminal
    mol beforeRight pair.2 rightTerminal
  intro child member
  simp only [denseNextDescriptorPairs, List.flatMap_singleton,
    leftChildren, rightChildren] at member
  simp at member
  rcases member with ⟨_, rfl⟩
  simp [Rule6PairSilent, denseDescriptorPhantom, RawMolecule.canonicalPhantom,
    cursorTerminal, CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf,
    occurrenceRule6NodePriority] at tied ⊢

theorem compareOccurrenceRule6PairLabels_eq_implies_all_tied
    (reference : Nat) : ∀ pairs,
    compareOccurrenceRule6PairLabels reference pairs = .eq →
      ∀ pair, pair ∈ pairs →
        compare (occurrenceRule6NodePriority reference pair.1)
          (occurrenceRule6NodePriority reference pair.2) = .eq
  | [], _, pair, member => by simp at member
  | head :: tail, computed, pair, member => by
      simp only [compareOccurrenceRule6PairLabels] at computed
      change (match compare
          (occurrenceRule6NodePriority reference head.1)
          (occurrenceRule6NodePriority reference head.2) with
        | .eq => compareOccurrenceRule6PairLabels reference tail
        | decision => decision) = .eq at computed
      cases headEq : compare (occurrenceRule6NodePriority reference head.1)
          (occurrenceRule6NodePriority reference head.2) with
      | lt => simp [headEq] at computed
      | gt => simp [headEq] at computed
      | eq =>
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact headEq
          · exact compareOccurrenceRule6PairLabels_eq_implies_all_tied reference tail
              (by simpa [headEq] using computed) pair tailMember

/-- One successful production frontier expansion preserves the active/dense erasure relation. -/
theorem nextRule6Pairs_dense_related (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) {active dense next : List DenseRule6Pair}
    (related : ErasesSilentRule6Pairs mol reference active dense)
    (allTied : ∀ pair, pair ∈ active →
      compare (occurrenceRule6NodePriority reference pair.1)
        (occurrenceRule6NodePriority reference pair.2) = .eq)
    (computed : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight active = some next) :
    ErasesSilentRule6Pairs mol reference next
      (denseNextDescriptorPairs mol beforeLeft beforeRight dense) := by
  induction related generalizing next with
  | nil =>
      simp [nextOccurrenceDescriptorPairs?] at computed
      subst next
      exact .nil
  | erase pair silent tail inductionHypothesis =>
      have tailRelated := inductionHypothesis allTied computed
      simpa [denseNextDescriptorPairs] using ErasesSilentRule6Pairs.erase_all
        (denseNextDescriptorPairs mol beforeLeft beforeRight [pair])
        (dense_silent_rule6_children_silent mol beforeLeft beforeRight reference pair silent)
        tailRelated
  | keep pair relatedTail inductionHypothesis =>
      rename_i activeTail denseTail
      have pairTied := allTied pair (by simp)
      have tailTied : ∀ candidate, candidate ∈ activeTail →
          compare (occurrenceRule6NodePriority reference candidate.1)
            (occurrenceRule6NodePriority reference candidate.2) = .eq := by
        intro candidate member
        exact allTied candidate (by simp [member])
      simp only [nextOccurrenceDescriptorPairs?] at computed
      cases restEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight activeTail with
      | none => simp [restEq] at computed
      | some rest =>
          have restRelated := inductionHypothesis tailTied restEq
          cases leftTerminal : cursorTerminal mol pair.1 <;>
            cases rightTerminal : cursorTerminal mol pair.2
          · cases leftEq : rankedCursorChildren? mol beforeLeft pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildren? mol beforeRight pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseDescriptorChildren_eq_of_success mol beforeLeft
                      pair.1 left leftEq
                    have denseRight := denseDescriptorChildren_eq_of_success mol beforeRight
                      pair.2 right rightEq
                    simp only [denseNextDescriptorPairs, List.flatMap_cons,
                      denseLeft, denseRight]
                    exact ErasesSilentRule6Pairs.keep_all (left.zip right) restRelated
          · cases leftEq : rankedCursorChildren? mol beforeLeft pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildren? mol beforeRight pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseDescriptorChildren_eq_of_success mol beforeLeft
                      pair.1 left leftEq
                    have denseRight := denseDescriptorChildren_eq_of_success mol beforeRight
                      pair.2 right rightEq
                    simp only [denseNextDescriptorPairs, List.flatMap_cons,
                      denseLeft, denseRight]
                    exact ErasesSilentRule6Pairs.keep_all (left.zip right) restRelated
          · cases leftEq : rankedCursorChildren? mol beforeLeft pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildren? mol beforeRight pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseDescriptorChildren_eq_of_success mol beforeLeft
                      pair.1 left leftEq
                    have denseRight := denseDescriptorChildren_eq_of_success mol beforeRight
                      pair.2 right rightEq
                    simp only [denseNextDescriptorPairs, List.flatMap_cons,
                      denseLeft, denseRight]
                    exact ErasesSilentRule6Pairs.keep_all (left.zip right) restRelated
          · simp [restEq, leftTerminal, rightTerminal] at computed
            subst next
            have silentPair : Rule6PairSilent mol reference pair :=
              ⟨leftTerminal, rightTerminal, pairTied⟩
            simpa [denseNextDescriptorPairs] using ErasesSilentRule6Pairs.erase_all
              (denseNextDescriptorPairs mol beforeLeft beforeRight [pair])
              (dense_silent_rule6_children_silent mol beforeLeft beforeRight reference pair
                silentPair)
              restRelated

theorem ErasesSilentRule6Pairs.empty_dense_rule_eq (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) : ∀ depth {dense},
    ErasesSilentRule6Pairs mol reference [] dense →
      compareDenseOccurrenceRule6 mol beforeLeft beforeRight reference depth dense = .eq
  | 0, dense, related => by
      have labels := related.labels_eq
      exact labels.symm.trans (by rfl)
  | depth + 1, dense, related => by
      have labels := related.labels_eq
      have current : compareDenseRule6PairLabels reference dense = .eq :=
        labels.symm.trans (by rfl)
      have nextRelated : ErasesSilentRule6Pairs mol reference []
          (denseNextDescriptorPairs mol beforeLeft beforeRight dense) :=
        nextRule6Pairs_dense_related mol beforeLeft beforeRight reference related
          (by intro pair member; simp at member) (by rfl)
      simp only [compareDenseOccurrenceRule6, current]
      exact ErasesSilentRule6Pairs.empty_dense_rule_eq mol beforeLeft beforeRight reference
        depth nextRelated

/-- Main dense factor theorem for every successful promoted sphere traversal. -/
theorem compareOccurrenceRule6_success_factors (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) : ∀ fuel active dense decision,
    ErasesSilentRule6Pairs mol reference active dense →
    compareOccurrenceRule6 mol beforeLeft reference fuel active = some decision →
    beforeLeft = beforeRight →
    compareDenseOccurrenceRule6 mol beforeLeft beforeRight reference fuel dense = decision
  | 0, active, dense, decision, related, computed, beforeEq => by
      subst beforeRight
      simp only [compareOccurrenceRule6] at computed
      have labelsEq := related.labels_eq
      cases current : compareOccurrenceRule6PairLabels reference active with
      | lt =>
          simp [current] at computed
          have decisionEq : decision = .lt := computed.2.symm
          subst decision
          have activeCurrent : compareDenseRule6PairLabels reference active = .lt := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          exact labelsEq.symm.trans activeCurrent
      | gt =>
          simp [current] at computed
          have decisionEq : decision = .gt := computed.2.symm
          subst decision
          have activeCurrent : compareDenseRule6PairLabels reference active = .gt := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          exact labelsEq.symm.trans activeCurrent
      | eq =>
          cases nextEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeLeft active with
          | none => simp [current, nextEq] at computed
          | some next =>
              cases next with
              | nil =>
                  simp [current, nextEq] at computed
                  have decisionEq : decision = .eq := computed.2.symm
                  subst decision
                  have activeCurrent : compareDenseRule6PairLabels reference active = .eq := by
                    rw [compareDenseRule6PairLabels,
                      ← compareOccurrenceRule6PairLabels_eq_compareLex]
                    exact current
                  exact labelsEq.symm.trans activeCurrent
              | cons nextHead nextTail => simp [current, nextEq] at computed
  | fuel + 1, active, dense, decision, related, computed, beforeEq => by
      subst beforeRight
      simp only [compareOccurrenceRule6] at computed
      have labelsEq := related.labels_eq
      cases current : compareOccurrenceRule6PairLabels reference active with
      | lt =>
          simp [current] at computed
          have decisionEq : decision = .lt := computed.2.symm
          subst decision
          have activeCurrent : compareDenseRule6PairLabels reference active = .lt := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          have denseCurrent := labelsEq.symm.trans activeCurrent
          simp [compareDenseOccurrenceRule6, denseCurrent]
      | gt =>
          simp [current] at computed
          have decisionEq : decision = .gt := computed.2.symm
          subst decision
          have activeCurrent : compareDenseRule6PairLabels reference active = .gt := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          have denseCurrent := labelsEq.symm.trans activeCurrent
          simp [compareDenseOccurrenceRule6, denseCurrent]
      | eq =>
          have activeCurrent : compareDenseRule6PairLabels reference active = .eq := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          have denseCurrent := labelsEq.symm.trans activeCurrent
          cases nextEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeLeft active with
          | none => simp [current, nextEq] at computed
          | some next =>
              cases next with
              | nil =>
                  simp [current, nextEq] at computed
                  have decisionEq : decision = .eq := computed.2.symm
                  subst decision
                  have allTied := compareOccurrenceRule6PairLabels_eq_implies_all_tied
                    reference active current
                  have nextRelated := nextRule6Pairs_dense_related mol beforeLeft beforeLeft
                    reference related allTied nextEq
                  have tailEq := ErasesSilentRule6Pairs.empty_dense_rule_eq mol beforeLeft
                    beforeLeft reference fuel nextRelated
                  simp [compareDenseOccurrenceRule6, denseCurrent, tailEq]
              | cons nextHead nextTail =>
                  simp [current, nextEq] at computed
                  have recursiveEq :
                      compareOccurrenceRule6 mol beforeLeft reference fuel
                          (nextHead :: nextTail) = some decision := by
                    exact computed.2
                  have allTied := compareOccurrenceRule6PairLabels_eq_implies_all_tied
                    reference active current
                  have nextRelated := nextRule6Pairs_dense_related mol beforeLeft beforeLeft
                    reference related allTied nextEq
                  have recursive := compareOccurrenceRule6_success_factors mol beforeLeft
                    beforeLeft reference fuel (nextHead :: nextTail)
                    (denseNextDescriptorPairs mol beforeLeft beforeLeft dense) decision
                    nextRelated recursiveEq rfl
                  simp [compareDenseOccurrenceRule6, denseCurrent, recursive]

/-- Singleton production comparison factors through two opponent-independent dense keys. -/
theorem compareOccurrenceRule6_singleton_success_factors (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference fuel : Nat) (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : compareOccurrenceRule6 mol before reference fuel [(left, right)] =
      some decision) :
    compareDenseOccurrenceRule6Keys
        (buildDenseOccurrenceRule6Key mol before reference fuel left)
        (buildDenseOccurrenceRule6Key mol before reference fuel right) = decision := by
  have factored := compareOccurrenceRule6_success_factors mol before before reference fuel
    [(left, right)] [(left, right)] decision
    (ErasesSilentRule6Pairs.refl [(left, right)]) computed rfl
  rw [compareDenseOccurrenceRule6_eq_frontiers] at factored
  exact factored

/-! ## Complete Rules 1--6 key -/

/-- At positive depth, production ranks Rule-6 children with the complete promoted comparison at
the preceding depth.  Depth zero never consults this callback. -/
def promotedRule6Before (mol : RawMolecule) (state : OccurrenceAuxState) (reference : Nat) :
    Nat → CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering
  | 0 => fun _ _ => none
  | depth + 1 => fun left right =>
      (compareOccurrenceBranchesThroughRule6At? mol state reference depth left right).map
        Rule6TrackedDecision.ordering

/-- One opponent-independent key for the complete Rules 1--6 branch comparison. -/
structure PromotedOccurrenceBranchKey where
  ordinary : FailClosedOccurrenceBranchProjectedKey
  rule6 : DenseOccurrenceRule6Key

def buildPromotedOccurrenceBranchKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference fuel : Nat) (cursor : CanonicalRerootCursor) : PromotedOccurrenceBranchKey :=
  { ordinary := buildFailClosedOccurrenceBranchProjectedKey mol state fuel cursor
    rule6 := buildDenseOccurrenceRule6Key mol (promotedRule6Before mol state reference fuel)
      reference fuel cursor }

/-- Rules 1--5 are compared first; Rule 6 is consulted exactly when that key ties. -/
def comparePromotedOccurrenceBranchKeys
    (left right : PromotedOccurrenceBranchKey) : Ordering :=
  compareLex
    (Ordering.byKey PromotedOccurrenceBranchKey.ordinary
      compareFailClosedOccurrenceBranchProjectedKeys)
    (Ordering.byKey PromotedOccurrenceBranchKey.rule6 compareDenseOccurrenceRule6Keys)
    left right

theorem comparePromotedOccurrenceBranchKeys_transCmp :
    Std.TransCmp comparePromotedOccurrenceBranchKeys := by
  unfold comparePromotedOccurrenceBranchKeys
  letI := compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  letI := compareDenseOccurrenceRule6Keys_transCmp
  infer_instance

/-- Every successful complete production comparison factors through the complete Rules 1--6
unary key.  The theorem changes no failure into success. -/
theorem compareOccurrenceBranchesThroughRule6At_ordering_success_factors
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference : Nat) :
    ∀ fuel left right result,
      compareOccurrenceBranchesThroughRule6At? mol state reference fuel left right = some result →
        comparePromotedOccurrenceBranchKeys
          (buildPromotedOccurrenceBranchKey mol state reference fuel left)
          (buildPromotedOccurrenceBranchKey mol state reference fuel right) = result.ordering
  | 0, left, right, result, computed => by
      cases priorEq : compareOccurrenceBranches? mol state 0 left right with
      | none => simp [compareOccurrenceBranchesThroughRule6At?, priorEq] at computed
      | some prior =>
          have ordinaryFactor :=
            compareOccurrenceBranches_ordering_success_failClosed_factors mol state 0
              left right prior priorEq
          cases priorOrdering : prior.ordering with
          | lt =>
              simp [compareOccurrenceBranchesThroughRule6At?, priorEq, priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  compareFailClosedOccurrenceBranchProjectedKeys
                    (buildFailClosedOccurrenceBranchProjectedKey mol state 0 left)
                    (buildFailClosedOccurrenceBranchProjectedKey mol state 0 right) = .lt :=
                ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | gt =>
              simp [compareOccurrenceBranchesThroughRule6At?, priorEq, priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  compareFailClosedOccurrenceBranchProjectedKeys
                    (buildFailClosedOccurrenceBranchProjectedKey mol state 0 left)
                    (buildFailClosedOccurrenceBranchProjectedKey mol state 0 right) = .gt :=
                ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | eq =>
              simp [compareOccurrenceBranchesThroughRule6At?, priorEq, priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  compareFailClosedOccurrenceBranchProjectedKeys
                    (buildFailClosedOccurrenceBranchProjectedKey mol state 0 left)
                    (buildFailClosedOccurrenceBranchProjectedKey mol state 0 right) = .eq :=
                ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision,
                buildDenseOccurrenceRule6Key, denseDescriptorFrontiers,
                occurrenceRule6NodePriority, compareDenseOccurrenceRule6Keys, List.compareLex]
              cases compare (if left.node.atom = reference then 1 else 0)
                  (if right.node.atom = reference then 1 else 0) <;> rfl
  | fuel + 1, left, right, result, computed => by
      cases priorEq : compareOccurrenceBranches? mol state (fuel + 1) left right with
      | none => simp [compareOccurrenceBranchesThroughRule6At?, priorEq] at computed
      | some prior =>
          have ordinaryFactor :=
            compareOccurrenceBranches_ordering_success_failClosed_factors mol state (fuel + 1)
              left right prior priorEq
          cases priorOrdering : prior.ordering with
          | lt =>
              simp [compareOccurrenceBranchesThroughRule6At?, priorEq, priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  compareFailClosedOccurrenceBranchProjectedKeys
                    (buildFailClosedOccurrenceBranchProjectedKey mol state (fuel + 1) left)
                    (buildFailClosedOccurrenceBranchProjectedKey mol state (fuel + 1) right) =
                      .lt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | gt =>
              simp [compareOccurrenceBranchesThroughRule6At?, priorEq, priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  compareFailClosedOccurrenceBranchProjectedKeys
                    (buildFailClosedOccurrenceBranchProjectedKey mol state (fuel + 1) left)
                    (buildFailClosedOccurrenceBranchProjectedKey mol state (fuel + 1) right) =
                      .gt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | eq =>
              have ordinaryDecision :
                  compareFailClosedOccurrenceBranchProjectedKeys
                    (buildFailClosedOccurrenceBranchProjectedKey mol state (fuel + 1) left)
                    (buildFailClosedOccurrenceBranchProjectedKey mol state (fuel + 1) right) =
                      .eq := ordinaryFactor.trans priorOrdering
              let before := promotedRule6Before mol state reference (fuel + 1)
              have rule6Eq : compareOccurrenceRule6 mol before reference (fuel + 1)
                  [(left, right)] = some result.ordering := by
                simpa [compareOccurrenceBranchesThroughRule6At?, priorEq, priorOrdering,
                  before, promotedRule6Before] using congrArg (Option.map Rule6TrackedDecision.ordering)
                    computed
              have rule6Factor := compareOccurrenceRule6_singleton_success_factors mol before
                reference (fuel + 1) left right result.ordering rule6Eq
              simpa [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision, before] using rule6Factor

/-- Non-strict transitivity of every three successful complete Rules 1--6 comparisons. -/
theorem compareOccurrenceBranchesThroughRule6At_ordering_isLE_trans_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : Rule6TrackedDecision}
    (leftMiddleEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel left middle =
      some leftMiddle)
    (middleRightEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel middle right =
      some middleRight)
    (leftRightEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel left right =
      some leftRight)
    (leftMiddleLE : leftMiddle.ordering.isLE)
    (middleRightLE : middleRight.ordering.isLE) :
    leftRight.ordering.isLE := by
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  let build := buildPromotedOccurrenceBranchKey mol state reference fuel
  have keyLeftMiddle :
      (comparePromotedOccurrenceBranchKeys (build left) (build middle)).isLE := by
    rw [compareOccurrenceBranchesThroughRule6At_ordering_success_factors mol state reference
      fuel left middle leftMiddle leftMiddleEq]
    exact leftMiddleLE
  have keyMiddleRight :
      (comparePromotedOccurrenceBranchKeys (build middle) (build right)).isLE := by
    rw [compareOccurrenceBranchesThroughRule6At_ordering_success_factors mol state reference
      fuel middle right middleRight middleRightEq]
    exact middleRightLE
  have keyLeftRight :
      (comparePromotedOccurrenceBranchKeys (build left) (build right)).isLE :=
    Std.TransCmp.isLE_trans keyLeftMiddle keyMiddleRight
  rw [compareOccurrenceBranchesThroughRule6At_ordering_success_factors mol state reference
    fuel left right leftRight leftRightEq] at keyLeftRight
  exact keyLeftRight

/-- Every determined composition of two complete-key decisions is the endpoint decision. -/
theorem comparePromotedOccurrenceBranchKeys_compose
    {left middle right : PromotedOccurrenceBranchKey} {composed : Ordering}
    (composition : composeSuccessfulOrdering?
      (comparePromotedOccurrenceBranchKeys left middle)
      (comparePromotedOccurrenceBranchKeys middle right) = some composed) :
    comparePromotedOccurrenceBranchKeys left right = composed := by
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  cases leftMiddleEq : comparePromotedOccurrenceBranchKeys left middle <;>
    cases middleRightEq : comparePromotedOccurrenceBranchKeys middle right <;>
    simp [composeSuccessfulOrdering?, leftMiddleEq, middleRightEq] at composition <;>
    subst composed
  · exact Std.TransCmp.lt_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_lt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_eq_of_lt leftMiddleEq middleRightEq
  · exact Std.TransCmp.eq_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_eq_of_gt leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_gt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_trans leftMiddleEq middleRightEq

/-- Full composition law for every three successful complete Rules 1--6 comparisons. -/
theorem compareOccurrenceBranchesThroughRule6At_ordering_compose_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : Rule6TrackedDecision} {composed : Ordering}
    (leftMiddleEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel left middle =
      some leftMiddle)
    (middleRightEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel middle right =
      some middleRight)
    (leftRightEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel left right =
      some leftRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    leftRight.ordering = composed := by
  let build := buildPromotedOccurrenceBranchKey mol state reference fuel
  have keyComposition : composeSuccessfulOrdering?
      (comparePromotedOccurrenceBranchKeys (build left) (build middle))
      (comparePromotedOccurrenceBranchKeys (build middle) (build right)) = some composed := by
    rw [compareOccurrenceBranchesThroughRule6At_ordering_success_factors mol state reference
        fuel left middle leftMiddle leftMiddleEq,
      compareOccurrenceBranchesThroughRule6At_ordering_success_factors mol state reference
        fuel middle right middleRight middleRightEq]
    exact composition
  have endpoint := comparePromotedOccurrenceBranchKeys_compose keyComposition
  rw [compareOccurrenceBranchesThroughRule6At_ordering_success_factors mol state reference
    fuel left right leftRight leftRightEq] at endpoint
  exact endpoint

/-- On a descriptor-bearing branching frame, structural support supplies the endpoint comparison,
so the complete Rules 1--6 composition law needs no separately assumed third success. -/
theorem descriptor_branching_frame_promoted_ordering_compose
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (reference : Nat) {left middle right : CanonicalRerootCursor}
    (left_mem : left ∈ roots) (_middle_mem : middle ∈ roots) (right_mem : right ∈ roots)
    {leftMiddle middleRight : Rule6TrackedDecision} {composed : Ordering}
    (leftMiddleEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel left middle =
      some leftMiddle)
    (middleRightEq : compareOccurrenceBranchesThroughRule6At? mol state reference fuel middle right =
      some middleRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    ∃ leftRight,
      compareOccurrenceBranchesThroughRule6At? mol state reference fuel left right =
          some leftRight ∧
        leftRight.ordering = composed := by
  rcases frame.promoted_comparison_exists reference left_mem right_mem with
    ⟨leftRight, leftRightEq⟩
  exact ⟨leftRight, leftRightEq,
    compareOccurrenceBranchesThroughRule6At_ordering_compose_of_three_success
      mol state reference fuel leftMiddleEq middleRightEq leftRightEq composition⟩

end TetraStereo.OneCenter.ProductionCIPRule6PromotedComparatorLaws
