import TetraStereo.OneCenter.CIPAuthoritativeRule6Comparator
import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceDescriptorComparatorLaws

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6PromotedComparatorLaws

/-!
# Unary-key law for width-unbounded promoted Rule 6

This is the frontier-cap-free analogue of the production promoted-comparator theorem.  It compiles
the authoritative traversal into one opponent-independent complete Rules-1--6 key per occurrence.
Every successful executable decision is then a comparison of two such keys, so its ordering laws
are inherited from ordinary lexicographic comparison rather than assumed of the algorithm.
-/

open RawMolecule
open AuthoritativeCIPOccurrenceDescriptorComparatorLaws

/-- Unary label selected by Rule 6 at one occurrence. -/
def occurrenceRule6NodePriority (reference : Nat) (cursor : CanonicalRerootCursor) : Nat :=
  if cursor.node.atom == reference then 1 else 0

/-- The executable first-difference scan is exactly lexicographic comparison of its unary
promotion labels. -/
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
        simp [headEq, inductionHypothesis]

/-- Width-unbounded unary Rule-6 key: breadth-first promotion labels after authoritative child
ranking. -/
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

/-- Total dense counterpart of the authoritative Rule-6 sphere traversal. -/
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

/-- The dense recursion is comparison of the flattened authoritative frontier labels. -/
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

/-- A terminal pair omitted by the executable traversal is silent for reference promotion. -/
def Rule6PairSilent (mol : RawMolecule) (reference : Nat) (pair : DenseRule6Pair) : Prop :=
  cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true ∧
    compare (occurrenceRule6NodePriority reference pair.1)
      (occurrenceRule6NodePriority reference pair.2) = .eq

/-- The executable active frontier is the dense frontier with only silent terminal pairs erased. -/
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

/-- One successful authoritative frontier expansion preserves the active/dense erasure relation.
No length bound appears in this theorem. -/
theorem nextRule6Pairs_dense_related (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) {active dense next : List DenseRule6Pair}
    (related : ErasesSilentRule6Pairs mol reference active dense)
    (allTied : ∀ pair, pair ∈ active →
      compare (occurrenceRule6NodePriority reference pair.1)
        (occurrenceRule6NodePriority reference pair.2) = .eq)
    (computed : nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight active =
      some next) :
    ErasesSilentRule6Pairs mol reference next
      (denseNextDescriptorPairs mol beforeLeft beforeRight dense) := by
  induction related generalizing next with
  | nil =>
      simp [nextOccurrenceDescriptorPairsAuthoritative?] at computed
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
      simp only [nextOccurrenceDescriptorPairsAuthoritative?] at computed
      cases restEq : nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeRight
          activeTail with
      | none => simp [restEq] at computed
      | some rest =>
          have restRelated := inductionHypothesis tailTied restEq
          cases leftTerminal : cursorTerminal mol pair.1 <;>
            cases rightTerminal : cursorTerminal mol pair.2
          · cases leftEq : rankedCursorChildrenAuthoritative? mol beforeLeft pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildrenAuthoritative? mol beforeRight pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseDescriptorChildren_eq_of_success mol beforeLeft
                      pair.1 left leftEq
                    have denseRight := denseDescriptorChildren_eq_of_success mol beforeRight
                      pair.2 right rightEq
                    simp only [denseNextDescriptorPairs, List.flatMap_cons, List.flatMap_nil,
                      denseLeft, denseRight]
                    exact ErasesSilentRule6Pairs.keep_all (left.zip right) restRelated
          · cases leftEq : rankedCursorChildrenAuthoritative? mol beforeLeft pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildrenAuthoritative? mol beforeRight pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseDescriptorChildren_eq_of_success mol beforeLeft
                      pair.1 left leftEq
                    have denseRight := denseDescriptorChildren_eq_of_success mol beforeRight
                      pair.2 right rightEq
                    simp only [denseNextDescriptorPairs, List.flatMap_cons, List.flatMap_nil,
                      denseLeft, denseRight]
                    exact ErasesSilentRule6Pairs.keep_all (left.zip right) restRelated
          · cases leftEq : rankedCursorChildrenAuthoritative? mol beforeLeft pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildrenAuthoritative? mol beforeRight pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseDescriptorChildren_eq_of_success mol beforeLeft
                      pair.1 left leftEq
                    have denseRight := denseDescriptorChildren_eq_of_success mol beforeRight
                      pair.2 right rightEq
                    simp only [denseNextDescriptorPairs, List.flatMap_cons, List.flatMap_nil,
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

/-- Every successful uncapped promoted-sphere traversal factors through the dense unary key. -/
theorem compareOccurrenceRule6Authoritative_success_factors (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference : Nat) : ∀ fuel active dense decision,
    ErasesSilentRule6Pairs mol reference active dense →
    compareOccurrenceRule6Authoritative mol beforeLeft reference fuel active = some decision →
    beforeLeft = beforeRight →
    compareDenseOccurrenceRule6 mol beforeLeft beforeRight reference fuel dense = decision
  | 0, active, dense, decision, related, computed, beforeEq => by
      subst beforeRight
      simp only [compareOccurrenceRule6Authoritative] at computed
      have labelsEq := related.labels_eq
      cases current : compareOccurrenceRule6PairLabels reference active with
      | lt =>
          simp [current] at computed
          subst decision
          have activeCurrent : compareDenseRule6PairLabels reference active = .lt := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          exact labelsEq.symm.trans activeCurrent
      | gt =>
          simp [current] at computed
          subst decision
          have activeCurrent : compareDenseRule6PairLabels reference active = .gt := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          exact labelsEq.symm.trans activeCurrent
      | eq =>
          cases nextEq : nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeLeft
              active with
          | none => simp [current, nextEq] at computed
          | some next =>
              cases next with
              | nil =>
                  simp [current, nextEq] at computed
                  subst decision
                  have activeCurrent : compareDenseRule6PairLabels reference active = .eq := by
                    rw [compareDenseRule6PairLabels,
                      ← compareOccurrenceRule6PairLabels_eq_compareLex]
                    exact current
                  exact labelsEq.symm.trans activeCurrent
              | cons nextHead nextTail => simp [current, nextEq] at computed
  | fuel + 1, active, dense, decision, related, computed, beforeEq => by
      subst beforeRight
      simp only [compareOccurrenceRule6Authoritative] at computed
      have labelsEq := related.labels_eq
      cases current : compareOccurrenceRule6PairLabels reference active with
      | lt =>
          simp [current] at computed
          subst decision
          have activeCurrent : compareDenseRule6PairLabels reference active = .lt := by
            rw [compareDenseRule6PairLabels, ← compareOccurrenceRule6PairLabels_eq_compareLex]
            exact current
          have denseCurrent := labelsEq.symm.trans activeCurrent
          simp [compareDenseOccurrenceRule6, denseCurrent]
      | gt =>
          simp [current] at computed
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
          cases nextEq : nextOccurrenceDescriptorPairsAuthoritative? mol beforeLeft beforeLeft
              active with
          | none => simp [current, nextEq] at computed
          | some next =>
              cases next with
              | nil =>
                  simp [current, nextEq] at computed
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
                      compareOccurrenceRule6Authoritative mol beforeLeft reference fuel
                          (nextHead :: nextTail) = some decision := computed
                  have allTied := compareOccurrenceRule6PairLabels_eq_implies_all_tied
                    reference active current
                  have nextRelated := nextRule6Pairs_dense_related mol beforeLeft beforeLeft
                    reference related allTied nextEq
                  have recursive := compareOccurrenceRule6Authoritative_success_factors mol
                    beforeLeft beforeLeft reference fuel (nextHead :: nextTail)
                    (denseNextDescriptorPairs mol beforeLeft beforeLeft dense) decision
                    nextRelated recursiveEq rfl
                  simp [compareDenseOccurrenceRule6, denseCurrent, recursive]

/-- A successful singleton authoritative traversal is exactly comparison of two independent dense
Rule-6 keys. -/
theorem compareOccurrenceRule6Authoritative_singleton_success_factors (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (reference fuel : Nat) (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : compareOccurrenceRule6Authoritative mol before reference fuel [(left, right)] =
      some decision) :
    compareDenseOccurrenceRule6Keys
        (buildDenseOccurrenceRule6Key mol before reference fuel left)
        (buildDenseOccurrenceRule6Key mol before reference fuel right) = decision := by
  have factored := compareOccurrenceRule6Authoritative_success_factors mol before before reference
    fuel [(left, right)] [(left, right)] decision
    (ErasesSilentRule6Pairs.refl [(left, right)]) computed rfl
  rw [compareDenseOccurrenceRule6_eq_frontiers] at factored
  exact factored

/-! ## Complete width-unbounded Rules 1--6 key -/

/-- At positive depth, authoritative Rule 6 ranks child occurrences by the complete promoted
comparison at the preceding depth. -/
def promotedRule6Before (mol : RawMolecule) (state : OccurrenceAuxState) (reference : Nat) :
    Nat → CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering
  | 0 => fun _ _ => none
  | depth + 1 => fun left right =>
      (compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference depth left right).map
        Rule6TrackedDecision.ordering

/-- One opponent-independent width-unbounded key for Rules 1--6. -/
structure PromotedOccurrenceBranchKey where
  ordinary : AuthoritativeCIPOccurrenceDescriptorComparatorLaws.FailClosedOccurrenceBranchProjectedKey
  rule6 : DenseOccurrenceRule6Key

def buildPromotedOccurrenceBranchKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference fuel : Nat) (cursor : CanonicalRerootCursor) : PromotedOccurrenceBranchKey :=
  { ordinary :=
      AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
        mol state fuel cursor
    rule6 := buildDenseOccurrenceRule6Key mol
      (promotedRule6Before mol state reference fuel) reference fuel cursor }

/-- Rules 1--5 precede Rule 6 in the complete authoritative key. -/
def comparePromotedOccurrenceBranchKeys
    (left right : PromotedOccurrenceBranchKey) : Ordering :=
  compareLex
    (Ordering.byKey PromotedOccurrenceBranchKey.ordinary
      AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys)
    (Ordering.byKey PromotedOccurrenceBranchKey.rule6 compareDenseOccurrenceRule6Keys)
    left right

theorem comparePromotedOccurrenceBranchKeys_transCmp :
    Std.TransCmp comparePromotedOccurrenceBranchKeys := by
  unfold comparePromotedOccurrenceBranchKeys
  letI :=
    AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  letI := compareDenseOccurrenceRule6Keys_transCmp
  infer_instance

/-- Recursive child-ranking callback for the ungated completeness path. -/
def promotedRule6BeforeUnrestricted (mol : RawMolecule) (state : OccurrenceAuxState)
    (reference : Nat) :
    Nat → CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering
  | 0 => fun _ _ => none
  | depth + 1 => fun left right =>
      (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference depth
        left right).map Rule6TrackedDecision.ordering

/-- Opponent-independent Rules-1--6 key using the unrestricted recursive callback. -/
def buildPromotedOccurrenceBranchKeyUnrestricted (mol : RawMolecule)
    (state : OccurrenceAuxState) (reference fuel : Nat)
    (cursor : CanonicalRerootCursor) : PromotedOccurrenceBranchKey :=
  { ordinary :=
      AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
        mol state fuel cursor
    rule6 := buildDenseOccurrenceRule6Key mol
      (promotedRule6BeforeUnrestricted mol state reference fuel) reference fuel cursor }

/-- Every successful width-unbounded complete comparison factors through the authoritative unary
Rules-1--6 key. -/
theorem compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_success_factors
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference : Nat) :
    ∀ fuel left right result,
      compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel left right =
          some result →
        comparePromotedOccurrenceBranchKeys
          (buildPromotedOccurrenceBranchKey mol state reference fuel left)
          (buildPromotedOccurrenceBranchKey mol state reference fuel right) = result.ordering
  | 0, left, right, result, computed => by
      cases priorEq : compareOccurrenceBranchesAuthoritative? mol state 0 left right with
      | none =>
          simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq] at computed
      | some prior =>
          have ordinaryFactor :=
            AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareOccurrenceBranches_ordering_success_failClosed_factors
              mol state 0 left right prior priorEq
          cases priorOrdering : prior.ordering with
          | lt =>
              simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 right) = .lt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | gt =>
              simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 right) = .gt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | eq =>
              simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 right) = .eq := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision,
                buildDenseOccurrenceRule6Key, denseDescriptorFrontiers,
                occurrenceRule6NodePriority, compareDenseOccurrenceRule6Keys, List.compareLex]
              cases compare (if left.node.atom = reference then 1 else 0)
                  (if right.node.atom = reference then 1 else 0) <;> rfl
  | fuel + 1, left, right, result, computed => by
      cases priorEq : compareOccurrenceBranchesAuthoritative? mol state (fuel + 1) left right with
      | none =>
          simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq] at computed
      | some prior =>
          have ordinaryFactor :=
            AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareOccurrenceBranches_ordering_success_failClosed_factors
              mol state (fuel + 1) left right prior priorEq
          cases priorOrdering : prior.ordering with
          | lt =>
              simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) right) = .lt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | gt =>
              simp [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) right) = .gt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision]
          | eq =>
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) right) = .eq := ordinaryFactor.trans priorOrdering
              let before := promotedRule6Before mol state reference (fuel + 1)
              have rule6Eq : compareOccurrenceRule6Authoritative mol before reference (fuel + 1)
                  [(left, right)] = some result.ordering := by
                simpa [compareOccurrenceBranchesThroughRule6AtAuthoritative?, priorEq,
                  priorOrdering, before, promotedRule6Before] using
                    congrArg (Option.map Rule6TrackedDecision.ordering) computed
              have rule6Factor :=
                compareOccurrenceRule6Authoritative_singleton_success_factors mol before
                  reference (fuel + 1) left right result.ordering rule6Eq
              simpa [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKey, ordinaryDecision, before] using rule6Factor

/-- Non-strict transitivity of every three successful uncapped complete Rules-1--6 comparisons. -/
theorem compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference : Nat) :
    ∀ fuel left right result,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference fuel left right =
          some result →
        comparePromotedOccurrenceBranchKeys
          (buildPromotedOccurrenceBranchKeyUnrestricted mol state reference fuel left)
          (buildPromotedOccurrenceBranchKeyUnrestricted mol state reference fuel right) = result.ordering
  | 0, left, right, result, computed => by
      cases priorEq : compareOccurrenceBranchesUnrestrictedAuthoritative? mol state 0 left right with
      | none =>
          simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq] at computed
      | some prior =>
          have ordinaryFactor :=
            AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareOccurrenceBranchesUnrestricted_ordering_success_factors
              mol state 0 left right prior priorEq
          cases priorOrdering : prior.ordering with
          | lt =>
              simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 right) = .lt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKeyUnrestricted, ordinaryDecision]
          | gt =>
              simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 right) = .gt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKeyUnrestricted, ordinaryDecision]
          | eq =>
              simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state 0 right) = .eq := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKeyUnrestricted, ordinaryDecision,
                buildDenseOccurrenceRule6Key, denseDescriptorFrontiers,
                occurrenceRule6NodePriority, compareDenseOccurrenceRule6Keys, List.compareLex]
              cases compare (if left.node.atom = reference then 1 else 0)
                  (if right.node.atom = reference then 1 else 0) <;> rfl
  | fuel + 1, left, right, result, computed => by
      cases priorEq : compareOccurrenceBranchesUnrestrictedAuthoritative? mol state (fuel + 1) left right with
      | none =>
          simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq] at computed
      | some prior =>
          have ordinaryFactor :=
            AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareOccurrenceBranchesUnrestricted_ordering_success_factors
              mol state (fuel + 1) left right prior priorEq
          cases priorOrdering : prior.ordering with
          | lt =>
              simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) right) = .lt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKeyUnrestricted, ordinaryDecision]
          | gt =>
              simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
                priorOrdering] at computed
              subst result
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) right) = .gt := ordinaryFactor.trans priorOrdering
              simp [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKeyUnrestricted, ordinaryDecision]
          | eq =>
              have ordinaryDecision :
                  AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) left)
                    (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
                      mol state (fuel + 1) right) = .eq := ordinaryFactor.trans priorOrdering
              let before := promotedRule6BeforeUnrestricted mol state reference (fuel + 1)
              have rule6Eq : compareOccurrenceRule6Authoritative mol before reference (fuel + 1)
                  [(left, right)] = some result.ordering := by
                simpa [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, priorEq,
                  priorOrdering, before, promotedRule6BeforeUnrestricted] using
                    congrArg (Option.map Rule6TrackedDecision.ordering) computed
              have rule6Factor :=
                compareOccurrenceRule6Authoritative_singleton_success_factors mol before
                  reference (fuel + 1) left right result.ordering rule6Eq
              simpa [comparePromotedOccurrenceBranchKeys, compareLex, Ordering.byKey,
                buildPromotedOccurrenceBranchKeyUnrestricted, ordinaryDecision, before] using rule6Factor

/-- Non-strict transitivity of every three successful uncapped complete Rules-1--6 comparisons. -/

theorem compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_isLE_trans_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : Rule6TrackedDecision}
    (leftMiddleEq : compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel
      left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel
      middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel
      left right = some leftRight)
    (leftMiddleLE : leftMiddle.ordering.isLE)
    (middleRightLE : middleRight.ordering.isLE) :
    leftRight.ordering.isLE := by
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  let build := buildPromotedOccurrenceBranchKey mol state reference fuel
  have keyLeftMiddle :
      (comparePromotedOccurrenceBranchKeys (build left) (build middle)).isLE := by
    rw [compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_success_factors mol state
      reference fuel left middle leftMiddle leftMiddleEq]
    exact leftMiddleLE
  have keyMiddleRight :
      (comparePromotedOccurrenceBranchKeys (build middle) (build right)).isLE := by
    rw [compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_success_factors mol state
      reference fuel middle right middleRight middleRightEq]
    exact middleRightLE
  have keyLeftRight :
      (comparePromotedOccurrenceBranchKeys (build left) (build right)).isLE :=
    Std.TransCmp.isLE_trans keyLeftMiddle keyMiddleRight
  rw [compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_success_factors mol state
    reference fuel left right leftRight leftRightEq] at keyLeftRight
  exact keyLeftRight

/-- Every determined composition of two authoritative complete-key decisions is the endpoint
decision. -/
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

/-- Full composition law for every three successful width-unbounded Rules-1--6 comparisons. -/
theorem compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_compose_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : Rule6TrackedDecision} {composed : Ordering}
    (leftMiddleEq : compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel
      left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel
      middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranchesThroughRule6AtAuthoritative? mol state reference fuel
      left right = some leftRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    leftRight.ordering = composed := by
  let build := buildPromotedOccurrenceBranchKey mol state reference fuel
  have keyComposition : composeSuccessfulOrdering?
      (comparePromotedOccurrenceBranchKeys (build left) (build middle))
      (comparePromotedOccurrenceBranchKeys (build middle) (build right)) = some composed := by
    rw [compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_success_factors mol state
        reference fuel left middle leftMiddle leftMiddleEq,
      compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_success_factors mol state
        reference fuel middle right middleRight middleRightEq]
    exact composition
  have endpoint := comparePromotedOccurrenceBranchKeys_compose keyComposition
  rw [compareOccurrenceBranchesThroughRule6AtAuthoritative_ordering_success_factors mol state
    reference fuel left right leftRight leftRightEq] at endpoint
  exact endpoint

/-- Non-strict transitivity of every three successful ungated Rules-1--6 comparisons. -/
theorem compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_isLE_trans_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : Rule6TrackedDecision}
    (leftMiddleEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference fuel
        left middle = some leftMiddle)
    (middleRightEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference fuel
        middle right = some middleRight)
    (leftRightEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference fuel
        left right = some leftRight)
    (leftMiddleLE : leftMiddle.ordering.isLE)
    (middleRightLE : middleRight.ordering.isLE) :
    leftRight.ordering.isLE := by
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  let build := buildPromotedOccurrenceBranchKeyUnrestricted mol state reference fuel
  have keyLeftMiddle :
      (comparePromotedOccurrenceBranchKeys (build left) (build middle)).isLE := by
    rw [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
      mol state reference fuel left middle leftMiddle leftMiddleEq]
    exact leftMiddleLE
  have keyMiddleRight :
      (comparePromotedOccurrenceBranchKeys (build middle) (build right)).isLE := by
    rw [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
      mol state reference fuel middle right middleRight middleRightEq]
    exact middleRightLE
  have keyLeftRight :
      (comparePromotedOccurrenceBranchKeys (build left) (build right)).isLE :=
    Std.TransCmp.isLE_trans keyLeftMiddle keyMiddleRight
  rw [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
    mol state reference fuel left right leftRight leftRightEq] at keyLeftRight
  exact keyLeftRight

/-- Every compatible composition of two successful ungated Rules-1--6 outcomes is the successful
endpoint outcome. -/
theorem compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_compose_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : Rule6TrackedDecision} {composed : Ordering}
    (leftMiddleEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference fuel
        left middle = some leftMiddle)
    (middleRightEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference fuel
        middle right = some middleRight)
    (leftRightEq :
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state reference fuel
        left right = some leftRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    leftRight.ordering = composed := by
  let build := buildPromotedOccurrenceBranchKeyUnrestricted mol state reference fuel
  have keyComposition : composeSuccessfulOrdering?
      (comparePromotedOccurrenceBranchKeys (build left) (build middle))
      (comparePromotedOccurrenceBranchKeys (build middle) (build right)) = some composed := by
    rw [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
        mol state reference fuel left middle leftMiddle leftMiddleEq,
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
        mol state reference fuel middle right middleRight middleRightEq]
    exact composition
  have endpoint := comparePromotedOccurrenceBranchKeys_compose keyComposition
  rw [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors
    mol state reference fuel left right leftRight leftRightEq] at endpoint
  exact endpoint

end TetraStereo.OneCenter.AuthoritativeCIPRule6PromotedComparatorLaws
