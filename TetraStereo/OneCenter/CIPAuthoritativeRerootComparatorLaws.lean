import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceComparator

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPRerootComparatorLaws

open RawMolecule

/-! ## A lawful unary key for the authoritative reroot comparator

The authoritative comparator is partial when an exact Rule-1a label cannot be constructed or a
local occurrence exceeds the stated bonding-number-six domain. This module totalizes only queries
that the executable comparator did not successfully reach, compiles each cursor independently to
a dense five-slot key, and proves that every successful Rule-2 result is exactly the comparison of
the two independent keys.
-/

private def atomicLabelValue (label : CIPAtomicLabel) : ℚ :=
  (label.numerator : ℚ) / (label.effectiveDenominator : ℚ)

private def compareAtomicLabelValue (left right : CIPAtomicLabel) : Ordering :=
  Ordering.byKey atomicLabelValue (fun x y => compareOfLessAndEq x y) left right

private theorem compareCIPAtomicLabel_eq_compare_value (left right : CIPAtomicLabel) :
    compareCIPAtomicLabel left right = compareAtomicLabelValue left right := by
  unfold compareCIPAtomicLabel compareAtomicLabelValue Ordering.byKey atomicLabelValue
  rw [LinearOrder.compare_eq_compareOfLessAndEq]
  unfold compareOfLessAndEq
  have leftPositive : (0 : ℚ) < left.effectiveDenominator := by
    have positive : 0 < left.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast positive
  have rightPositive : (0 : ℚ) < right.effectiveDenominator := by
    have positive : 0 < right.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast positive
  simp only [div_lt_div_iff₀ leftPositive rightPositive,
    div_eq_div_iff leftPositive.ne' rightPositive.ne']
  norm_cast

private local instance rationalCompareTrans :
    Std.TransCmp (fun left right : ℚ => compareOfLessAndEq left right) :=
  Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_antisymm
    (fun value => lt_irrefl value)
    (fun {_ _ _} leftMiddle middleRight => lt_trans leftMiddle middleRight)
    (fun notLeftRight notRightLeft =>
      le_antisymm (le_of_not_gt notRightLeft) (le_of_not_gt notLeftRight))

private local instance atomicValueCompareTrans : Std.TransCmp compareAtomicLabelValue := by
  unfold compareAtomicLabelValue
  infer_instance

private theorem compareCIPAtomicLabel_transCmp : Std.TransCmp compareCIPAtomicLabel where
  eq_swap {left right} := by
    rw [compareCIPAtomicLabel_eq_compare_value,
      compareCIPAtomicLabel_eq_compare_value]
    exact Std.OrientedCmp.eq_swap
  isLE_trans {left middle right} leftMiddle middleRight := by
    rw [compareCIPAtomicLabel_eq_compare_value] at leftMiddle middleRight ⊢
    exact Std.TransCmp.isLE_trans leftMiddle middleRight

/-- Total label used only to define an opponent-independent semantic key. Every successful
authoritative label query agrees with it; the default is unreachable in every successful-factor
theorem below. -/
def authoritativeRule1aLabelTotal (mol : RawMolecule) (node : CanonicalBranchNode) :
    CIPAtomicLabel :=
  (mol.canonicalRule1aLabelAuthoritative? node).getD { numerator := 0, denominator := 1 }

/-- Total counterpart of the authoritative primitive node comparator. -/
def compareCanonicalNodeRuleTotal (mol : RawMolecule) (rule : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Ordering :=
  match rule with
  | .rule1a => compareCIPAtomicLabel (authoritativeRule1aLabelTotal mol left)
      (authoritativeRule1aLabelTotal mol right)
  | .rule1b | .rule2 => mol.compareCanonicalNodeRule rule left right

/-- Totalize only the internal sibling-ranking query.  On every successful production query this
is definitionally the production result. -/
def totalizedCursorDecision (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Ordering :=
  (compareCursorBranchAtAuthoritative? mol fuel .rule2 left right).getD .eq

/-- Total counterpart of production insertion. -/
def insertCursorTotal (mol : RawMolecule) (fuel : ℕ)
    (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → List CanonicalRerootCursor
  | [] => [candidate]
  | head :: tail =>
      match totalizedCursorDecision mol fuel candidate head with
      | .gt | .eq => candidate :: head :: tail
      | .lt => head :: insertCursorTotal mol fuel candidate tail

/-- Total counterpart of production insertion sort. -/
def sortCursorsTotal (mol : RawMolecule) (fuel : ℕ) :
    List CanonicalRerootCursor → List CanonicalRerootCursor
  | [] => []
  | cursor :: cursors =>
      insertCursorTotal mol fuel cursor (sortCursorsTotal mol fuel cursors)

theorem totalizedCursorDecision_eq_of_success (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : compareCursorBranchAtAuthoritative? mol fuel .rule2 left right = some decision) :
    totalizedCursorDecision mol fuel left right = decision := by
  simp [totalizedCursorDecision, computed]

theorem insertCursorTotal_eq_of_success (mol : RawMolecule) (fuel : ℕ)
    (candidate : CanonicalRerootCursor) :
    ∀ cursors sorted,
      insertCursorBy? (compareCursorBranchAtAuthoritative? mol fuel .rule2) candidate cursors = some sorted →
      insertCursorTotal mol fuel candidate cursors = sorted
  | [], sorted, computed => by
      simp [insertCursorBy?] at computed
      subst sorted
      rfl
  | head :: tail, sorted, computed => by
      simp only [insertCursorBy?] at computed
      cases comparisonEq : compareCursorBranchAtAuthoritative? mol fuel .rule2 candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          have totalized : totalizedCursorDecision mol fuel candidate head = decision :=
            totalizedCursorDecision_eq_of_success mol fuel candidate head decision comparisonEq
          cases decision with
          | lt =>
              simp only [comparisonEq, Option.map_eq_some_iff] at computed
              rcases computed with ⟨deeper, deeperEq, rfl⟩
              simp [insertCursorTotal, totalized,
                insertCursorTotal_eq_of_success mol fuel candidate tail deeper deeperEq]
          | eq =>
              simp [comparisonEq] at computed
              subst sorted
              simp [insertCursorTotal, totalized]
          | gt =>
              simp [comparisonEq] at computed
              subst sorted
              simp [insertCursorTotal, totalized]

theorem sortCursorsTotal_eq_of_success (mol : RawMolecule) (fuel : ℕ) :
    ∀ cursors sorted,
      sortCursorsBy? (compareCursorBranchAtAuthoritative? mol fuel .rule2) cursors = some sorted →
      sortCursorsTotal mol fuel cursors = sorted
  | [], sorted, computed => by
      simp [sortCursorsBy?] at computed
      subst sorted
      rfl
  | cursor :: cursors, sorted, computed => by
      simp only [sortCursorsBy?] at computed
      cases tailEq : sortCursorsBy? (compareCursorBranchAtAuthoritative? mol fuel .rule2) cursors with
      | none => simp [tailEq] at computed
      | some tail =>
          have sortedTail := sortCursorsTotal_eq_of_success mol fuel cursors tail tailEq
          have inserted := insertCursorTotal_eq_of_success mol fuel cursor tail sorted (by
            simpa [tailEq] using computed)
          simpa [sortCursorsTotal, sortedTail] using inserted

@[simp] theorem insertCursorTotal_length (mol : RawMolecule) (fuel : ℕ)
    (candidate : CanonicalRerootCursor) : ∀ cursors,
    (insertCursorTotal mol fuel candidate cursors).length = cursors.length + 1
  | [] => rfl
  | head :: tail => by
      simp only [insertCursorTotal]
      cases totalizedCursorDecision mol fuel candidate head <;>
        simp [insertCursorTotal_length mol fuel candidate tail]

@[simp] theorem sortCursorsTotal_length (mol : RawMolecule) (fuel : ℕ) : ∀ cursors,
    (sortCursorsTotal mol fuel cursors).length = cursors.length
  | [] => rfl
  | cursor :: cursors => by
      simp [sortCursorsTotal, sortCursorsTotal_length mol fuel cursors]

/-- A dense reroot key. Its three fields share the same full five-slot sphere traversal. -/
structure DenseRerootKey where
  rule1a : List CIPAtomicLabel
  rule1b : List ℕ
  rule2 : List ℕ
  deriving DecidableEq, Repr

private def cursorRule2Mass (mol : RawMolecule) (cursor : CanonicalRerootCursor) : ℕ :=
  match cursor.node.provenance with
  | .realAtom => mol.atomMassAt cursor.node.atom
  | _ => 0

/-- Total five-slot child frame. Supported authoritative expansions agree with this frame. -/
def denseRankedCursorChildren (mol : RawMolecule) (rankFuel : ℕ)
    (cursor : CanonicalRerootCursor) : List CanonicalRerootCursor :=
  let sorted := sortCursorsTotal mol rankFuel (cursor.children mol)
  let bounded := sorted.take RawMolecule.authoritativeChildSlots
  let phantom : CanonicalRerootCursor :=
    { node := mol.canonicalPhantom cursor.node.atom
        (cursor.node.rule1bRootDistance + 1) }
  bounded ++ List.replicate (RawMolecule.authoritativeChildSlots - bounded.length) phantom

def denseNextCursorFrontier (mol : RawMolecule) (rankFuel : ℕ)
    (frontier : List CanonicalRerootCursor) : List CanonicalRerootCursor :=
  frontier.flatMap (denseRankedCursorChildren mol rankFuel)

def denseCursorFrontiers (mol : RawMolecule) (rankFuel : ℕ) :
    ℕ → List CanonicalRerootCursor → List (List CanonicalRerootCursor)
  | 0, frontier => [frontier]
  | depth + 1, frontier =>
      frontier :: denseCursorFrontiers mol rankFuel depth
        (denseNextCursorFrontier mol rankFuel frontier)

/-- Compile a cursor without consulting an opponent. -/
def buildDenseRerootKey (mol : RawMolecule) :
    ℕ → CanonicalRerootCursor → DenseRerootKey
  | 0, cursor =>
      { rule1a := [authoritativeRule1aLabelTotal mol cursor.node]
        rule1b := [cursor.node.rule1bRootDistance]
        rule2 := [cursorRule2Mass mol cursor] }
  | fuel + 1, cursor =>
      let frontiers := denseCursorFrontiers mol fuel (fuel + 1) [cursor]
      let nodes := frontiers.flatten
      { rule1a := nodes.map fun entry => authoritativeRule1aLabelTotal mol entry.node
        rule1b := nodes.map fun entry => entry.node.rule1bRootDistance
        rule2 := nodes.map (cursorRule2Mass mol) }

def compareDenseRule1b (left right : ℕ) : Ordering :=
  if left < right then .gt else if right < left then .lt else .eq

private theorem compareDenseRule1b_eq_flip_compare (left right : ℕ) :
    compareDenseRule1b left right = flip compare left right := by
  by_cases leftRight : left < right
  · have compared : compare right left = Ordering.gt := Nat.compare_eq_gt.mpr leftRight
    simp [compareDenseRule1b, leftRight, flip, compared]
  · by_cases rightLeft : right < left
    · have compared : compare right left = Ordering.lt := Nat.compare_eq_lt.mpr rightLeft
      simp [compareDenseRule1b, leftRight, rightLeft, flip, compared]
    · have equal : left = right := Nat.le_antisymm (Nat.le_of_not_gt rightLeft)
          (Nat.le_of_not_gt leftRight)
      subst right
      simp [compareDenseRule1b, flip]

private local instance denseRule1bTrans : Std.TransCmp compareDenseRule1b := by
  have comparatorEq : compareDenseRule1b = flip compare := by
    funext left right
    exact compareDenseRule1b_eq_flip_compare left right
  rw [comparatorEq]
  infer_instance

def compareDenseRerootKeys (left right : DenseRerootKey) : Ordering :=
  compareLex
    (Ordering.byKey DenseRerootKey.rule1a (List.compareLex compareCIPAtomicLabel))
    (compareLex
      (Ordering.byKey DenseRerootKey.rule1b (List.compareLex compareDenseRule1b))
      (Ordering.byKey DenseRerootKey.rule2 (List.compareLex compare))) left right

private local instance denseAtomicLabelTrans : Std.TransCmp compareCIPAtomicLabel :=
  compareCIPAtomicLabel_transCmp

/-- The unary dense-key comparator is a transitive oriented comparator. -/
theorem compareDenseRerootKeys_transCmp : Std.TransCmp compareDenseRerootKeys := by
  unfold compareDenseRerootKeys
  infer_instance

theorem denseRankedCursorChildren_eq_of_success (mol : RawMolecule) (fuel : ℕ)
    (cursor : CanonicalRerootCursor) (ranked : List CanonicalRerootCursor)
    (computed : rankedCursorChildrenAuthoritative? mol (compareCursorBranchAtAuthoritative? mol fuel .rule2) cursor =
      some ranked) :
    denseRankedCursorChildren mol fuel cursor = ranked := by
  unfold rankedCursorChildrenAuthoritative? at computed
  let children := cursor.children mol
  by_cases tooWide : RawMolecule.authoritativeChildSlots < children.length
  · simp [children, tooWide] at computed
  · cases sortedEq : sortCursorsBy? (compareCursorBranchAtAuthoritative? mol fuel .rule2) children with
    | none => simp [children, tooWide, sortedEq] at computed
    | some sorted =>
        have totalSorted : sortCursorsTotal mol fuel children = sorted :=
          sortCursorsTotal_eq_of_success mol fuel children sorted sortedEq
        have childLength : children.length ≤ RawMolecule.authoritativeChildSlots :=
          Nat.le_of_not_gt tooWide
        have sortedLength : sorted.length = children.length := by
          rw [← totalSorted]
          exact sortCursorsTotal_length mol fuel children
        have rankedEq : ranked = sorted ++ List.replicate
            (RawMolecule.authoritativeChildSlots - sorted.length)
            { node := mol.canonicalPhantom cursor.node.atom
                (cursor.node.rule1bRootDistance + 1) } := by
          simpa [children, tooWide, sortedEq] using computed.symm
        have takeEq : sorted.take RawMolecule.authoritativeChildSlots = sorted :=
          List.take_of_length_le (sortedLength.trans_le childLength)
        simp [denseRankedCursorChildren, children, totalSorted, takeEq,
          sortedLength, rankedEq]

def densePhantomCursor (mol : RawMolecule) (parent distance : ℕ) :
    CanonicalRerootCursor :=
  { node := mol.canonicalPhantom parent distance }

theorem cursor_children_eq_nil_of_terminal (mol : RawMolecule)
    (cursor : CanonicalRerootCursor) (terminal : cursorTerminal mol cursor = true) :
    cursor.children mol = [] := by
  cases childrenEq : cursor.children mol with
  | nil => rfl
  | cons child children =>
      cases forcedEq : cursor.node.forcedLeaf with
      | false => simp [cursorTerminal, forcedEq, childrenEq] at terminal
      | true =>
          simp [CanonicalRerootCursor.children, forcedEq] at childrenEq

theorem denseRankedCursorChildren_eq_replicate_of_terminal (mol : RawMolecule)
    (rankFuel : ℕ) (cursor : CanonicalRerootCursor)
    (terminal : cursorTerminal mol cursor = true) :
    denseRankedCursorChildren mol rankFuel cursor =
      List.replicate RawMolecule.authoritativeChildSlots (densePhantomCursor mol cursor.node.atom
        (cursor.node.rule1bRootDistance + 1)) := by
  have childrenNil := cursor_children_eq_nil_of_terminal mol cursor terminal
  simp [denseRankedCursorChildren, densePhantomCursor, childrenNil, sortCursorsTotal]

@[simp] theorem denseRankedCursorChildren_phantom (mol : RawMolecule)
    (rankFuel parent distance : ℕ) :
    denseRankedCursorChildren mol rankFuel (densePhantomCursor mol parent distance) =
      List.replicate RawMolecule.authoritativeChildSlots
        (densePhantomCursor mol mol.atomCount (distance + 1)) := by
  simp [denseRankedCursorChildren, densePhantomCursor,
    RawMolecule.canonicalPhantom,
    CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf,
    CanonicalBranchNode.rule1bRootDistance, sortCursorsTotal]

theorem compareCanonicalNodeRuleAuthoritative?_success_eq_total (mol : RawMolecule)
    (rule : CanonicalRuleStage) (left right : CanonicalBranchNode)
    (decision : Ordering)
    (computed : mol.compareCanonicalNodeRuleAuthoritative? rule left right = some decision) :
    compareCanonicalNodeRuleTotal mol rule left right = decision := by
  cases rule with
  | rule1b => simpa [RawMolecule.compareCanonicalNodeRuleAuthoritative?,
      compareCanonicalNodeRuleTotal] using computed
  | rule2 => simpa [RawMolecule.compareCanonicalNodeRuleAuthoritative?,
      compareCanonicalNodeRuleTotal] using computed
  | rule1a =>
      simp only [RawMolecule.compareCanonicalNodeRuleAuthoritative?] at computed
      cases leftEq : mol.canonicalRule1aLabelAuthoritative? left with
      | none => simp [leftEq] at computed
      | some leftLabel =>
          cases rightEq : mol.canonicalRule1aLabelAuthoritative? right with
          | none => simp [leftEq, rightEq] at computed
          | some rightLabel =>
              have leftTotal : authoritativeRule1aLabelTotal mol left = leftLabel := by
                simp [authoritativeRule1aLabelTotal, leftEq]
              have rightTotal : authoritativeRule1aLabelTotal mol right = rightLabel := by
                simp [authoritativeRule1aLabelTotal, rightEq]
              simpa [leftEq, rightEq, compareCanonicalNodeRuleTotal,
                leftTotal, rightTotal] using computed

theorem compareCursorPairLabelsAuthoritative?_success_factors (mol : RawMolecule)
    (rule : CanonicalRuleStage) :
    ∀ pairs decision,
      compareCursorPairLabelsAuthoritative? mol rule pairs = some decision →
      List.compareLex
          (fun left right => compareCanonicalNodeRuleTotal mol rule left.node right.node)
          (pairs.map Prod.fst) (pairs.map Prod.snd) = decision
  | [], decision, computed => by
      simp [compareCursorPairLabelsAuthoritative?] at computed
      subst decision
      rfl
  | pair :: pairs, decision, computed => by
      simp only [compareCursorPairLabelsAuthoritative?] at computed
      cases nodeEq : mol.compareCanonicalNodeRuleAuthoritative? rule pair.1.node pair.2.node with
      | none => simp [nodeEq] at computed
      | some nodeDecision =>
          have totalEq := compareCanonicalNodeRuleAuthoritative?_success_eq_total mol rule
            pair.1.node pair.2.node nodeDecision nodeEq
          cases nodeDecision with
          | lt =>
              simp [nodeEq] at computed
              subst decision
              simp [List.compareLex, totalEq]
          | gt =>
              simp [nodeEq] at computed
              subst decision
              simp [List.compareLex, totalEq]
          | eq =>
              have tail := compareCursorPairLabelsAuthoritative?_success_factors mol rule pairs decision
                (by simpa [nodeEq] using computed)
              simpa [List.compareLex, totalEq] using tail

abbrev DenseCursorPair := CanonicalRerootCursor × CanonicalRerootCursor

def compareDenseCursorPairLabels (mol : RawMolecule) (rule : CanonicalRuleStage)
    (pairs : List DenseCursorPair) : Ordering :=
  List.compareLex
    (fun left right => compareCanonicalNodeRuleTotal mol rule left.node right.node)
    (pairs.map Prod.fst) (pairs.map Prod.snd)

def denseNextCursorPairs (mol : RawMolecule) (rankFuel : ℕ)
    (pairs : List DenseCursorPair) : List DenseCursorPair :=
  pairs.flatMap fun pair =>
    (denseRankedCursorChildren mol rankFuel pair.1).zip
      (denseRankedCursorChildren mol rankFuel pair.2)

def compareDenseCursorRule (mol : RawMolecule) (rankFuel : ℕ)
    (rule : CanonicalRuleStage) : ℕ → List DenseCursorPair → Ordering
  | 0, pairs => compareDenseCursorPairLabels mol rule pairs
  | depth + 1, pairs =>
      match compareDenseCursorPairLabels mol rule pairs with
      | .eq => compareDenseCursorRule mol rankFuel rule depth
          (denseNextCursorPairs mol rankFuel pairs)
      | decision => decision

@[simp] theorem denseRankedCursorChildren_length (mol : RawMolecule) (fuel : ℕ)
    (cursor : CanonicalRerootCursor) :
    (denseRankedCursorChildren mol fuel cursor).length =
      RawMolecule.authoritativeChildSlots := by
  simp [denseRankedCursorChildren]

theorem denseNextCursorPairs_map_fst (mol : RawMolecule) (fuel : ℕ) : ∀ pairs,
    (denseNextCursorPairs mol fuel pairs).map Prod.fst =
      denseNextCursorFrontier mol fuel (pairs.map Prod.fst)
  | [] => rfl
  | pair :: pairs => by
      simp only [denseNextCursorPairs, List.flatMap_cons, List.map_append,
        denseNextCursorFrontier, List.map_cons, List.flatMap_cons]
      rw [List.map_fst_zip (by simp)]
      congr 1
      simpa [denseNextCursorPairs, denseNextCursorFrontier] using
        denseNextCursorPairs_map_fst mol fuel pairs

theorem denseNextCursorPairs_map_snd (mol : RawMolecule) (fuel : ℕ) : ∀ pairs,
    (denseNextCursorPairs mol fuel pairs).map Prod.snd =
      denseNextCursorFrontier mol fuel (pairs.map Prod.snd)
  | [] => rfl
  | pair :: pairs => by
      simp only [denseNextCursorPairs, List.flatMap_cons, List.map_append,
        denseNextCursorFrontier, List.map_cons, List.flatMap_cons]
      rw [List.map_snd_zip (by simp)]
      congr 1
      simpa [denseNextCursorPairs, denseNextCursorFrontier] using
        denseNextCursorPairs_map_snd mol fuel pairs

theorem compareLex_append_of_length_eq {alpha : Type*}
    (cmp : alpha → alpha → Ordering) : ∀ left right leftTail rightTail,
    left.length = right.length →
    List.compareLex cmp (left ++ leftTail) (right ++ rightTail) =
      (List.compareLex cmp left right).then
        (List.compareLex cmp leftTail rightTail)
  | [], [], leftTail, rightTail, _ => rfl
  | leftHead :: left, rightHead :: right, leftTail, rightTail, lengths => by
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp only [List.cons_append, List.compareLex]
      cases headEq : cmp leftHead rightHead with
      | lt => simp
      | gt => simp
      | eq =>
          simpa [headEq] using
            compareLex_append_of_length_eq cmp left right leftTail rightTail lengths

theorem compareDenseCursorRule_eq_frontiers (mol : RawMolecule) (rankFuel : ℕ)
    (rule : CanonicalRuleStage) : ∀ depth pairs,
    compareDenseCursorRule mol rankFuel rule depth pairs =
      List.compareLex
        (fun left right => compareCanonicalNodeRuleTotal mol rule left.node right.node)
        (denseCursorFrontiers mol rankFuel depth (pairs.map Prod.fst)).flatten
        (denseCursorFrontiers mol rankFuel depth (pairs.map Prod.snd)).flatten
  | 0, pairs => by
      simp [compareDenseCursorRule, compareDenseCursorPairLabels,
        denseCursorFrontiers]
  | depth + 1, pairs => by
      let cmp := fun left right : CanonicalRerootCursor =>
        compareCanonicalNodeRuleTotal mol rule left.node right.node
      have prefixLength : (pairs.map Prod.fst).length = (pairs.map Prod.snd).length := by simp
      have appendRule := compareLex_append_of_length_eq cmp
        (pairs.map Prod.fst) (pairs.map Prod.snd)
        (denseCursorFrontiers mol rankFuel depth
          (denseNextCursorFrontier mol rankFuel (pairs.map Prod.fst))).flatten
        (denseCursorFrontiers mol rankFuel depth
          (denseNextCursorFrontier mol rankFuel (pairs.map Prod.snd))).flatten prefixLength
      have tail := compareDenseCursorRule_eq_frontiers mol rankFuel rule depth
        (denseNextCursorPairs mol rankFuel pairs)
      rw [denseNextCursorPairs_map_fst, denseNextCursorPairs_map_snd] at tail
      simp only [compareDenseCursorRule, denseCursorFrontiers, List.flatten_cons]
      rw [appendRule]
      rw [tail]
      unfold compareDenseCursorPairLabels
      cases current : List.compareLex cmp (List.map Prod.fst pairs) (List.map Prod.snd pairs) <;>
        simp [cmp]

/-- `active` is the production frontier and `dense` is its full virtual frontier.  The latter may
contain only terminal tied pairs that production legitimately drops. -/
def CursorPairSilent (mol : RawMolecule) (rule : CanonicalRuleStage)
    (pair : DenseCursorPair) : Prop :=
  cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true ∧
    compareCanonicalNodeRuleTotal mol rule pair.1.node pair.2.node = .eq

inductive ErasesSilentCursorPairs (mol : RawMolecule) (rule : CanonicalRuleStage) :
    List DenseCursorPair → List DenseCursorPair → Prop
  | nil : ErasesSilentCursorPairs mol rule [] []
  | keep (pair : DenseCursorPair) {active dense : List DenseCursorPair}
      (tail : ErasesSilentCursorPairs mol rule active dense) :
      ErasesSilentCursorPairs mol rule (pair :: active) (pair :: dense)
  | erase (pair : DenseCursorPair) {active dense : List DenseCursorPair}
      (silent : CursorPairSilent mol rule pair)
      (tail : ErasesSilentCursorPairs mol rule active dense) :
      ErasesSilentCursorPairs mol rule active (pair :: dense)

theorem ErasesSilentCursorPairs.labels_eq
    {mol : RawMolecule} {rule : CanonicalRuleStage} {active dense : List DenseCursorPair}
    (related : ErasesSilentCursorPairs mol rule active dense) :
    compareDenseCursorPairLabels mol rule active =
      compareDenseCursorPairLabels mol rule dense := by
  induction related with
  | nil => rfl
  | keep pair tail ih =>
      unfold compareDenseCursorPairLabels at ih ⊢
      simp only [List.map_cons, List.compareLex]
      cases compareCanonicalNodeRuleTotal mol rule pair.1.node pair.2.node <;> simp [ih]
  | erase pair silent tail ih =>
      unfold compareDenseCursorPairLabels at ih ⊢
      rcases silent with ⟨_, _, tied⟩
      simp [List.compareLex, tied, ih]

theorem ErasesSilentCursorPairs.erase_all
    {mol : RawMolecule} {rule : CanonicalRuleStage}
    (silentPairs : List DenseCursorPair) {active dense : List DenseCursorPair}
    (allSilent : ∀ pair, pair ∈ silentPairs → CursorPairSilent mol rule pair)
    (tail : ErasesSilentCursorPairs mol rule active dense) :
    ErasesSilentCursorPairs mol rule active (silentPairs ++ dense) := by
  induction silentPairs with
  | nil => simpa using tail
  | cons pair pairs ih =>
      exact .erase pair (allSilent pair (by simp))
        (ih (fun candidate member => allSilent candidate (by simp [member])))

theorem node_rule1b_eq_implies_distance_eq (mol : RawMolecule)
    (left right : CanonicalBranchNode)
    (tied : mol.compareCanonicalNodeRule .rule1b left right = .eq) :
    left.rule1bRootDistance = right.rule1bRootDistance := by
  simp only [RawMolecule.compareCanonicalNodeRule] at tied
  by_cases leftRight : left.rule1bRootDistance < right.rule1bRootDistance
  · simp [leftRight] at tied
  · by_cases rightLeft : right.rule1bRootDistance < left.rule1bRootDistance
    · simp [leftRight, rightLeft] at tied
    · simp [leftRight, rightLeft] at tied
      omega

theorem dense_silent_pair_children_silent (mol : RawMolecule) (fuel : ℕ)
    (rule : CanonicalRuleStage) (pair : DenseCursorPair)
    (silent : CursorPairSilent mol rule pair) :
    ∀ child, child ∈ denseNextCursorPairs mol fuel [pair] →
      CursorPairSilent mol rule child := by
  rcases silent with ⟨leftTerminal, rightTerminal, tied⟩
  have leftChildren := denseRankedCursorChildren_eq_replicate_of_terminal
    mol fuel pair.1 leftTerminal
  have rightChildren := denseRankedCursorChildren_eq_replicate_of_terminal
    mol fuel pair.2 rightTerminal
  intro child member
  simp only [denseNextCursorPairs, List.flatMap_singleton, leftChildren, rightChildren] at member
  simp at member
  rcases member with ⟨_, rfl⟩
  cases rule with
  | rule1a =>
      simp [CursorPairSilent, densePhantomCursor, RawMolecule.canonicalPhantom,
        cursorTerminal, CanonicalRerootCursor.children,
        CanonicalBranchNode.forcedLeaf,
        compareCanonicalNodeRuleTotal, authoritativeRule1aLabelTotal,
        RawMolecule.canonicalRule1aLabelAuthoritative?]
  | rule2 =>
      simp [CursorPairSilent, densePhantomCursor, RawMolecule.canonicalPhantom,
        cursorTerminal, CanonicalRerootCursor.children,
        CanonicalBranchNode.forcedLeaf, compareCanonicalNodeRuleTotal,
        RawMolecule.compareCanonicalNodeRule]
  | rule1b =>
      have distanceEq := node_rule1b_eq_implies_distance_eq mol pair.1.node pair.2.node tied
      constructor
      · simp [cursorTerminal, densePhantomCursor, RawMolecule.canonicalPhantom,
          CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf]
      · constructor
        · simp [cursorTerminal, densePhantomCursor, RawMolecule.canonicalPhantom,
            CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf]
        · change compareDenseRule1b (pair.1.node.rule1bRootDistance + 1)
              (pair.2.node.rule1bRootDistance + 1) = .eq
          rw [distanceEq]
          simp [compareDenseRule1b]

theorem compareCursorPairLabelsAuthoritative?_eq_implies_all_tied (mol : RawMolecule)
    (rule : CanonicalRuleStage) : ∀ pairs,
    compareCursorPairLabelsAuthoritative? mol rule pairs = some .eq →
      ∀ pair, pair ∈ pairs →
        compareCanonicalNodeRuleTotal mol rule pair.1.node pair.2.node = .eq
  | [], _, pair, member => by simp at member
  | head :: tail, computed, pair, member => by
      simp only [compareCursorPairLabelsAuthoritative?] at computed
      cases headEq : mol.compareCanonicalNodeRuleAuthoritative? rule
          head.1.node head.2.node with
      | none => simp [headEq] at computed
      | some decision =>
          have headTotal := compareCanonicalNodeRuleAuthoritative?_success_eq_total mol rule
            head.1.node head.2.node decision headEq
          cases decision with
          | lt => simp [headEq] at computed
          | gt => simp [headEq] at computed
          | eq =>
              rcases List.mem_cons.mp member with rfl | tailMember
              · exact headTotal
              · exact compareCursorPairLabelsAuthoritative?_eq_implies_all_tied mol rule tail
                  (by simpa [headEq] using computed) pair tailMember

theorem ErasesSilentCursorPairs.keep_all
    {mol : RawMolecule} {rule : CanonicalRuleStage}
    (initial : List DenseCursorPair) {active dense : List DenseCursorPair}
    (tail : ErasesSilentCursorPairs mol rule active dense) :
    ErasesSilentCursorPairs mol rule (initial ++ active) (initial ++ dense) := by
  induction initial with
  | nil => simpa using tail
  | cons pair pairs ih => exact .keep pair ih

theorem nextCursorPairs_dense_related (mol : RawMolecule) (rankFuel : ℕ)
    (rule : CanonicalRuleStage) {active dense next : List DenseCursorPair}
    (related : ErasesSilentCursorPairs mol rule active dense)
    (allTied : ∀ pair, pair ∈ active →
      compareCanonicalNodeRuleTotal mol rule pair.1.node pair.2.node = .eq)
    (computed : nextCursorPairsAuthoritative? mol (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) active =
      some next) :
    ErasesSilentCursorPairs mol rule next (denseNextCursorPairs mol rankFuel dense) := by
  induction related generalizing next with
  | nil =>
      simp [nextCursorPairsAuthoritative?] at computed
      subst next
      exact .nil
  | erase pair silent tail ih =>
      have tailRelated := ih allTied computed
      simpa [denseNextCursorPairs] using ErasesSilentCursorPairs.erase_all
        (denseNextCursorPairs mol rankFuel [pair])
        (dense_silent_pair_children_silent mol rankFuel rule pair silent)
        tailRelated
  | keep pair relatedTail ih =>
      rename_i activeTail denseTail
      have pairTied := allTied pair (by simp)
      have tailTied : ∀ candidate, candidate ∈ activeTail →
          compareCanonicalNodeRuleTotal mol rule candidate.1.node candidate.2.node = .eq := by
        intro candidate member
        exact allTied candidate (by simp [member])
      simp only [nextCursorPairsAuthoritative?] at computed
      cases restEq : nextCursorPairsAuthoritative? mol
          (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) activeTail with
      | none => simp [restEq] at computed
      | some rest =>
          have restRelated := ih tailTied restEq
          cases leftTerminal : cursorTerminal mol pair.1 <;>
            cases rightTerminal : cursorTerminal mol pair.2
          · cases leftEq : rankedCursorChildrenAuthoritative? mol
                (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildrenAuthoritative? mol
                    (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseRankedCursorChildren_eq_of_success mol rankFuel
                      pair.1 left leftEq
                    have denseRight := denseRankedCursorChildren_eq_of_success mol rankFuel
                      pair.2 right rightEq
                    simp only [denseNextCursorPairs, List.flatMap_cons,
                      denseLeft, denseRight]
                    exact ErasesSilentCursorPairs.keep_all (left.zip right) restRelated
          · cases leftEq : rankedCursorChildrenAuthoritative? mol
                (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildrenAuthoritative? mol
                    (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseRankedCursorChildren_eq_of_success mol rankFuel
                      pair.1 left leftEq
                    have denseRight := denseRankedCursorChildren_eq_of_success mol rankFuel
                      pair.2 right rightEq
                    simp only [denseNextCursorPairs, List.flatMap_cons,
                      denseLeft, denseRight]
                    exact ErasesSilentCursorPairs.keep_all (left.zip right) restRelated
          · cases leftEq : rankedCursorChildrenAuthoritative? mol
                (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) pair.1 with
            | none => simp [restEq, leftTerminal, rightTerminal, leftEq] at computed
            | some left =>
                cases rightEq : rankedCursorChildrenAuthoritative? mol
                    (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) pair.2 with
                | none => simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                | some right =>
                    simp [restEq, leftTerminal, rightTerminal, leftEq, rightEq] at computed
                    subst next
                    have denseLeft := denseRankedCursorChildren_eq_of_success mol rankFuel
                      pair.1 left leftEq
                    have denseRight := denseRankedCursorChildren_eq_of_success mol rankFuel
                      pair.2 right rightEq
                    simp only [denseNextCursorPairs, List.flatMap_cons,
                      denseLeft, denseRight]
                    exact ErasesSilentCursorPairs.keep_all (left.zip right) restRelated
          · simp [restEq, leftTerminal, rightTerminal] at computed
            subst next
            have silentPair : CursorPairSilent mol rule pair :=
              ⟨leftTerminal, rightTerminal, pairTied⟩
            simpa [denseNextCursorPairs] using ErasesSilentCursorPairs.erase_all
              (denseNextCursorPairs mol rankFuel [pair])
              (dense_silent_pair_children_silent mol rankFuel rule pair silentPair)
              restRelated

theorem ErasesSilentCursorPairs.refl
    {mol : RawMolecule} {rule : CanonicalRuleStage} : ∀ pairs,
    ErasesSilentCursorPairs mol rule pairs pairs
  | [] => .nil
  | pair :: pairs => .keep pair (ErasesSilentCursorPairs.refl pairs)

theorem ErasesSilentCursorPairs.empty_dense_rule_eq (mol : RawMolecule)
    (rankFuel : ℕ) (rule : CanonicalRuleStage) : ∀ depth {dense},
    ErasesSilentCursorPairs mol rule [] dense →
      compareDenseCursorRule mol rankFuel rule depth dense = .eq
  | 0, dense, related => by
      have labels := related.labels_eq
      simpa [compareDenseCursorRule, compareDenseCursorPairLabels] using labels.symm
  | depth + 1, dense, related => by
      have labels := related.labels_eq
      have current : compareDenseCursorPairLabels mol rule dense = .eq := by
        simpa [compareDenseCursorPairLabels] using labels.symm
      have nextRelated : ErasesSilentCursorPairs mol rule []
          (denseNextCursorPairs mol rankFuel dense) :=
        nextCursorPairs_dense_related mol rankFuel rule related
          (by intro pair member; simp at member)
          (by rfl)
      simp only [compareDenseCursorRule, current]
      exact ErasesSilentCursorPairs.empty_dense_rule_eq mol rankFuel rule depth nextRelated

/-- Every successful optional production rule walk equals the corresponding total dense walk. -/
theorem compareCursorRuleAuthoritative?_success_dense (mol : RawMolecule) (rankFuel : ℕ)
    (rule : CanonicalRuleStage) : ∀ depth active dense decision,
    ErasesSilentCursorPairs mol rule active dense →
    compareCursorRuleAuthoritative? mol (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) rule depth active =
      some decision →
    compareDenseCursorRule mol rankFuel rule depth dense = decision
  | 0, active, dense, decision, related, computed => by
      simp only [compareCursorRuleAuthoritative?] at computed
      cases labelsEq : compareCursorPairLabelsAuthoritative? mol rule active with
      | none => simp [labelsEq] at computed
      | some current =>
          have activeTotal : compareDenseCursorPairLabels mol rule active = current :=
            compareCursorPairLabelsAuthoritative?_success_factors mol rule active current labelsEq
          have denseTotal : compareDenseCursorPairLabels mol rule dense = current := by
            rw [← related.labels_eq]
            exact activeTotal
          cases current with
          | lt => simpa [labelsEq, compareDenseCursorRule, denseTotal] using computed
          | gt => simpa [labelsEq, compareDenseCursorRule, denseTotal] using computed
          | eq =>
              cases nextEq : nextCursorPairsAuthoritative? mol
                  (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) active with
              | none => simp [labelsEq, nextEq] at computed
              | some next =>
                  cases next with
                  | nil => simpa [labelsEq, nextEq, compareDenseCursorRule, denseTotal]
                      using computed
                  | cons head tail => simp [labelsEq, nextEq] at computed
  | depth + 1, active, dense, decision, related, computed => by
      simp only [compareCursorRuleAuthoritative?] at computed
      cases labelsEq : compareCursorPairLabelsAuthoritative? mol rule active with
      | none => simp [labelsEq] at computed
      | some current =>
          have activeTotal : compareDenseCursorPairLabels mol rule active = current :=
            compareCursorPairLabelsAuthoritative?_success_factors mol rule active current labelsEq
          have denseTotal : compareDenseCursorPairLabels mol rule dense = current := by
            rw [← related.labels_eq]
            exact activeTotal
          cases current with
          | lt => simpa [labelsEq, compareDenseCursorRule, denseTotal] using computed
          | gt => simpa [labelsEq, compareDenseCursorRule, denseTotal] using computed
          | eq =>
              have allTied := compareCursorPairLabelsAuthoritative?_eq_implies_all_tied mol rule active labelsEq
              cases nextEq : nextCursorPairsAuthoritative? mol
                  (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) active with
              | none => simp [labelsEq, nextEq] at computed
              | some next =>
                  have nextRelated := nextCursorPairs_dense_related mol rankFuel rule related
                    allTied nextEq
                  cases next with
                  | nil =>
                      have tailEq := nextRelated.empty_dense_rule_eq mol rankFuel rule depth
                      simpa [labelsEq, nextEq, compareDenseCursorRule, denseTotal, tailEq]
                        using computed
                  | cons head tail =>
                      have tailFactor := compareCursorRuleAuthoritative?_success_dense mol rankFuel rule depth
                        (head :: tail) (denseNextCursorPairs mol rankFuel dense) decision
                        nextRelated (by simpa [labelsEq, nextEq] using computed)
                      simpa [compareDenseCursorRule, denseTotal] using tailFactor

def compareDenseRerootKeyRule (rule : CanonicalRuleStage)
    (left right : DenseRerootKey) : Ordering :=
  match rule with
  | .rule1a => List.compareLex compareCIPAtomicLabel left.rule1a right.rule1a
  | .rule1b => List.compareLex compareDenseRule1b left.rule1b right.rule1b
  | .rule2 => List.compareLex compare left.rule2 right.rule2

theorem listCompareLex_map {alpha beta : Type*}
    (mapValue : alpha → beta) (compareSource : alpha → alpha → Ordering)
    (compareTarget : beta → beta → Ordering)
    (hcompare : ∀ left right,
      compareTarget (mapValue left) (mapValue right) = compareSource left right) :
    ∀ left right,
      List.compareLex compareTarget (left.map mapValue) (right.map mapValue) =
        List.compareLex compareSource left right := by
  intro left
  induction left with
  | nil => intro right; cases right <;> rfl
  | cons head tail ih =>
      intro right
      cases right with
      | nil => rfl
      | cons other others =>
          simp only [List.map_cons, List.compareLex]
          rw [hcompare]
          cases compareSource head other <;> simp [ih]

/-- Successful traversal of one production rule is comparison of one dense-key field. -/
theorem compareCursorRuleAuthoritative?_singleton_success_dense_key_rule (mol : RawMolecule)
    (rankFuel : ℕ) (rule : CanonicalRuleStage)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : compareCursorRuleAuthoritative? mol (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) rule
      (rankFuel + 1) [(left, right)] = some decision) :
    compareDenseRerootKeyRule rule (buildDenseRerootKey mol (rankFuel + 1) left)
      (buildDenseRerootKey mol (rankFuel + 1) right) = decision := by
  have factor := compareCursorRuleAuthoritative?_success_dense mol rankFuel rule (rankFuel + 1)
    [(left, right)] [(left, right)] decision (ErasesSilentCursorPairs.refl _) computed
  rw [compareDenseCursorRule_eq_frontiers] at factor
  cases rule with
  | rule1a =>
      simp only [compareDenseRerootKeyRule, buildDenseRerootKey]
      rw [listCompareLex_map _ _ _ (by intro cursorLeft cursorRight; rfl)]
      simpa [compareCanonicalNodeRuleTotal] using factor
  | rule1b =>
      simp only [compareDenseRerootKeyRule, buildDenseRerootKey]
      rw [listCompareLex_map _ _ _ (by intro cursorLeft cursorRight; rfl)]
      simpa [compareCanonicalNodeRuleTotal, RawMolecule.compareCanonicalNodeRule,
        compareDenseRule1b] using factor
  | rule2 =>
      simp only [compareDenseRerootKeyRule, buildDenseRerootKey]
      rw [listCompareLex_map _ _ _ (by intro cursorLeft cursorRight; rfl)]
      simpa [compareCanonicalNodeRuleTotal, RawMolecule.compareCanonicalNodeRule,
        cursorRule2Mass] using factor

/-- Assumption-free unary factorization of the raw production Rule-2 branch comparator.  Every
successful result is comparison of two keys compiled independently from its cursor operands. -/
theorem compareCursorBranchAtAuthoritative?_success_dense_factors (mol : RawMolecule) :
    ∀ fuel (left right : CanonicalRerootCursor) (decision : Ordering),
    compareCursorBranchAtAuthoritative? mol fuel .rule2 left right = some decision →
      compareDenseRerootKeys (buildDenseRerootKey mol fuel left)
        (buildDenseRerootKey mol fuel right) = decision
  | 0, left, right, decision, computed => by
      simp only [compareCursorBranchAtAuthoritative?,
        RawMolecule.compareCanonicalNodeThroughAuthoritative?,
        RawMolecule.compareCanonicalNodeRuleAuthoritative?] at computed
      simp only [buildDenseRerootKey, compareDenseRerootKeys, List.compareLex,
        compareLex, Ordering.byKey]
      cases leftLabelEq : mol.canonicalRule1aLabelAuthoritative? left.node with
      | none => simp [leftLabelEq] at computed
      | some leftLabel =>
          cases rightLabelEq : mol.canonicalRule1aLabelAuthoritative? right.node with
          | none => simp [leftLabelEq, rightLabelEq] at computed
          | some rightLabel =>
              have leftTotal : authoritativeRule1aLabelTotal mol left.node = leftLabel := by
                simp [authoritativeRule1aLabelTotal, leftLabelEq]
              have rightTotal : authoritativeRule1aLabelTotal mol right.node = rightLabel := by
                simp [authoritativeRule1aLabelTotal, rightLabelEq]
              rw [leftTotal, rightTotal]
              cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel with
              | lt => simpa [leftLabelEq, rightLabelEq, rule1aEq] using computed
              | gt => simpa [leftLabelEq, rightLabelEq, rule1aEq] using computed
              | eq =>
                  simp [leftLabelEq, rightLabelEq, rule1aEq,
                    RawMolecule.compareCanonicalNodeRule] at computed
                  change
                    (match compareDenseRule1b left.node.rule1bRootDistance
                        right.node.rule1bRootDistance with
                      | .eq => some (compare (cursorRule2Mass mol left)
                          (cursorRule2Mass mol right))
                      | result => some result) = some decision at computed
                  cases rule1bEq : compareDenseRule1b left.node.rule1bRootDistance
                      right.node.rule1bRootDistance with
                  | lt => simpa [rule1bEq] using computed
                  | gt => simpa [rule1bEq] using computed
                  | eq =>
                      cases massEq : compare (cursorRule2Mass mol left)
                          (cursorRule2Mass mol right) with
                      | lt => simpa [rule1bEq, massEq] using computed
                      | eq => simpa [rule1bEq, massEq] using computed
                      | gt => simpa [rule1bEq, massEq] using computed
  | rankFuel + 1, left, right, decision, computed => by
      simp only [compareCursorBranchAtAuthoritative?] at computed
      cases rule1aEq : compareCursorRuleAuthoritative? mol
          (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) .rule1a (rankFuel + 1)
          [(left, right)] with
      | none => simp [rule1aEq] at computed
      | some rule1aDecision =>
          have rule1aFactor := compareCursorRuleAuthoritative?_singleton_success_dense_key_rule mol
            rankFuel .rule1a left right rule1aDecision rule1aEq
          have rule1aField : List.compareLex compareCIPAtomicLabel
              (buildDenseRerootKey mol (rankFuel + 1) left).rule1a
              (buildDenseRerootKey mol (rankFuel + 1) right).rule1a = rule1aDecision := by
            simpa [compareDenseRerootKeyRule] using rule1aFactor
          cases rule1aDecision with
          | lt =>
              simp [rule1aEq] at computed
              subst decision
              simp [compareDenseRerootKeys, compareLex, Ordering.byKey, rule1aField]
          | gt =>
              simp [rule1aEq] at computed
              subst decision
              simp [compareDenseRerootKeys, compareLex, Ordering.byKey, rule1aField]
          | eq =>
              cases rule1bEq : compareCursorRuleAuthoritative? mol
                  (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) .rule1b (rankFuel + 1)
                  [(left, right)] with
              | none => simp [rule1aEq, rule1bEq] at computed
              | some rule1bDecision =>
                  have rule1bFactor := compareCursorRuleAuthoritative?_singleton_success_dense_key_rule mol
                    rankFuel .rule1b left right rule1bDecision rule1bEq
                  have rule1bField : List.compareLex compareDenseRule1b
                      (buildDenseRerootKey mol (rankFuel + 1) left).rule1b
                      (buildDenseRerootKey mol (rankFuel + 1) right).rule1b =
                        rule1bDecision := by
                    simpa [compareDenseRerootKeyRule] using rule1bFactor
                  cases rule1bDecision with
                  | lt =>
                      simp [rule1aEq, rule1bEq] at computed
                      subst decision
                      simp [compareDenseRerootKeys, compareLex, Ordering.byKey,
                        rule1aField, rule1bField]
                  | gt =>
                      simp [rule1aEq, rule1bEq] at computed
                      subst decision
                      simp [compareDenseRerootKeys, compareLex, Ordering.byKey,
                        rule1aField, rule1bField]
                  | eq =>
                      cases rule2Eq : compareCursorRuleAuthoritative? mol
                          (compareCursorBranchAtAuthoritative? mol rankFuel .rule2) .rule2 (rankFuel + 1)
                          [(left, right)] with
                      | none => simp [rule1aEq, rule1bEq, rule2Eq] at computed
                      | some rule2Decision =>
                          have rule2Factor :=
                            compareCursorRuleAuthoritative?_singleton_success_dense_key_rule mol rankFuel
                              .rule2 left right rule2Decision rule2Eq
                          have rule2Field : List.compareLex compare
                              (buildDenseRerootKey mol (rankFuel + 1) left).rule2
                              (buildDenseRerootKey mol (rankFuel + 1) right).rule2 =
                                rule2Decision := by
                            simpa [compareDenseRerootKeyRule] using rule2Factor
                          simp [rule1aEq, rule1bEq, rule2Eq] at computed
                          subst decision
                          simpa [compareDenseRerootKeys, compareLex, Ordering.byKey,
                            rule1aField, rule1bField] using rule2Field

/-! ## A structural completeness class -/

/-- The production constitutional comparator is total on a pair of terminal cursors whose two
Rule-1a root labels are supported.

This is a genuine completeness theorem, not a factorization of an assumed successful call.
Terminality makes every child sphere empty, so sibling sorting, frontier capacity, and recursive
fuel cannot refuse; the two label witnesses remove the only remaining optional root lookup. -/
theorem compareCursorBranchAtAuthoritative?_terminal_supported_exists (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (leftTerminal : cursorTerminal mol left = true)
    (rightTerminal : cursorTerminal mol right = true)
    (leftLabel : ∃ label, mol.canonicalRule1aLabelAuthoritative? left.node = some label)
    (rightLabel : ∃ label, mol.canonicalRule1aLabelAuthoritative? right.node = some label) :
    ∃ ordering, compareCursorBranchAtAuthoritative? mol fuel .rule2 left right = some ordering := by
  rcases leftLabel with ⟨leftLabel, leftLabelEq⟩
  rcases rightLabel with ⟨rightLabel, rightLabelEq⟩
  cases fuel with
  | zero =>
      simp only [compareCursorBranchAtAuthoritative?,
        RawMolecule.compareCanonicalNodeThroughAuthoritative?,
        RawMolecule.compareCanonicalNodeRuleAuthoritative?, leftLabelEq, rightLabelEq]
      cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel <;> simp [rule1aEq]
      cases rule1bEq : mol.compareCanonicalNodeRule .rule1b left.node right.node <;>
        simp
  | succ fuel =>
      simp only [compareCursorBranchAtAuthoritative?]
      have leftChildren := cursor_children_eq_nil_of_terminal mol left leftTerminal
      have rightChildren := cursor_children_eq_nil_of_terminal mol right rightTerminal
      cases rule1aEq : compareCIPAtomicLabel leftLabel rightLabel <;>
        cases rule1bEq : mol.compareCanonicalNodeRule .rule1b left.node right.node <;>
        cases rule2Eq : mol.compareCanonicalNodeRule .rule2 left.node right.node <;>
        simp [compareCursorRuleAuthoritative?, compareCursorPairLabelsAuthoritative?, nextCursorPairsAuthoritative?, cursorTerminal,
          leftChildren, rightChildren, leftLabelEq, rightLabelEq,
          RawMolecule.compareCanonicalNodeRuleAuthoritative?,
          rule1aEq, rule1bEq, rule2Eq]

/-- Honest transitivity law for the partial raw comparator: if all three comparisons succeed,
two weakly increasing results force the third result to be weakly increasing.  This is not a
totality or success theorem for the optional comparator. -/
theorem compareCursorBranchAtAuthoritative?_success_isLE_trans (mol : RawMolecule) (fuel : ℕ)
    (left middle right : CanonicalRerootCursor)
    (leftMiddle middleRight leftRight : Ordering)
    (leftMiddleComputed :
      compareCursorBranchAtAuthoritative? mol fuel .rule2 left middle = some leftMiddle)
    (middleRightComputed :
      compareCursorBranchAtAuthoritative? mol fuel .rule2 middle right = some middleRight)
    (leftRightComputed :
      compareCursorBranchAtAuthoritative? mol fuel .rule2 left right = some leftRight)
    (leftMiddleLE : leftMiddle.isLE = true)
    (middleRightLE : middleRight.isLE = true) :
    leftRight.isLE = true := by
  let leftKey := buildDenseRerootKey mol fuel left
  let middleKey := buildDenseRerootKey mol fuel middle
  let rightKey := buildDenseRerootKey mol fuel right
  have leftMiddleFactor : compareDenseRerootKeys leftKey middleKey = leftMiddle :=
    compareCursorBranchAtAuthoritative?_success_dense_factors mol fuel left middle leftMiddle
      leftMiddleComputed
  have middleRightFactor : compareDenseRerootKeys middleKey rightKey = middleRight :=
    compareCursorBranchAtAuthoritative?_success_dense_factors mol fuel middle right middleRight
      middleRightComputed
  have leftRightFactor : compareDenseRerootKeys leftKey rightKey = leftRight :=
    compareCursorBranchAtAuthoritative?_success_dense_factors mol fuel left right leftRight
      leftRightComputed
  letI : Std.TransCmp compareDenseRerootKeys := compareDenseRerootKeys_transCmp
  have denseLeftMiddleLE : (compareDenseRerootKeys leftKey middleKey).isLE = true := by
    simpa [leftMiddleFactor] using leftMiddleLE
  have denseMiddleRightLE : (compareDenseRerootKeys middleKey rightKey).isLE = true := by
    simpa [middleRightFactor] using middleRightLE
  have denseLeftRightLE : (compareDenseRerootKeys leftKey rightKey).isLE = true :=
    Std.TransCmp.isLE_trans denseLeftMiddleLE denseMiddleRightLE
  simpa [leftRightFactor] using denseLeftRightLE

/-! ## Conservative fail-closed constitutional boundary -/

/-- Every successful fail-closed constitutional result is the raw Rule-2 result on the same two
reroot cursors. -/
theorem certifiedConstitutionalStageAuthoritative?_success_raw_eq
    (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (decision : Ordering)
    (computed : certifiedConstitutionalStageAuthoritative? mol fuel left right = some decision) :
    compareCursorBranchAtAuthoritative? mol fuel .rule2 left right = some decision := by
  unfold certifiedConstitutionalStageAuthoritative? at computed
  cases rawEq : compareCursorBranchAtAuthoritative? mol fuel .rule2 left right with
  | none => simp [rawEq] at computed
  | some rawDecision =>
      by_cases conflict : occurrenceRootsProvedAutomorphic mol fuel left right rawDecision
      · simp [rawEq, conflict] at computed
      · have decisionEq : rawDecision = decision := by
          simpa [rawEq, conflict] using computed
        exact congrArg some decisionEq

/-- A successful result certifies that the disputed pairwise automorphism override did not fire. -/
theorem certifiedConstitutionalStageAuthoritative?_success_gate_false
    (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (decision : Ordering)
    (computed : certifiedConstitutionalStageAuthoritative? mol fuel left right = some decision) :
    occurrenceRootsProvedAutomorphic mol fuel left right decision = false := by
  unfold certifiedConstitutionalStageAuthoritative? at computed
  cases rawEq : compareCursorBranchAtAuthoritative? mol fuel .rule2 left right with
  | none => simp [rawEq] at computed
  | some rawDecision =>
      by_cases conflict : occurrenceRootsProvedAutomorphic mol fuel left right rawDecision
      · simp [rawEq, conflict] at computed
      · have decisionEq : rawDecision = decision := by
          simpa [rawEq, conflict] using computed
        simpa [decisionEq] using conflict

/-- Every successful result of the actual fail-closed production stage factors through the lawful
dense unary keys of the two actual cursors. -/
theorem certifiedConstitutionalStageAuthoritative?_success_dense_factors
    (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (decision : Ordering)
    (computed : certifiedConstitutionalStageAuthoritative? mol fuel left right = some decision) :
    compareDenseRerootKeys (buildDenseRerootKey mol fuel left)
      (buildDenseRerootKey mol fuel right) = decision := by
  exact compareCursorBranchAtAuthoritative?_success_dense_factors mol fuel left right decision
    (certifiedConstitutionalStageAuthoritative?_success_raw_eq mol fuel left right decision computed)

/-- Honest transitivity law for the partial actual production stage.  It requires success of all
three optional comparisons and claims no endpoint totality. -/
theorem certifiedConstitutionalStageAuthoritative?_success_isLE_trans
    (mol : RawMolecule) (fuel : ℕ)
    (left middle right : CanonicalRerootCursor)
    (leftMiddle middleRight leftRight : Ordering)
    (leftMiddleComputed :
      certifiedConstitutionalStageAuthoritative? mol fuel left middle = some leftMiddle)
    (middleRightComputed :
      certifiedConstitutionalStageAuthoritative? mol fuel middle right = some middleRight)
    (leftRightComputed :
      certifiedConstitutionalStageAuthoritative? mol fuel left right = some leftRight)
    (leftMiddleLE : leftMiddle.isLE = true)
    (middleRightLE : middleRight.isLE = true) :
    leftRight.isLE = true := by
  have leftMiddleFactor := certifiedConstitutionalStageAuthoritative?_success_dense_factors
    mol fuel left middle leftMiddle leftMiddleComputed
  have middleRightFactor := certifiedConstitutionalStageAuthoritative?_success_dense_factors
    mol fuel middle right middleRight middleRightComputed
  have leftRightFactor := certifiedConstitutionalStageAuthoritative?_success_dense_factors
    mol fuel left right leftRight leftRightComputed
  letI : Std.TransCmp compareDenseRerootKeys := compareDenseRerootKeys_transCmp
  have denseLeftMiddleLE :
      (compareDenseRerootKeys (buildDenseRerootKey mol fuel left)
        (buildDenseRerootKey mol fuel middle)).isLE = true := by
    simpa [leftMiddleFactor] using leftMiddleLE
  have denseMiddleRightLE :
      (compareDenseRerootKeys (buildDenseRerootKey mol fuel middle)
        (buildDenseRerootKey mol fuel right)).isLE = true := by
    simpa [middleRightFactor] using middleRightLE
  have denseLeftRightLE :
      (compareDenseRerootKeys (buildDenseRerootKey mol fuel left)
        (buildDenseRerootKey mol fuel right)).isLE = true :=
    Std.TransCmp.isLE_trans denseLeftMiddleLE denseMiddleRightLE
  simpa [leftRightFactor] using denseLeftRightLE

end TetraStereo.OneCenter.AuthoritativeCIPRerootComparatorLaws
