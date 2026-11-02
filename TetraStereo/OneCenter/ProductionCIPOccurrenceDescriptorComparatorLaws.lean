import TetraStereo.OneCenter.ProductionCIPRerootComparatorLaws

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws

open RawMolecule

/-! A callback-parametric dense compiler for occurrence descriptor spheres.  The callback is
totalized only outside successful production traces. -/

def totalizedDecision
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (left right : CanonicalRerootCursor) : Ordering :=
  (before left right).getD .eq

def insertCursorTotalBy
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → List CanonicalRerootCursor
  | [] => [candidate]
  | head :: tail =>
      match totalizedDecision before candidate head with
      | .gt | .eq => candidate :: head :: tail
      | .lt => head :: insertCursorTotalBy before candidate tail

def sortCursorsTotalBy
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    List CanonicalRerootCursor → List CanonicalRerootCursor
  | [] => []
  | cursor :: cursors =>
      insertCursorTotalBy before cursor (sortCursorsTotalBy before cursors)

theorem totalizedDecision_eq_of_success
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : before left right = some decision) :
    totalizedDecision before left right = decision := by
  simp [totalizedDecision, computed]

theorem insertCursorTotalBy_eq_of_success
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (candidate : CanonicalRerootCursor) :
    ∀ cursors sorted,
      insertCursorBy? before candidate cursors = some sorted →
      insertCursorTotalBy before candidate cursors = sorted
  | [], sorted, computed => by
      simp [insertCursorBy?] at computed
      subst sorted
      rfl
  | head :: tail, sorted, computed => by
      simp only [insertCursorBy?] at computed
      cases comparisonEq : before candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          have totalized : totalizedDecision before candidate head = decision :=
            totalizedDecision_eq_of_success before candidate head decision comparisonEq
          cases decision with
          | lt =>
              simp only [comparisonEq, Option.map_eq_some_iff] at computed
              rcases computed with ⟨deeper, deeperEq, rfl⟩
              simp [insertCursorTotalBy, totalized,
                insertCursorTotalBy_eq_of_success before candidate tail deeper deeperEq]
          | eq =>
              simp [comparisonEq] at computed
              subst sorted
              simp [insertCursorTotalBy, totalized]
          | gt =>
              simp [comparisonEq] at computed
              subst sorted
              simp [insertCursorTotalBy, totalized]

theorem sortCursorsTotalBy_eq_of_success
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∀ cursors sorted,
      sortCursorsBy? before cursors = some sorted →
      sortCursorsTotalBy before cursors = sorted
  | [], sorted, computed => by
      simp [sortCursorsBy?] at computed
      subst sorted
      rfl
  | cursor :: cursors, sorted, computed => by
      simp only [sortCursorsBy?] at computed
      cases tailEq : sortCursorsBy? before cursors with
      | none => simp [tailEq] at computed
      | some tail =>
          have sortedTail := sortCursorsTotalBy_eq_of_success before cursors tail tailEq
          have inserted := insertCursorTotalBy_eq_of_success before cursor tail sorted (by
            simpa [tailEq] using computed)
          simpa [sortCursorsTotalBy, sortedTail] using inserted

@[simp] theorem insertCursorTotalBy_length
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (candidate : CanonicalRerootCursor) : ∀ cursors,
    (insertCursorTotalBy before candidate cursors).length = cursors.length + 1
  | [] => rfl
  | head :: tail => by
      simp only [insertCursorTotalBy]
      cases totalizedDecision before candidate head <;>
        simp [insertCursorTotalBy_length before candidate tail]

@[simp] theorem sortCursorsTotalBy_length
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) : ∀ cursors,
    (sortCursorsTotalBy before cursors).length = cursors.length
  | [] => rfl
  | cursor :: cursors => by
      simp [sortCursorsTotalBy, sortCursorsTotalBy_length before cursors]

def denseDescriptorChildren (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor) : List CanonicalRerootCursor :=
  let sorted := sortCursorsTotalBy before (cursor.children mol)
  let bounded := sorted.take 3
  let phantom : CanonicalRerootCursor :=
    { node := mol.canonicalPhantom cursor.node.atom
        (cursor.node.rule1bRootDistance + 1) }
  bounded ++ List.replicate (3 - bounded.length) phantom

theorem denseDescriptorChildren_eq_of_success (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor) (ranked : List CanonicalRerootCursor)
    (computed : rankedCursorChildren? mol before cursor = some ranked) :
    denseDescriptorChildren mol before cursor = ranked := by
  unfold rankedCursorChildren? at computed
  let children := cursor.children mol
  by_cases tooWide : 3 < children.length
  · simp [children, tooWide] at computed
  · cases sortedEq : sortCursorsBy? before children with
    | none => simp [children, tooWide, sortedEq] at computed
    | some sorted =>
        have totalSorted : sortCursorsTotalBy before children = sorted :=
          sortCursorsTotalBy_eq_of_success before children sorted sortedEq
        have childLength : children.length ≤ 3 := Nat.le_of_not_gt tooWide
        have sortedLength : sorted.length = children.length := by
          rw [← totalSorted]
          exact sortCursorsTotalBy_length before children
        have rankedEq : ranked = sorted ++ List.replicate (3 - sorted.length)
            { node := mol.canonicalPhantom cursor.node.atom
                (cursor.node.rule1bRootDistance + 1) } := by
          simpa [children, tooWide, sortedEq] using computed.symm
        have takeEq : sorted.take 3 = sorted :=
          List.take_of_length_le (sortedLength.trans_le childLength)
        simp [denseDescriptorChildren, children, totalSorted, takeEq,
          sortedLength, rankedEq]

def denseDescriptorNext (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (frontier : List CanonicalRerootCursor) : List CanonicalRerootCursor :=
  frontier.flatMap (denseDescriptorChildren mol before)

def denseDescriptorFrontiers (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ℕ → List CanonicalRerootCursor → List (List CanonicalRerootCursor)
  | 0, frontier => [frontier]
  | depth + 1, frontier =>
      frontier :: denseDescriptorFrontiers mol before depth
        (denseDescriptorNext mol before frontier)

def descriptorPrioritySequence (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (frontiers : List (List CanonicalRerootCursor)) : List ℕ :=
  frontiers.flatten.map (occurrenceNodePriority state stage leftSide)

def DenseOccurrenceDescriptorKey := List ℕ

def buildDenseOccurrenceDescriptorKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ) (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (cursor : CanonicalRerootCursor) : DenseOccurrenceDescriptorKey :=
  descriptorPrioritySequence state stage leftSide
    (denseDescriptorFrontiers mol before fuel [cursor])

def compareDenseOccurrenceDescriptorKeys :
    DenseOccurrenceDescriptorKey → DenseOccurrenceDescriptorKey → Ordering :=
  List.compareLex compare

theorem compareDenseOccurrenceDescriptorKeys_transCmp :
    Std.TransCmp compareDenseOccurrenceDescriptorKeys := by
  unfold compareDenseOccurrenceDescriptorKeys
  change Std.TransCmp (List.compareLex (compare : ℕ → ℕ → Ordering))
  infer_instance

theorem compareOccurrenceDescriptorPairLabels_eq_compareLex (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage)
    (pairs : List (CanonicalRerootCursor × CanonicalRerootCursor)) :
    compareOccurrenceDescriptorPairLabels state stage pairs =
      List.compareLex compare
        (pairs.map fun pair => occurrenceNodePriority state stage true pair.1)
        (pairs.map fun pair => occurrenceNodePriority state stage false pair.2) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      simp only [compareOccurrenceDescriptorPairLabels, List.map_cons,
        List.compareLex_cons_cons]
      cases compare (occurrenceNodePriority state stage true pair.1)
          (occurrenceNodePriority state stage false pair.2) <;> simp [ih]

abbrev DenseDescriptorPair := CanonicalRerootCursor × CanonicalRerootCursor

def compareDenseDescriptorPairLabels (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (pairs : List DenseDescriptorPair) : Ordering :=
  List.compareLex compare
    (pairs.map fun pair => occurrenceNodePriority state stage true pair.1)
    (pairs.map fun pair => occurrenceNodePriority state stage false pair.2)

def denseNextDescriptorPairs (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (pairs : List DenseDescriptorPair) : List DenseDescriptorPair :=
  pairs.flatMap fun pair =>
    (denseDescriptorChildren mol beforeLeft pair.1).zip
      (denseDescriptorChildren mol beforeRight pair.2)

def compareDenseDescriptorRule (mol : RawMolecule) (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) :
    ℕ → List DenseDescriptorPair → Ordering
  | 0, pairs => compareDenseDescriptorPairLabels state stage pairs
  | depth + 1, pairs =>
      match compareDenseDescriptorPairLabels state stage pairs with
      | .eq => compareDenseDescriptorRule mol state beforeLeft beforeRight stage depth
          (denseNextDescriptorPairs mol beforeLeft beforeRight pairs)
      | decision => decision

@[simp] theorem denseDescriptorChildren_length (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor) :
    (denseDescriptorChildren mol before cursor).length = 3 := by
  simp [denseDescriptorChildren]

theorem denseNextDescriptorPairs_map_fst (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) : ∀ pairs,
    (denseNextDescriptorPairs mol beforeLeft beforeRight pairs).map Prod.fst =
      denseDescriptorNext mol beforeLeft (pairs.map Prod.fst)
  | [] => rfl
  | pair :: pairs => by
      simp only [denseNextDescriptorPairs, List.flatMap_cons, List.map_append,
        denseDescriptorNext, List.map_cons, List.flatMap_cons]
      rw [List.map_fst_zip (by simp)]
      congr 1
      simpa [denseNextDescriptorPairs, denseDescriptorNext] using
        denseNextDescriptorPairs_map_fst mol beforeLeft beforeRight pairs

theorem denseNextDescriptorPairs_map_snd (mol : RawMolecule)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) : ∀ pairs,
    (denseNextDescriptorPairs mol beforeLeft beforeRight pairs).map Prod.snd =
      denseDescriptorNext mol beforeRight (pairs.map Prod.snd)
  | [] => rfl
  | pair :: pairs => by
      simp only [denseNextDescriptorPairs, List.flatMap_cons, List.map_append,
        denseDescriptorNext, List.map_cons, List.flatMap_cons]
      rw [List.map_snd_zip (by simp)]
      congr 1
      simpa [denseNextDescriptorPairs, denseDescriptorNext] using
        denseNextDescriptorPairs_map_snd mol beforeLeft beforeRight pairs

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

theorem compareDenseDescriptorRule_eq_frontiers (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : ∀ depth pairs,
    compareDenseDescriptorRule mol state beforeLeft beforeRight stage depth pairs =
      List.compareLex compare
        ((denseDescriptorFrontiers mol beforeLeft depth (pairs.map Prod.fst)).flatten.map
          (occurrenceNodePriority state stage true))
        ((denseDescriptorFrontiers mol beforeRight depth (pairs.map Prod.snd)).flatten.map
          (occurrenceNodePriority state stage false))
  | 0, pairs => by
      simp [compareDenseDescriptorRule, compareDenseDescriptorPairLabels,
        denseDescriptorFrontiers, Function.comp_def]
  | depth + 1, pairs => by
      have prefixLength : (pairs.map Prod.fst).length = (pairs.map Prod.snd).length := by simp
      have appendRule := compareLex_append_of_length_eq (compare : ℕ → ℕ → Ordering)
        ((pairs.map Prod.fst).map (occurrenceNodePriority state stage true))
        ((pairs.map Prod.snd).map (occurrenceNodePriority state stage false))
        ((denseDescriptorFrontiers mol beforeLeft depth
          (denseDescriptorNext mol beforeLeft (pairs.map Prod.fst))).flatten.map
            (occurrenceNodePriority state stage true))
        ((denseDescriptorFrontiers mol beforeRight depth
          (denseDescriptorNext mol beforeRight (pairs.map Prod.snd))).flatten.map
            (occurrenceNodePriority state stage false)) (by simpa using prefixLength)
      have tail := compareDenseDescriptorRule_eq_frontiers mol state beforeLeft beforeRight stage
        depth (denseNextDescriptorPairs mol beforeLeft beforeRight pairs)
      rw [denseNextDescriptorPairs_map_fst, denseNextDescriptorPairs_map_snd] at tail
      simp only [compareDenseDescriptorRule, denseDescriptorFrontiers, List.flatten_cons,
        List.map_append]
      rw [appendRule]
      rw [tail]
      unfold compareDenseDescriptorPairLabels
      cases current : List.compareLex compare
          (List.map (fun pair => occurrenceNodePriority state stage true pair.1) pairs)
          (List.map (fun pair => occurrenceNodePriority state stage false pair.2) pairs) <;>
        simp [current, Function.comp_def]

def DescriptorPairSilent (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) (pair : DenseDescriptorPair) : Prop :=
  cursorTerminal mol pair.1 = true ∧ cursorTerminal mol pair.2 = true ∧
    compare (occurrenceNodePriority state stage true pair.1)
      (occurrenceNodePriority state stage false pair.2) = .eq

inductive ErasesSilentDescriptorPairs (mol : RawMolecule) (state : OccurrenceAuxState)
    (stage : RawDescriptorRuleStage) :
    List DenseDescriptorPair → List DenseDescriptorPair → Prop
  | nil : ErasesSilentDescriptorPairs mol state stage [] []
  | keep (pair : DenseDescriptorPair) {active dense : List DenseDescriptorPair}
      (tail : ErasesSilentDescriptorPairs mol state stage active dense) :
      ErasesSilentDescriptorPairs mol state stage (pair :: active) (pair :: dense)
  | erase (pair : DenseDescriptorPair) {active dense : List DenseDescriptorPair}
      (silent : DescriptorPairSilent mol state stage pair)
      (tail : ErasesSilentDescriptorPairs mol state stage active dense) :
      ErasesSilentDescriptorPairs mol state stage active (pair :: dense)

theorem ErasesSilentDescriptorPairs.labels_eq
    {mol : RawMolecule} {state : OccurrenceAuxState} {stage : RawDescriptorRuleStage}
    {active dense : List DenseDescriptorPair}
    (related : ErasesSilentDescriptorPairs mol state stage active dense) :
    compareDenseDescriptorPairLabels state stage active =
      compareDenseDescriptorPairLabels state stage dense := by
  induction related with
  | nil => rfl
  | keep pair tail ih =>
      unfold compareDenseDescriptorPairLabels at ih ⊢
      simp only [List.map_cons, List.compareLex]
      cases compare (occurrenceNodePriority state stage true pair.1)
          (occurrenceNodePriority state stage false pair.2) <;> simp [ih]
  | erase pair silent tail ih =>
      unfold compareDenseDescriptorPairLabels at ih ⊢
      rcases silent with ⟨_, _, tied⟩
      simp [List.compareLex, tied, ih]

theorem ErasesSilentDescriptorPairs.erase_all
    {mol : RawMolecule} {state : OccurrenceAuxState} {stage : RawDescriptorRuleStage}
    (silentPairs : List DenseDescriptorPair) {active dense : List DenseDescriptorPair}
    (allSilent : ∀ pair, pair ∈ silentPairs → DescriptorPairSilent mol state stage pair)
    (tail : ErasesSilentDescriptorPairs mol state stage active dense) :
    ErasesSilentDescriptorPairs mol state stage active (silentPairs ++ dense) := by
  induction silentPairs with
  | nil => simpa using tail
  | cons pair pairs ih =>
      exact .erase pair (allSilent pair (by simp))
        (ih (fun candidate member => allSilent candidate (by simp [member])))

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

def denseDescriptorPhantom (mol : RawMolecule) (parent distance : ℕ) :
    CanonicalRerootCursor :=
  { node := mol.canonicalPhantom parent distance }

theorem denseDescriptorChildren_eq_replicate_of_terminal (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (cursor : CanonicalRerootCursor) (terminal : cursorTerminal mol cursor = true) :
    denseDescriptorChildren mol before cursor =
      List.replicate 3 (denseDescriptorPhantom mol cursor.node.atom
        (cursor.node.rule1bRootDistance + 1)) := by
  have childrenNil := cursor_children_eq_nil_of_terminal mol cursor terminal
  simp [denseDescriptorChildren, denseDescriptorPhantom, childrenNil, sortCursorsTotalBy]

theorem dense_silent_descriptor_children_silent (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) (pair : DenseDescriptorPair)
    (silent : DescriptorPairSilent mol state stage pair) :
    ∀ child, child ∈ denseNextDescriptorPairs mol beforeLeft beforeRight [pair] →
      DescriptorPairSilent mol state stage child := by
  rcases silent with ⟨leftTerminal, rightTerminal, _⟩
  have leftChildren := denseDescriptorChildren_eq_replicate_of_terminal
    mol beforeLeft pair.1 leftTerminal
  have rightChildren := denseDescriptorChildren_eq_replicate_of_terminal
    mol beforeRight pair.2 rightTerminal
  intro child member
  simp only [denseNextDescriptorPairs, List.flatMap_singleton,
    leftChildren, rightChildren] at member
  simp at member
  subst child
  simp [DescriptorPairSilent, denseDescriptorPhantom, RawMolecule.canonicalPhantom,
    cursorTerminal, CanonicalRerootCursor.children, CanonicalBranchNode.forcedLeaf,
    occurrenceNodePriority, OccurrenceAuxState.factAt?]

theorem compareOccurrenceDescriptorPairLabels_eq_implies_all_tied
    (state : OccurrenceAuxState) (stage : RawDescriptorRuleStage) : ∀ pairs,
    compareOccurrenceDescriptorPairLabels state stage pairs = .eq →
      ∀ pair, pair ∈ pairs →
        compare (occurrenceNodePriority state stage true pair.1)
          (occurrenceNodePriority state stage false pair.2) = .eq
  | [], _, pair, member => by simp at member
  | head :: tail, computed, pair, member => by
      simp only [compareOccurrenceDescriptorPairLabels] at computed
      cases headEq : compare (occurrenceNodePriority state stage true head.1)
          (occurrenceNodePriority state stage false head.2) with
      | lt => simp [headEq] at computed
      | gt => simp [headEq] at computed
      | eq =>
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact headEq
          · exact compareOccurrenceDescriptorPairLabels_eq_implies_all_tied state stage tail
              (by simpa [headEq] using computed) pair tailMember

theorem ErasesSilentDescriptorPairs.keep_all
    {mol : RawMolecule} {state : OccurrenceAuxState} {stage : RawDescriptorRuleStage}
    (initial : List DenseDescriptorPair) {active dense : List DenseDescriptorPair}
    (tail : ErasesSilentDescriptorPairs mol state stage active dense) :
    ErasesSilentDescriptorPairs mol state stage (initial ++ active) (initial ++ dense) := by
  induction initial with
  | nil => simpa using tail
  | cons pair pairs ih => exact .keep pair ih

theorem nextDescriptorPairs_dense_related (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) {active dense next : List DenseDescriptorPair}
    (related : ErasesSilentDescriptorPairs mol state stage active dense)
    (allTied : ∀ pair, pair ∈ active →
      compare (occurrenceNodePriority state stage true pair.1)
        (occurrenceNodePriority state stage false pair.2) = .eq)
    (computed : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight active = some next) :
    ErasesSilentDescriptorPairs mol state stage next
      (denseNextDescriptorPairs mol beforeLeft beforeRight dense) := by
  induction related generalizing next with
  | nil =>
      simp [nextOccurrenceDescriptorPairs?] at computed
      subst next
      exact .nil
  | erase pair silent tail ih =>
      have tailRelated := ih allTied computed
      simpa [denseNextDescriptorPairs] using ErasesSilentDescriptorPairs.erase_all
        (denseNextDescriptorPairs mol beforeLeft beforeRight [pair])
        (dense_silent_descriptor_children_silent mol state beforeLeft beforeRight stage pair silent)
        tailRelated
  | keep pair relatedTail ih =>
      rename_i activeTail denseTail
      have pairTied := allTied pair (by simp)
      have tailTied : ∀ candidate, candidate ∈ activeTail →
          compare (occurrenceNodePriority state stage true candidate.1)
            (occurrenceNodePriority state stage false candidate.2) = .eq := by
        intro candidate member
        exact allTied candidate (by simp [member])
      simp only [nextOccurrenceDescriptorPairs?] at computed
      cases restEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight activeTail with
      | none => simp [restEq] at computed
      | some rest =>
          have restRelated := ih tailTied restEq
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
                    simp only [denseNextDescriptorPairs, List.flatMap_cons, List.flatMap_nil,
                      denseLeft, denseRight]
                    exact ErasesSilentDescriptorPairs.keep_all (left.zip right) restRelated
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
                    simp only [denseNextDescriptorPairs, List.flatMap_cons, List.flatMap_nil,
                      denseLeft, denseRight]
                    exact ErasesSilentDescriptorPairs.keep_all (left.zip right) restRelated
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
                    simp only [denseNextDescriptorPairs, List.flatMap_cons, List.flatMap_nil,
                      denseLeft, denseRight]
                    exact ErasesSilentDescriptorPairs.keep_all (left.zip right) restRelated
          · simp [restEq, leftTerminal, rightTerminal] at computed
            subst next
            have silentPair : DescriptorPairSilent mol state stage pair :=
              ⟨leftTerminal, rightTerminal, pairTied⟩
            simpa [denseNextDescriptorPairs] using ErasesSilentDescriptorPairs.erase_all
              (denseNextDescriptorPairs mol beforeLeft beforeRight [pair])
              (dense_silent_descriptor_children_silent mol state beforeLeft beforeRight stage pair
                silentPair)
              restRelated

theorem ErasesSilentDescriptorPairs.refl
    {mol : RawMolecule} {state : OccurrenceAuxState} {stage : RawDescriptorRuleStage} : ∀ pairs,
    ErasesSilentDescriptorPairs mol state stage pairs pairs
  | [] => .nil
  | pair :: pairs => .keep pair (ErasesSilentDescriptorPairs.refl pairs)

theorem ErasesSilentDescriptorPairs.empty_dense_rule_eq (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : ∀ depth {dense},
    ErasesSilentDescriptorPairs mol state stage [] dense →
      compareDenseDescriptorRule mol state beforeLeft beforeRight stage depth dense = .eq
  | 0, dense, related => by
      have labels := related.labels_eq
      exact labels.symm.trans (by rfl)
  | depth + 1, dense, related => by
      have labels := related.labels_eq
      have current : compareDenseDescriptorPairLabels state stage dense = .eq := by
        exact labels.symm.trans (by rfl)
      have nextRelated : ErasesSilentDescriptorPairs mol state stage []
          (denseNextDescriptorPairs mol beforeLeft beforeRight dense) :=
        nextDescriptorPairs_dense_related mol state beforeLeft beforeRight stage related
          (by intro pair member; simp at member)
          (by rfl)
      simp only [compareDenseDescriptorRule, current]
      exact ErasesSilentDescriptorPairs.empty_dense_rule_eq mol state beforeLeft beforeRight stage
        depth nextRelated

theorem compareOccurrenceDescriptorRule_success_factors (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) : ∀ fuel active dense decision,
    ErasesSilentDescriptorPairs mol state stage active dense →
    compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel active =
      some decision →
    compareDenseDescriptorRule mol state beforeLeft beforeRight stage fuel dense = decision
  | 0, active, dense, decision, related, computed => by
      simp only [compareOccurrenceDescriptorRule] at computed
      by_cases tooWide : RawMolecule.defaultBranchWidthCap < active.length
      · simp [tooWide] at computed
      · simp only [tooWide, Bool.false_eq_true, ↓reduceIte] at computed
        have labelsEq := related.labels_eq
        cases current : compareOccurrenceDescriptorPairLabels state stage active with
        | lt =>
            simp [current] at computed
            subst decision
            have activeCurrent : compareDenseDescriptorPairLabels state stage active = .lt := by
              rw [compareDenseDescriptorPairLabels,
                ← compareOccurrenceDescriptorPairLabels_eq_compareLex]
              exact current
            exact labelsEq.symm.trans activeCurrent
        | gt =>
            simp [current] at computed
            subst decision
            have activeCurrent : compareDenseDescriptorPairLabels state stage active = .gt := by
              rw [compareDenseDescriptorPairLabels,
                ← compareOccurrenceDescriptorPairLabels_eq_compareLex]
              exact current
            exact labelsEq.symm.trans activeCurrent
        | eq =>
            cases nextEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight active with
            | none => simp [current, nextEq] at computed
            | some next =>
                cases next with
                | nil =>
                    simp [current, nextEq] at computed
                    subst decision
                    have activeCurrent :
                        compareDenseDescriptorPairLabels state stage active = .eq := by
                      rw [compareDenseDescriptorPairLabels,
                        ← compareOccurrenceDescriptorPairLabels_eq_compareLex]
                      exact current
                    exact labelsEq.symm.trans activeCurrent
                | cons nextHead nextTail => simp [current, nextEq] at computed
  | fuel + 1, active, dense, decision, related, computed => by
      simp only [compareOccurrenceDescriptorRule] at computed
      by_cases tooWide : RawMolecule.defaultBranchWidthCap < active.length
      · simp [tooWide] at computed
      · simp only [tooWide, Bool.false_eq_true, ↓reduceIte] at computed
        have labelsEq := related.labels_eq
        cases current : compareOccurrenceDescriptorPairLabels state stage active with
        | lt =>
            simp [current] at computed
            subst decision
            have activeCurrent : compareDenseDescriptorPairLabels state stage active = .lt := by
              rw [compareDenseDescriptorPairLabels,
                ← compareOccurrenceDescriptorPairLabels_eq_compareLex]
              exact current
            have denseCurrent := labelsEq.symm.trans activeCurrent
            simp [compareDenseDescriptorRule, denseCurrent]
        | gt =>
            simp [current] at computed
            subst decision
            have activeCurrent : compareDenseDescriptorPairLabels state stage active = .gt := by
              rw [compareDenseDescriptorPairLabels,
                ← compareOccurrenceDescriptorPairLabels_eq_compareLex]
              exact current
            have denseCurrent := labelsEq.symm.trans activeCurrent
            simp [compareDenseDescriptorRule, denseCurrent]
        | eq =>
            have activeCurrent : compareDenseDescriptorPairLabels state stage active = .eq := by
              rw [compareDenseDescriptorPairLabels,
                ← compareOccurrenceDescriptorPairLabels_eq_compareLex]
              exact current
            have denseCurrent := labelsEq.symm.trans activeCurrent
            cases nextEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight active with
            | none => simp [current, nextEq] at computed
            | some next =>
                cases next with
                | nil =>
                    simp [current, nextEq] at computed
                    subst decision
                    have allTied := compareOccurrenceDescriptorPairLabels_eq_implies_all_tied
                      state stage active current
                    have nextRelated := nextDescriptorPairs_dense_related mol state beforeLeft
                      beforeRight stage related allTied nextEq
                    have tailEq := ErasesSilentDescriptorPairs.empty_dense_rule_eq mol state
                      beforeLeft beforeRight stage fuel nextRelated
                    simp [compareDenseDescriptorRule, denseCurrent, tailEq]
                | cons nextHead nextTail =>
                    have recursiveEq :
                        compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel
                            (nextHead :: nextTail) = some decision := by
                      simpa [current, nextEq] using computed
                    have allTied := compareOccurrenceDescriptorPairLabels_eq_implies_all_tied
                      state stage active current
                    have nextRelated := nextDescriptorPairs_dense_related mol state beforeLeft
                      beforeRight stage related allTied nextEq
                    have recursive := compareOccurrenceDescriptorRule_success_factors mol state
                      beforeLeft beforeRight stage fuel (nextHead :: nextTail)
                      (denseNextDescriptorPairs mol beforeLeft beforeRight dense) decision
                      nextRelated recursiveEq
                    simp [compareDenseDescriptorRule, denseCurrent, recursive]

theorem compareOccurrenceDescriptorRule_singleton_success_factors (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (stage : RawDescriptorRuleStage) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : compareOccurrenceDescriptorRule mol state beforeLeft beforeRight stage fuel
      [(left, right)] = some decision) :
    compareDenseOccurrenceDescriptorKeys
        (buildDenseOccurrenceDescriptorKey mol state beforeLeft fuel stage true left)
        (buildDenseOccurrenceDescriptorKey mol state beforeRight fuel stage false right) =
      decision := by
  have factored := compareOccurrenceDescriptorRule_success_factors mol state beforeLeft beforeRight
    stage fuel [(left, right)] [(left, right)] decision
    (ErasesSilentDescriptorPairs.refl [(left, right)]) computed
  rw [compareDenseDescriptorRule_eq_frontiers] at factored
  change List.compareLex compare
      ((denseDescriptorFrontiers mol beforeLeft fuel [left]).flatten.map
        (occurrenceNodePriority state stage true))
      ((denseDescriptorFrontiers mol beforeRight fuel [right]).flatten.map
        (occurrenceNodePriority state stage false)) = decision
  exact factored

/-! The complete descriptor-only comparator at a constitutionally tied root is a rule-major
lexicographic comparison of unary dense priority sequences. -/

def localDescriptorStage (leftSide : Bool) (stage : RawDescriptorRuleStage) :
    RawDescriptorRuleStage :=
  if leftSide then stage.leftInternal else stage.rightInternal

def buildDenseTiedRootDescriptorKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (stage : RawDescriptorRuleStage) (leftSide : Bool)
    (cursor : CanonicalRerootCursor) : List DenseOccurrenceDescriptorKey :=
  let before := compareOccurrenceDescriptorBranchAt mol state fuel
    (localDescriptorStage leftSide stage)
  let field := fun selected =>
    buildDenseOccurrenceDescriptorKey mol state before fuel selected leftSide cursor
  field .rule4a :: match stage with
    | .rule4a => []
    | .rule4b leftReference rightReference =>
        [field (.rule4b leftReference rightReference)]
    | .rule4c =>
        if state.any fun fact => !fact.uppercase then [field .rule4c] else []
    | .rule5 leftReference rightReference =>
        if state.any fun fact => !fact.uppercase then
          [field .rule4c, field (.rule5 leftReference rightReference)]
        else [field (.rule5 leftReference rightReference)]

def compareDenseTiedRootDescriptorKeys :
    List DenseOccurrenceDescriptorKey → List DenseOccurrenceDescriptorKey → Ordering :=
  List.compareLex compareDenseOccurrenceDescriptorKeys

theorem compareDenseTiedRootDescriptorKeys_transCmp :
    Std.TransCmp compareDenseTiedRootDescriptorKeys := by
  unfold compareDenseTiedRootDescriptorKeys compareDenseOccurrenceDescriptorKeys
  change Std.TransCmp
    (List.compareLex (List.compareLex (compare : ℕ → ℕ → Ordering)))
  infer_instance

theorem compareOccurrenceDescriptorAtTiedRoot_success_factors
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (stage : RawDescriptorRuleStage) (left right : CanonicalRerootCursor)
    (decision : Ordering)
    (computed : compareOccurrenceDescriptorAtTiedRoot? mol state fuel stage left right =
      some decision) :
    compareDenseTiedRootDescriptorKeys
        (buildDenseTiedRootDescriptorKey mol state fuel stage true left)
        (buildDenseTiedRootDescriptorKey mol state fuel stage false right) = decision := by
  let beforeLeft := compareOccurrenceDescriptorBranchAt mol state fuel stage.leftInternal
  let beforeRight := compareOccurrenceDescriptorBranchAt mol state fuel stage.rightInternal
  cases rule4aEq : compareOccurrenceDescriptorRule mol state beforeLeft beforeRight .rule4a fuel
      [(left, right)] with
  | none =>
      simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq] at computed
  | some rule4a =>
      have rule4aFactor := compareOccurrenceDescriptorRule_singleton_success_factors mol state
        beforeLeft beforeRight .rule4a fuel left right rule4a rule4aEq
      dsimp [beforeLeft, beforeRight] at rule4aFactor
      cases rule4a with
      | lt =>
          simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq] at computed
          subst decision
          cases stage <;>
            simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
              localDescriptorStage, rule4aFactor]
      | gt =>
          simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq] at computed
          subst decision
          cases stage <;>
            simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
              localDescriptorStage, rule4aFactor]
      | eq =>
          cases stage with
          | rule4a =>
              simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight, rule4aEq]
                at computed
              subst decision
              simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                localDescriptorStage, beforeLeft, beforeRight, rule4aFactor]
          | rule4b leftReference rightReference =>
              cases selectedEq : compareOccurrenceDescriptorRule mol state beforeLeft beforeRight
                  (.rule4b leftReference rightReference) fuel [(left, right)] with
              | none =>
                  simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                    rule4aEq, selectedEq] at computed
              | some selected =>
                  have selectedFactor :=
                    compareOccurrenceDescriptorRule_singleton_success_factors mol state
                      beforeLeft beforeRight (.rule4b leftReference rightReference) fuel left right
                      selected selectedEq
                  dsimp [beforeLeft, beforeRight] at selectedFactor
                  simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                    rule4aEq, selectedEq] at computed
                  subst decision
                  simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                    localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, selectedFactor]
                  cases selected <;> rfl
          | rule4c =>
              cases lowercase : state.any fun fact => !fact.uppercase
              · simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                  rule4aEq, lowercase] at computed
                subst decision
                simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                  localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, lowercase]
              · cases selectedEq : compareOccurrenceDescriptorRule mol state beforeLeft
                    beforeRight .rule4c fuel [(left, right)] with
                | none =>
                    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                | some selected =>
                    have selectedFactor :=
                      compareOccurrenceDescriptorRule_singleton_success_factors mol state
                        beforeLeft beforeRight .rule4c fuel left right selected selectedEq
                    dsimp [beforeLeft, beforeRight] at selectedFactor
                    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                    subst decision
                    simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                      localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, selectedFactor,
                      lowercase]
                    cases selected <;> rfl
          | rule5 leftReference rightReference =>
              cases lowercase : state.any fun fact => !fact.uppercase
              · cases selectedEq : compareOccurrenceDescriptorRule mol state beforeLeft
                    beforeRight (.rule5 leftReference rightReference) fuel [(left, right)] with
                | none =>
                    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                | some selected =>
                    have selectedFactor :=
                      compareOccurrenceDescriptorRule_singleton_success_factors mol state
                        beforeLeft beforeRight (.rule5 leftReference rightReference) fuel left right
                        selected selectedEq
                    dsimp [beforeLeft, beforeRight] at selectedFactor
                    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, selectedEq] at computed
                    subst decision
                    simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                      localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, selectedFactor,
                      lowercase]
                    cases selected <;> rfl
              · cases rule4cEq : compareOccurrenceDescriptorRule mol state beforeLeft
                    beforeRight .rule4c fuel [(left, right)] with
                | none =>
                    simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                      rule4aEq, lowercase, rule4cEq] at computed
                | some rule4c =>
                    have rule4cFactor :=
                      compareOccurrenceDescriptorRule_singleton_success_factors mol state
                        beforeLeft beforeRight .rule4c fuel left right rule4c rule4cEq
                    dsimp [beforeLeft, beforeRight] at rule4cFactor
                    cases rule4c with
                    | lt =>
                        simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                          rule4aEq, lowercase, rule4cEq] at computed
                        subst decision
                        simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                          localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, rule4cFactor,
                          lowercase]
                    | gt =>
                        simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                          rule4aEq, lowercase, rule4cEq] at computed
                        subst decision
                        simp [buildDenseTiedRootDescriptorKey, compareDenseTiedRootDescriptorKeys, List.compareLex,
                          localDescriptorStage, beforeLeft, beforeRight, rule4aFactor, rule4cFactor,
                          lowercase]
                    | eq =>
                        cases selectedEq : compareOccurrenceDescriptorRule mol state beforeLeft
                            beforeRight (.rule5 leftReference rightReference) fuel [(left, right)] with
                        | none =>
                            simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                              rule4aEq, lowercase, rule4cEq, selectedEq] at computed
                        | some selected =>
                            have selectedFactor :=
                              compareOccurrenceDescriptorRule_singleton_success_factors mol state
                                beforeLeft beforeRight (.rule5 leftReference rightReference) fuel
                                left right selected selectedEq
                            dsimp [beforeLeft, beforeRight] at selectedFactor
                            simp [compareOccurrenceDescriptorAtTiedRoot?, beforeLeft, beforeRight,
                              rule4aEq, lowercase, rule4cEq, selectedEq] at computed
                            subst decision
                            simp [buildDenseTiedRootDescriptorKey,
                              compareDenseTiedRootDescriptorKeys, List.compareLex, localDescriptorStage,
                              beforeLeft, beforeRight, rule4aFactor, rule4cFactor, selectedFactor,
                              lowercase]
                            cases selected <;> rfl

theorem occurrenceNodePriority_rule4a_side_independent (state : OccurrenceAuxState) :
    occurrenceNodePriority state .rule4a true =
      occurrenceNodePriority state .rule4a false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4c_side_independent (state : OccurrenceAuxState) :
    occurrenceNodePriority state .rule4c true =
      occurrenceNodePriority state .rule4c false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4b_same_reference_side_independent
    (state : OccurrenceAuxState) (reference : RS) :
    occurrenceNodePriority state (.rule4b reference reference) true =
      occurrenceNodePriority state (.rule4b reference reference) false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4b_left_local (state : OccurrenceAuxState)
    (leftReference rightReference : RS) :
    occurrenceNodePriority state (.rule4b leftReference rightReference) true =
      occurrenceNodePriority state (.rule4b leftReference leftReference) true := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule4b_right_local (state : OccurrenceAuxState)
    (leftReference rightReference : RS) :
    occurrenceNodePriority state (.rule4b leftReference rightReference) false =
      occurrenceNodePriority state (.rule4b rightReference rightReference) false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem occurrenceNodePriority_rule5_same_reference_side_independent
    (state : OccurrenceAuxState) (reference : RS) :
    occurrenceNodePriority state (.rule5 reference reference) true =
      occurrenceNodePriority state (.rule5 reference reference) false := by
  funext cursor
  cases cursor.node.provenance <;> cases state.factAt? cursor.node <;>
    simp [occurrenceNodePriority]

theorem buildDenseTiedRoot_rule4a_side_independent (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (cursor : CanonicalRerootCursor) :
    buildDenseTiedRootDescriptorKey mol state fuel .rule4a true cursor =
      buildDenseTiedRootDescriptorKey mol state fuel .rule4a false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildDenseOccurrenceDescriptorKey, descriptorPrioritySequence,
    occurrenceNodePriority_rule4a_side_independent state]

theorem buildDenseTiedRoot_rule4c_side_independent (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (cursor : CanonicalRerootCursor) :
    buildDenseTiedRootDescriptorKey mol state fuel .rule4c true cursor =
      buildDenseTiedRootDescriptorKey mol state fuel .rule4c false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildDenseOccurrenceDescriptorKey, descriptorPrioritySequence,
    occurrenceNodePriority_rule4a_side_independent state,
    occurrenceNodePriority_rule4c_side_independent state]

theorem buildDenseTiedRoot_rule4b_same_reference_side_independent (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (reference : RS)
    (cursor : CanonicalRerootCursor) :
    buildDenseTiedRootDescriptorKey mol state fuel (.rule4b reference reference) true cursor =
      buildDenseTiedRootDescriptorKey mol state fuel (.rule4b reference reference) false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildDenseOccurrenceDescriptorKey, descriptorPrioritySequence,
    occurrenceNodePriority_rule4a_side_independent state,
    occurrenceNodePriority_rule4b_same_reference_side_independent state reference]

theorem buildDenseTiedRoot_rule4b_left_local (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (leftReference rightReference : RS)
    (cursor : CanonicalRerootCursor) :
    buildDenseTiedRootDescriptorKey mol state fuel
        (.rule4b leftReference rightReference) true cursor =
      buildDenseTiedRootDescriptorKey mol state fuel
        (.rule4b leftReference leftReference) true cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildDenseOccurrenceDescriptorKey, descriptorPrioritySequence,
    occurrenceNodePriority_rule4b_left_local state leftReference rightReference]

theorem buildDenseTiedRoot_rule4b_right_local (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (leftReference rightReference : RS)
    (cursor : CanonicalRerootCursor) :
    buildDenseTiedRootDescriptorKey mol state fuel
        (.rule4b leftReference rightReference) false cursor =
      buildDenseTiedRootDescriptorKey mol state fuel
        (.rule4b rightReference rightReference) false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildDenseOccurrenceDescriptorKey, descriptorPrioritySequence,
    occurrenceNodePriority_rule4b_right_local state leftReference rightReference]

theorem buildDenseTiedRoot_rule5_same_reference_side_independent (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (reference : RS)
    (cursor : CanonicalRerootCursor) :
    buildDenseTiedRootDescriptorKey mol state fuel (.rule5 reference reference) true cursor =
      buildDenseTiedRootDescriptorKey mol state fuel (.rule5 reference reference) false cursor := by
  simp [buildDenseTiedRootDescriptorKey, localDescriptorStage,
    RawDescriptorRuleStage.leftInternal, RawDescriptorRuleStage.rightInternal,
    buildDenseOccurrenceDescriptorKey, descriptorPrioritySequence,
    occurrenceNodePriority_rule4a_side_independent state,
    occurrenceNodePriority_rule4c_side_independent state,
    occurrenceNodePriority_rule5_same_reference_side_independent state reference]

abbrev DenseRule4aProjectedKey := List DenseOccurrenceDescriptorKey

def buildDenseRule4aProjectedKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (cursor : CanonicalRerootCursor) : DenseRule4aProjectedKey :=
  buildDenseTiedRootDescriptorKey mol state fuel .rule4a true cursor

def compareDenseRule4aProjectedKeys :
    DenseRule4aProjectedKey → DenseRule4aProjectedKey → Ordering :=
  compareDenseTiedRootDescriptorKeys

theorem compareDenseRule4aProjectedKeys_transCmp :
    Std.TransCmp compareDenseRule4aProjectedKeys :=
  compareDenseTiedRootDescriptorKeys_transCmp

theorem compareOccurrenceRule4a_tied_success_factors (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : compareOccurrenceDescriptorAtTiedRoot? mol state fuel .rule4a left right =
      some decision) :
    compareDenseRule4aProjectedKeys
        (buildDenseRule4aProjectedKey mol state fuel left)
        (buildDenseRule4aProjectedKey mol state fuel right) = decision := by
  have factored := compareOccurrenceDescriptorAtTiedRoot_success_factors mol state fuel .rule4a
    left right decision computed
  rw [← buildDenseTiedRoot_rule4a_side_independent mol state fuel right] at factored
  exact factored

abbrev DenseRule5ProjectedKey := List DenseOccurrenceDescriptorKey

def buildDenseRule5ProjectedKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (cursor : CanonicalRerootCursor) : DenseRule5ProjectedKey :=
  buildDenseTiedRootDescriptorKey mol state fuel (.rule5 RS.R RS.R) true cursor

def compareDenseRule5ProjectedKeys :
    DenseRule5ProjectedKey → DenseRule5ProjectedKey → Ordering :=
  compareDenseTiedRootDescriptorKeys

theorem compareDenseRule5ProjectedKeys_transCmp :
    Std.TransCmp compareDenseRule5ProjectedKeys :=
  compareDenseTiedRootDescriptorKeys_transCmp

/-- Production Rule 5's ordering projection is exactly its R-reference unary-key comparison.
The S-reference run supplies only the pseudoasymmetry bit and cannot change `ordering`. -/
theorem compareOccurrenceRule5_ordering_success_factors (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (result : RawRule5Comparison)
    (computed : compareOccurrenceRule5? mol state fuel left right = some result) :
    compareDenseRule5ProjectedKeys
        (buildDenseRule5ProjectedKey mol state fuel left)
        (buildDenseRule5ProjectedKey mol state fuel right) = result.ordering := by
  cases cmpREq : compareOccurrenceDescriptorAtTiedRoot? mol state fuel
      (.rule5 RS.R RS.R) left right with
  | none => simp [compareOccurrenceRule5?, cmpREq] at computed
  | some cmpR =>
      have cmpRFactor := compareOccurrenceDescriptorAtTiedRoot_success_factors mol state fuel
        (.rule5 RS.R RS.R) left right cmpR cmpREq
      cases cmpSEq : compareOccurrenceDescriptorAtTiedRoot? mol state fuel
          (.rule5 RS.S RS.S) left right with
      | none => simp [compareOccurrenceRule5?, cmpREq, cmpSEq] at computed
      | some cmpS =>
          cases cmpR <;> cases cmpS <;>
            simp [compareOccurrenceRule5?, cmpREq, cmpSEq] at computed <;>
            subst result <;>
            simpa [compareDenseRule5ProjectedKeys, buildDenseRule5ProjectedKey,
              buildDenseTiedRoot_rule5_same_reference_side_independent mol state fuel RS.R right]
              using cmpRFactor

/-- Unary Rule-4b key.  Reference-count priority is compared before the ranked descriptor
readings, as required by IUPAC P-92.5.2.1 criterion (c)(i). -/
structure DenseRule4bProjectedKey where
  referenceCountPriority : Nat
  readings : List (List DenseOccurrenceDescriptorKey)

/-- One selected reference precedes two.  Zero and unsupported counts are retained below both
supported nonzero counts; successful production comparisons never use those mixed cases. -/
def denseRule4bReferenceCountPriority : Nat → Nat
  | 1 => 2
  | 2 => 1
  | _ => 0

def totalRankedOccurrenceRule4bReferences (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (root : CanonicalRerootCursor)
    (references : List RS) : List RS :=
  (rankOccurrenceRule4bReferences? mol state fuel root references).getD references

def buildDenseRule4bProjectedKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (root : CanonicalRerootCursor) : DenseRule4bProjectedKey :=
  let references := occurrenceRule4bReferences mol state fuel [root]
  let ranked := totalRankedOccurrenceRule4bReferences mol state fuel root references
  { referenceCountPriority := denseRule4bReferenceCountPriority references.length
    readings := ranked.map fun reference =>
      buildDenseTiedRootDescriptorKey mol state fuel (.rule4b reference reference) true root }

def compareDenseRule4bProjectedKeys :
    DenseRule4bProjectedKey → DenseRule4bProjectedKey → Ordering :=
  compareLex
    (Ordering.byKey DenseRule4bProjectedKey.referenceCountPriority compare)
    (Ordering.byKey DenseRule4bProjectedKey.readings
      (List.compareLex compareDenseTiedRootDescriptorKeys))

theorem compareDenseRule4bProjectedKeys_transCmp :
    Std.TransCmp compareDenseRule4bProjectedKeys := by
  unfold compareDenseRule4bProjectedKeys
  letI := compareDenseTiedRootDescriptorKeys_transCmp
  infer_instance

@[simp] theorem compareDenseRule4bProjectedKeys_same_count
    (priority : Nat) (leftReadings rightReadings : List (List DenseOccurrenceDescriptorKey)) :
    compareDenseRule4bProjectedKeys
        { referenceCountPriority := priority, readings := leftReadings }
        { referenceCountPriority := priority, readings := rightReadings } =
      List.compareLex compareDenseTiedRootDescriptorKeys leftReadings rightReadings := by
  simp [compareDenseRule4bProjectedKeys, compareLex, Ordering.byKey]

@[simp] theorem compareDenseRule4bProjectedKeys_one_over_two
    (leftReadings rightReadings : List (List DenseOccurrenceDescriptorKey)) :
    compareDenseRule4bProjectedKeys
        { referenceCountPriority := 2, readings := leftReadings }
        { referenceCountPriority := 1, readings := rightReadings } = Ordering.gt := by
  rfl

@[simp] theorem compareDenseRule4bProjectedKeys_two_below_one
    (leftReadings rightReadings : List (List DenseOccurrenceDescriptorKey)) :
    compareDenseRule4bProjectedKeys
        { referenceCountPriority := 1, readings := leftReadings }
        { referenceCountPriority := 2, readings := rightReadings } = Ordering.lt := by
  rfl

theorem rankOccurrenceRule4bReferences_length_of_success (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (root : CanonicalRerootCursor) :
    ∀ references ranked,
    rankOccurrenceRule4bReferences? mol state fuel root references = some ranked →
      ranked.length = references.length
  | [], ranked, computed => by simp [rankOccurrenceRule4bReferences?] at computed; subst ranked; rfl
  | [first], ranked, computed => by
      simp [rankOccurrenceRule4bReferences?] at computed
      subst ranked
      rfl
  | [first, second], ranked, computed => by
      simp only [rankOccurrenceRule4bReferences?] at computed
      cases decisionEq : compareOccurrenceDescriptorAtTiedRoot? mol state fuel
          (.rule4b first second) root root with
      | none => simp [decisionEq] at computed
      | some decision =>
          cases decision <;> simp [decisionEq] at computed <;> subst ranked <;> rfl
  | first :: second :: third :: rest, ranked, computed => by
      simp [rankOccurrenceRule4bReferences?] at computed
      subst ranked
      rfl

theorem list_eq_getD_two {alpha : Type*} (values : List alpha)
    (fallback0 fallback1 : alpha) (lengthEq : values.length = 2) :
    values = [values.getD 0 fallback0, values.getD 1 fallback1] := by
  cases values with
  | nil => simp at lengthEq
  | cons first tail =>
      cases tail with
      | nil => simp at lengthEq
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest => simp at lengthEq

theorem exists_pair_of_length_eq_two {alpha : Type*} (values : List alpha)
    (lengthEq : values.length = 2) : ∃ first second, values = [first, second] := by
  cases values with
  | nil => simp at lengthEq
  | cons first tail =>
      cases tail with
      | nil => simp at lengthEq
      | cons second rest =>
          cases rest with
          | nil => exact ⟨first, second, rfl⟩
          | cons third rest => simp at lengthEq

theorem compareOccurrenceRule4b_success_factors (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (computed : compareOccurrenceRule4b? mol state fuel left right = some decision) :
    compareDenseRule4bProjectedKeys
        (buildDenseRule4bProjectedKey mol state fuel left)
        (buildDenseRule4bProjectedKey mol state fuel right) = decision := by
  cases leftRefsEq : occurrenceRule4bReferences mol state fuel [left] with
  | nil =>
      cases rightRefsEq : occurrenceRule4bReferences mol state fuel [right] with
      | nil =>
          simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
          subst decision
          simp [buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
            leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
            rankOccurrenceRule4bReferences?, List.compareLex, compareLex, Ordering.byKey]
      | cons rightFirst rightTail =>
          simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
  | cons leftFirst leftTail =>
      cases leftTail with
      | nil =>
          cases rightRefsEq : occurrenceRule4bReferences mol state fuel [right] with
          | nil => simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
          | cons rightFirst rightTail =>
              cases rightTail with
              | nil =>
                  cases selectedEq : compareOccurrenceDescriptorAtTiedRoot? mol state fuel
                      (.rule4b leftFirst rightFirst) left right with
                  | none =>
                      simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq, selectedEq]
                        at computed
                  | some selected =>
                      have selectedFactor :=
                        compareOccurrenceDescriptorAtTiedRoot_success_factors mol state fuel
                          (.rule4b leftFirst rightFirst) left right selected selectedEq
                      simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq, selectedEq]
                        at computed
                      subst decision
                      rw [buildDenseTiedRoot_rule4b_left_local mol state fuel leftFirst
                        rightFirst left] at selectedFactor
                      rw [buildDenseTiedRoot_rule4b_right_local mol state fuel leftFirst
                        rightFirst right] at selectedFactor
                      rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent mol state fuel
                        rightFirst right] at selectedFactor
                      simp [buildDenseRule4bProjectedKey, denseRule4bReferenceCountPriority,
                        leftRefsEq, rightRefsEq, totalRankedOccurrenceRule4bReferences,
                        rankOccurrenceRule4bReferences?, List.compareLex, selectedFactor]
                      cases selected <;> rfl
              | cons rightSecond rightRest =>
                  cases rightRest with
                  | nil =>
                      simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
                      subst decision
                      simp [buildDenseRule4bProjectedKey,
                        denseRule4bReferenceCountPriority, leftRefsEq, rightRefsEq,
                        totalRankedOccurrenceRule4bReferences,
                        rankOccurrenceRule4bReferences?, compareLex, Ordering.byKey]
                  | cons rightThird rightMore =>
                      simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
      | cons leftSecond leftRest =>
          cases leftRest with
          | cons leftThird leftMore =>
              simp [compareOccurrenceRule4b?, leftRefsEq] at computed
          | nil =>
              cases rightRefsEq : occurrenceRule4bReferences mol state fuel [right] with
              | nil => simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
              | cons rightFirst rightTail =>
                  cases rightTail with
                  | nil =>
                      simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
                      subst decision
                      simp [buildDenseRule4bProjectedKey,
                        denseRule4bReferenceCountPriority, leftRefsEq, rightRefsEq,
                        totalRankedOccurrenceRule4bReferences,
                        rankOccurrenceRule4bReferences?, compareLex, Ordering.byKey]
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | cons rightThird rightMore =>
                          simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq] at computed
                      | nil =>
                          cases rankLeftEq : rankOccurrenceRule4bReferences? mol state fuel left
                              [leftFirst, leftSecond] with
                          | none =>
                              simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq, rankLeftEq]
                                at computed
                          | some rankedLeft =>
                              cases rankRightEq : rankOccurrenceRule4bReferences? mol state fuel right
                                  [rightFirst, rightSecond] with
                              | none =>
                                  simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq,
                                    rankLeftEq, rankRightEq] at computed
                              | some rankedRight =>
                                  have rankedLeftLength :=
                                    rankOccurrenceRule4bReferences_length_of_success mol state fuel
                                      left [leftFirst, leftSecond] rankedLeft rankLeftEq
                                  have rankedRightLength :=
                                    rankOccurrenceRule4bReferences_length_of_success mol state fuel
                                      right [rightFirst, rightSecond] rankedRight rankRightEq
                                  rcases exists_pair_of_length_eq_two rankedLeft rankedLeftLength with
                                    ⟨rankedLeftFirst, rankedLeftSecond, rfl⟩
                                  rcases exists_pair_of_length_eq_two rankedRight rankedRightLength with
                                    ⟨rankedRightFirst, rankedRightSecond, rfl⟩
                                  simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq,
                                    rankLeftEq, rankRightEq] at computed
                                  cases firstEq : compareOccurrenceDescriptorAtTiedRoot? mol state fuel
                                      (.rule4b rankedLeftFirst rankedRightFirst) left right with
                                  | none =>
                                      rw [firstEq] at computed
                                      simp at computed
                                  | some first =>
                                      have firstFactor :=
                                        compareOccurrenceDescriptorAtTiedRoot_success_factors mol
                                          state fuel (.rule4b rankedLeftFirst rankedRightFirst)
                                            left right first firstEq
                                      rw [buildDenseTiedRoot_rule4b_left_local mol state fuel
                                        rankedLeftFirst rankedRightFirst left]
                                        at firstFactor
                                      rw [buildDenseTiedRoot_rule4b_right_local mol state fuel
                                        rankedLeftFirst rankedRightFirst right]
                                        at firstFactor
                                      rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent
                                        mol state fuel rankedRightFirst right] at firstFactor
                                      cases first with
                                      | lt =>
                                          simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq,
                                            rankLeftEq, rankRightEq, firstEq] at computed
                                          subst decision
                                          simp [buildDenseRule4bProjectedKey,
                                            denseRule4bReferenceCountPriority,
                                            leftRefsEq, rightRefsEq,
                                            totalRankedOccurrenceRule4bReferences, rankLeftEq,
                                            rankRightEq, List.compareLex,
                                            firstFactor]
                                      | gt =>
                                          simp [compareOccurrenceRule4b?, leftRefsEq, rightRefsEq,
                                            rankLeftEq, rankRightEq, firstEq] at computed
                                          subst decision
                                          simp [buildDenseRule4bProjectedKey,
                                            denseRule4bReferenceCountPriority,
                                            leftRefsEq, rightRefsEq,
                                            totalRankedOccurrenceRule4bReferences, rankLeftEq,
                                            rankRightEq, List.compareLex,
                                            firstFactor]
                                      | eq =>
                                          cases secondEq : compareOccurrenceDescriptorAtTiedRoot?
                                              mol state fuel
                                              (.rule4b rankedLeftSecond rankedRightSecond) left right with
                                          | none =>
                                              simp [compareOccurrenceRule4b?, leftRefsEq,
                                                rightRefsEq, rankLeftEq, rankRightEq, firstEq,
                                                secondEq] at computed
                                          | some second =>
                                              have secondFactor :=
                                                compareOccurrenceDescriptorAtTiedRoot_success_factors
                                                  mol state fuel
                                                  (.rule4b rankedLeftSecond rankedRightSecond)
                                                    left right second
                                                  secondEq
                                              rw [buildDenseTiedRoot_rule4b_left_local mol state fuel
                                                rankedLeftSecond rankedRightSecond left]
                                                at secondFactor
                                              rw [buildDenseTiedRoot_rule4b_right_local mol state fuel
                                                rankedLeftSecond rankedRightSecond right]
                                                at secondFactor
                                              rw [← buildDenseTiedRoot_rule4b_same_reference_side_independent
                                                mol state fuel rankedRightSecond right]
                                                at secondFactor
                                              simp [compareOccurrenceRule4b?, leftRefsEq,
                                                rightRefsEq, rankLeftEq, rankRightEq, firstEq,
                                                secondEq] at computed
                                              subst decision
                                              simp [buildDenseRule4bProjectedKey,
                                                denseRule4bReferenceCountPriority, leftRefsEq,
                                                rightRefsEq, totalRankedOccurrenceRule4bReferences,
                                                rankLeftEq, rankRightEq, List.compareLex, firstFactor,
                                                secondFactor]
                                              cases second <;> rfl

abbrev DenseRule4cProjectedKey := DenseOccurrenceDescriptorKey

def buildDenseRule4cProjectedKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (cursor : CanonicalRerootCursor) : DenseRule4cProjectedKey :=
  let before := compareOccurrenceDescriptorBranchAt mol state fuel .rule4c
  buildDenseOccurrenceDescriptorKey mol state before fuel .rule4c true cursor

def compareDenseRule4cProjectedKeys :
    DenseRule4cProjectedKey → DenseRule4cProjectedKey → Ordering :=
  compareDenseOccurrenceDescriptorKeys

theorem compareDenseRule4cProjectedKeys_transCmp :
    Std.TransCmp compareDenseRule4cProjectedKeys :=
  compareDenseOccurrenceDescriptorKeys_transCmp

theorem compareOccurrenceRule4cPairLabelsWithWitness_ordering_eq
    (state : OccurrenceAuxState) : ∀ pairs,
    (compareOccurrenceRule4cPairLabelsWithWitness state pairs).ordering =
      compareOccurrenceDescriptorPairLabels state .rule4c pairs
  | [] => rfl
  | pair :: pairs => by
      simp only [compareOccurrenceRule4cPairLabelsWithWitness,
        compareOccurrenceDescriptorPairLabels]
      cases priorityEq : compare (occurrenceNodePriority state .rule4c true pair.1)
          (occurrenceNodePriority state .rule4c false pair.2) with
      | lt => rfl
      | gt => rfl
      | eq => exact compareOccurrenceRule4cPairLabelsWithWitness_ordering_eq state pairs

theorem compareOccurrenceRule4cWithWitness_implies_plain (mol : RawMolecule)
    (state : OccurrenceAuxState)
    (beforeLeft beforeRight :
      CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
    ∀ fuel pairs result,
    compareOccurrenceRule4cWithWitness mol state beforeLeft beforeRight fuel pairs =
      some result →
    compareOccurrenceDescriptorRule mol state beforeLeft beforeRight .rule4c fuel pairs =
      some result.ordering
  | 0, pairs, result, computed => by
      simp only [compareOccurrenceRule4cWithWitness,
        compareOccurrenceDescriptorRule] at computed ⊢
      by_cases tooWide : RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [tooWide] at computed
      · simp only [tooWide, ↓reduceIte] at computed ⊢
        cases witnessEq : compareOccurrenceRule4cPairLabelsWithWitness state pairs with
        | mk ordering carrier =>
            have orderingEq := compareOccurrenceRule4cPairLabelsWithWitness_ordering_eq state pairs
            rw [witnessEq] at orderingEq
            cases ordering with
            | lt =>
                simp [witnessEq] at computed
                subst result
                simp [← orderingEq]
            | gt =>
                simp [witnessEq] at computed
                subst result
                simp [← orderingEq]
            | eq =>
                cases nextEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs with
                | none => simp [witnessEq, nextEq] at computed
                | some next =>
                    cases next with
                    | nil =>
                        simp [witnessEq, nextEq] at computed
                        subst result
                        simp [← orderingEq, nextEq]
                    | cons head tail => simp [witnessEq, nextEq] at computed
  | fuel + 1, pairs, result, computed => by
      simp only [compareOccurrenceRule4cWithWitness,
        compareOccurrenceDescriptorRule] at computed ⊢
      by_cases tooWide : RawMolecule.defaultBranchWidthCap < pairs.length
      · simp [tooWide] at computed
      · simp only [tooWide, ↓reduceIte] at computed ⊢
        cases witnessEq : compareOccurrenceRule4cPairLabelsWithWitness state pairs with
        | mk ordering carrier =>
            have orderingEq := compareOccurrenceRule4cPairLabelsWithWitness_ordering_eq state pairs
            rw [witnessEq] at orderingEq
            cases ordering with
            | lt =>
                simp [witnessEq] at computed
                subst result
                simp [← orderingEq]
            | gt =>
                simp [witnessEq] at computed
                subst result
                simp [← orderingEq]
            | eq =>
                cases nextEq : nextOccurrenceDescriptorPairs? mol beforeLeft beforeRight pairs with
                | none => simp [witnessEq, nextEq] at computed
                | some next =>
                    cases next with
                    | nil =>
                        simp [witnessEq, nextEq] at computed
                        subst result
                        simp [← orderingEq, nextEq]
                    | cons head tail =>
                        have recursiveComputed :
                            compareOccurrenceRule4cWithWitness mol state beforeLeft beforeRight
                              fuel (head :: tail) = some result := by
                          simpa [witnessEq, nextEq] using computed
                        have recursive := compareOccurrenceRule4cWithWitness_implies_plain mol state
                          beforeLeft beforeRight fuel (head :: tail) result recursiveComputed
                        simp [← orderingEq, nextEq, recursive]

theorem compareOccurrenceRule4cWithWitness_ordering_success_factors (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (result : OccurrenceRule4cDecision)
    (computed : compareOccurrenceRule4cWithWitness mol state
      (compareOccurrenceDescriptorBranchAt mol state fuel .rule4c)
      (compareOccurrenceDescriptorBranchAt mol state fuel .rule4c)
      fuel [(left, right)] = some result) :
    compareDenseRule4cProjectedKeys
        (buildDenseRule4cProjectedKey mol state fuel left)
        (buildDenseRule4cProjectedKey mol state fuel right) = result.ordering := by
  let before := compareOccurrenceDescriptorBranchAt mol state fuel .rule4c
  have plain := compareOccurrenceRule4cWithWitness_implies_plain mol state before before fuel
    [(left, right)] result (by simpa [before] using computed)
  have factored := compareOccurrenceDescriptorRule_singleton_success_factors mol state
    before before .rule4c fuel left right result.ordering plain
  have rightKeyEq :
      buildDenseOccurrenceDescriptorKey mol state before fuel .rule4c true right =
        buildDenseOccurrenceDescriptorKey mol state before fuel .rule4c false right := by
    unfold buildDenseOccurrenceDescriptorKey descriptorPrioritySequence
    rw [occurrenceNodePriority_rule4c_side_independent state]
  rw [← rightKeyEq] at factored
  simpa [compareDenseRule4cProjectedKeys, buildDenseRule4cProjectedKey, before] using factored

abbrev DenseProductionRule4cKey := List DenseRule4cProjectedKey

def buildDenseProductionRule4cKey (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (cursor : CanonicalRerootCursor) : DenseProductionRule4cKey :=
  if state.any fun fact => !fact.uppercase then
    [buildDenseRule4cProjectedKey mol state fuel cursor]
  else []

def compareDenseProductionRule4cKeys :
    DenseProductionRule4cKey → DenseProductionRule4cKey → Ordering :=
  List.compareLex compareDenseRule4cProjectedKeys

theorem compareDenseProductionRule4cKeys_transCmp :
    Std.TransCmp compareDenseProductionRule4cKeys := by
  unfold compareDenseProductionRule4cKeys
  letI := compareDenseRule4cProjectedKeys_transCmp
  infer_instance

/-! ## Structural completeness for terminal constitution-only ligands -/

/-- Descriptor comparison of two terminal roots with no local auxiliary fact always reaches an
equality result.  Auxiliary facts elsewhere in the molecule are allowed: terminality prevents the
comparison from traversing to them. -/
theorem compareOccurrenceDescriptorAtTiedRoot?_terminal_silent_eq (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (stage : RawDescriptorRuleStage) (left right : CanonicalRerootCursor)
    (leftTerminal : cursorTerminal mol left = true)
    (rightTerminal : cursorTerminal mol right = true)
    (leftSilent : state.factAt? left.node = none)
    (rightSilent : state.factAt? right.node = none) :
    compareOccurrenceDescriptorAtTiedRoot? mol state fuel stage left right = some .eq := by
  have leftChildren := cursor_children_eq_nil_of_terminal mol left leftTerminal
  have rightChildren := cursor_children_eq_nil_of_terminal mol right rightTerminal
  cases fuel <;> cases stage <;>
    simp [compareOccurrenceDescriptorAtTiedRoot?, compareOccurrenceDescriptorRule,
      compareOccurrenceDescriptorPairLabels, nextOccurrenceDescriptorPairs?,
      occurrenceNodePriority, cursorTerminal, leftChildren, rightChildren,
      leftSilent, rightSilent, RawMolecule.defaultBranchWidthCap]

/-- Rule 4b discovers no reference descriptor at a terminal root with no local auxiliary fact. -/
theorem occurrenceRule4bReferences_terminal_silent_eq_nil (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (root : CanonicalRerootCursor)
    (terminal : cursorTerminal mol root = true)
    (silent : state.factAt? root.node = none) :
    occurrenceRule4bReferences mol state fuel [root] = [] := by
  have children := cursor_children_eq_nil_of_terminal mol root terminal
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have nilEq : occurrenceRule4bReferences mol state fuel [] = [] := by
        cases fuel <;> rfl
      cases provenanceEq : root.node.provenance <;>
        simp [occurrenceRule4bReferences, provenanceEq, silent, children, nilEq]

/-- The witness-retaining Rule-4c pass is likewise total and tied on locally silent terminal
roots, independently of the recursive callback supplied by its caller. -/
theorem compareOccurrenceRule4cWithWitness_terminal_silent_eq (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (left right : CanonicalRerootCursor)
    (leftTerminal : cursorTerminal mol left = true)
    (rightTerminal : cursorTerminal mol right = true)
    (leftSilent : state.factAt? left.node = none)
    (rightSilent : state.factAt? right.node = none) :
    compareOccurrenceRule4cWithWitness mol state before before fuel [(left, right)] =
      some { ordering := .eq } := by
  have leftChildren := cursor_children_eq_nil_of_terminal mol left leftTerminal
  have rightChildren := cursor_children_eq_nil_of_terminal mol right rightTerminal
  cases fuel <;>
    simp [compareOccurrenceRule4cWithWitness, compareOccurrenceRule4cPairLabelsWithWitness,
      nextOccurrenceDescriptorPairs?, occurrenceNodePriority, cursorTerminal,
      leftChildren, rightChildren, leftSilent, rightSilent,
      RawMolecule.defaultBranchWidthCap]

/-- Structural pairwise completeness for the actual Rules-1--5 production comparator.

For two terminal roots, supported Rule-1a labels eliminate label refusal, empty child spheres
eliminate fuel/frontier/sibling refusal, local descriptor silence makes Rules 4a--5 total, and an
acyclic left root makes the pairwise automorphism-conflict gate definitionally impossible.  The
successful production ordering is exactly the raw constitutional ordering; no successful
comparison occurs among the assumptions. -/
theorem compareOccurrenceBranches?_terminal_supported_silent_of_left_acyclic
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (leftTerminal : cursorTerminal mol left = true)
    (rightTerminal : cursorTerminal mol right = true)
    (leftAcyclic : mol.atomLiesInCycle fuel left.node.atom = false)
    (leftLabel : ∃ label, mol.canonicalRule1aLabel? left.node = some label)
    (rightLabel : ∃ label, mol.canonicalRule1aLabel? right.node = some label)
    (leftSilent : state.factAt? left.node = none)
    (rightSilent : state.factAt? right.node = none) :
    ∃ ordering,
      compareCursorBranchAt mol fuel .rule2 left right = some ordering ∧
      compareOccurrenceBranches? mol state fuel left right =
        some { ordering := ordering } := by
  rcases
      ProductionCIPRerootComparatorLaws.compareCursorBranchAt_terminal_supported_exists
        mol fuel left right leftTerminal rightTerminal leftLabel rightLabel with
    ⟨ordering, rawEq⟩
  have gateFalse : occurrenceRootsProvedAutomorphic mol fuel left right ordering = false := by
    simp [occurrenceRootsProvedAutomorphic, leftAcyclic]
  have constitutionalEq : certifiedConstitutionalStage? mol fuel left right = some ordering := by
    simp [certifiedConstitutionalStage?, rawEq, gateFalse]
  refine ⟨ordering, rawEq, ?_⟩
  cases ordering with
  | lt => simp [compareOccurrenceBranches?, constitutionalEq]
  | gt => simp [compareOccurrenceBranches?, constitutionalEq]
  | eq =>
      have rule4aEq := compareOccurrenceDescriptorAtTiedRoot?_terminal_silent_eq
        mol state fuel .rule4a left right leftTerminal rightTerminal leftSilent rightSilent
      have rule5REq := compareOccurrenceDescriptorAtTiedRoot?_terminal_silent_eq
        mol state fuel (.rule5 .R .R) left right leftTerminal rightTerminal
          leftSilent rightSilent
      have rule5SEq := compareOccurrenceDescriptorAtTiedRoot?_terminal_silent_eq
        mol state fuel (.rule5 .S .S) left right leftTerminal rightTerminal
          leftSilent rightSilent
      have rule4bEq : compareOccurrenceRule4b? mol state fuel left right = some .eq := by
        simp [compareOccurrenceRule4b?,
          occurrenceRule4bReferences_terminal_silent_eq_nil
            mol state fuel left leftTerminal leftSilent,
          occurrenceRule4bReferences_terminal_silent_eq_nil
            mol state fuel right rightTerminal rightSilent]
      have rule5Eq : compareOccurrenceRule5? mol state fuel left right =
          some { ordering := .eq, pseudo := false } := by
        simp [compareOccurrenceRule5?, rule5REq, rule5SEq]
      cases anyLower : state.any fun fact => !fact.uppercase with
      | false =>
          simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq,
            anyLower, rule5Eq]
      | true =>
          have rule4cEq := compareOccurrenceRule4cWithWitness_terminal_silent_eq
            mol state fuel (compareOccurrenceDescriptorBranchAt mol state fuel .rule4c)
              left right leftTerminal rightTerminal leftSilent rightSilent
          simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq,
            anyLower, rule4cEq, rule5Eq]

/-- Partial composition of two known comparison outcomes.  Oppositely directed strict results do
not determine the endpoints. -/
def composeSuccessfulOrdering? : Ordering → Ordering → Option Ordering
  | .eq, ordering | ordering, .eq => some ordering
  | .gt, .gt => some .gt
  | .lt, .lt => some .lt
  | .gt, .lt | .lt, .gt => none

/-- Minimal interface required from a complete occurrence-key construction.

`factor` is deliberately conditional only on a successful production comparison.  It does not
assert that `compareOccurrenceBranches?` is total on arbitrary cursors. -/
structure SuccessfulOccurrenceOrderingKeyAPI (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) where
  Key : Type
  build : CanonicalRerootCursor → Key
  compare : Key → Key → Ordering
  lawful : Std.TransCmp compare
  factor : ∀ left right result,
    compareOccurrenceBranches? mol state fuel left right = some result →
      compare (build left) (build right) = result.ordering

namespace SuccessfulOccurrenceOrderingKeyAPI

variable {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : ℕ}

/-- Honest arbitrary-cursor transitivity: all three production comparisons are assumed successful.
No endpoint `Option` is synthesized. -/
theorem compareOccurrenceBranches_ordering_isLE_trans_of_three_success
    (api : SuccessfulOccurrenceOrderingKeyAPI mol state fuel)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : OccurrenceComparison}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (leftMiddleLE : leftMiddle.ordering.isLE)
    (middleRightLE : middleRight.ordering.isLE) :
    leftRight.ordering.isLE := by
  letI := api.lawful
  have keyLeftMiddle : (api.compare (api.build left) (api.build middle)).isLE := by
    rw [api.factor left middle leftMiddle leftMiddleEq]
    exact leftMiddleLE
  have keyMiddleRight : (api.compare (api.build middle) (api.build right)).isLE := by
    rw [api.factor middle right middleRight middleRightEq]
    exact middleRightLE
  have keyLeftRight : (api.compare (api.build left) (api.build right)).isLE :=
    Std.TransCmp.isLE_trans keyLeftMiddle keyMiddleRight
  rw [api.factor left right leftRight leftRightEq] at keyLeftRight
  exact keyLeftRight

/-- Strict-left strengthening of the preceding theorem. -/
theorem compareOccurrenceBranches_ordering_lt_of_lt_of_isLE_three_success
    (api : SuccessfulOccurrenceOrderingKeyAPI mol state fuel)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : OccurrenceComparison}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (leftMiddleLT : leftMiddle.ordering = .lt)
    (middleRightLE : middleRight.ordering.isLE) :
    leftRight.ordering = .lt := by
  letI := api.lawful
  have keyLeftMiddle : api.compare (api.build left) (api.build middle) = .lt := by
    rw [api.factor left middle leftMiddle leftMiddleEq]
    exact leftMiddleLT
  have keyMiddleRight : (api.compare (api.build middle) (api.build right)).isLE := by
    rw [api.factor middle right middleRight middleRightEq]
    exact middleRightLE
  have keyLeftRight : api.compare (api.build left) (api.build right) = .lt :=
    Std.TransCmp.lt_of_lt_of_isLE keyLeftMiddle keyMiddleRight
  rw [api.factor left right leftRight leftRightEq] at keyLeftRight
  exact keyLeftRight

/-- Every defined `composeOrdering?` outcome is the actual endpoint comparison for a lawful key. -/
theorem compare_composeOrdering_of_lawful_key
    (api : SuccessfulOccurrenceOrderingKeyAPI mol state fuel)
    {left middle right : CanonicalRerootCursor} {composed : Ordering}
    (composition : composeSuccessfulOrdering?
      (api.compare (api.build left) (api.build middle))
      (api.compare (api.build middle) (api.build right)) = some composed) :
    api.compare (api.build left) (api.build right) = composed := by
  letI := api.lawful
  cases leftMiddleEq : api.compare (api.build left) (api.build middle) <;>
    cases middleRightEq : api.compare (api.build middle) (api.build right) <;>
    simp [composeSuccessfulOrdering?, leftMiddleEq, middleRightEq] at composition <;>
    subst composed
  · exact Std.TransCmp.lt_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_lt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_eq_of_lt leftMiddleEq middleRightEq
  · exact Std.TransCmp.eq_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_eq_of_gt leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_gt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_trans leftMiddleEq middleRightEq

/-- Production-facing composition theorem, again requiring all three successful endpoints. -/
theorem compareOccurrenceBranches_ordering_compose_of_three_success
    (api : SuccessfulOccurrenceOrderingKeyAPI mol state fuel)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : OccurrenceComparison}
    {composed : Ordering}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    leftRight.ordering = composed := by
  have keyComposition : composeSuccessfulOrdering?
      (api.compare (api.build left) (api.build middle))
      (api.compare (api.build middle) (api.build right)) = some composed := by
    rw [api.factor left middle leftMiddle leftMiddleEq,
      api.factor middle right middleRight middleRightEq]
    exact composition
  have endpoint := compare_composeOrdering_of_lawful_key api keyComposition
  rw [api.factor left right leftRight leftRightEq] at endpoint
  exact endpoint

end SuccessfulOccurrenceOrderingKeyAPI

/-! ## Certified fail-closed production-key instantiation -/

structure FailClosedOccurrenceBranchProjectedKey where
  constitutional : ProductionCIPRerootComparatorLaws.DenseRerootKey
  rule4a : DenseRule4aProjectedKey
  rule4b : DenseRule4bProjectedKey
  rule4c : DenseProductionRule4cKey
  rule5 : DenseRule5ProjectedKey

def buildFailClosedOccurrenceBranchProjectedKey (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    (cursor : CanonicalRerootCursor) : FailClosedOccurrenceBranchProjectedKey :=
  { constitutional := ProductionCIPRerootComparatorLaws.buildDenseRerootKey mol fuel cursor
    rule4a := buildDenseRule4aProjectedKey mol state fuel cursor
    rule4b := buildDenseRule4bProjectedKey mol state fuel cursor
    rule4c := buildDenseProductionRule4cKey mol state fuel cursor
    rule5 := buildDenseRule5ProjectedKey mol state fuel cursor }

def compareFailClosedOccurrenceBranchProjectedKeys
    (left right : FailClosedOccurrenceBranchProjectedKey) : Ordering :=
  compareLex
    (Ordering.byKey FailClosedOccurrenceBranchProjectedKey.constitutional
      ProductionCIPRerootComparatorLaws.compareDenseRerootKeys)
    (compareLex
      (Ordering.byKey FailClosedOccurrenceBranchProjectedKey.rule4a
        compareDenseRule4aProjectedKeys)
      (compareLex
        (Ordering.byKey FailClosedOccurrenceBranchProjectedKey.rule4b
          compareDenseRule4bProjectedKeys)
        (compareLex
          (Ordering.byKey FailClosedOccurrenceBranchProjectedKey.rule4c
            compareDenseProductionRule4cKeys)
          (Ordering.byKey FailClosedOccurrenceBranchProjectedKey.rule5
            compareDenseRule5ProjectedKeys)))) left right

theorem compareFailClosedOccurrenceBranchProjectedKeys_transCmp :
    Std.TransCmp compareFailClosedOccurrenceBranchProjectedKeys := by
  unfold compareFailClosedOccurrenceBranchProjectedKeys
  letI := ProductionCIPRerootComparatorLaws.compareDenseRerootKeys_transCmp
  letI := compareDenseRule4aProjectedKeys_transCmp
  letI := compareDenseRule4bProjectedKeys_transCmp
  letI := compareDenseProductionRule4cKeys_transCmp
  letI := compareDenseRule5ProjectedKeys_transCmp
  infer_instance

/-- Every successful production occurrence comparison factors through the complete raw unary key.
Automorphism conflicts and unsupported comparisons remain outside the theorem's boundary. -/
theorem compareOccurrenceBranches_ordering_success_failClosed_factors
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ) :
    ∀ left right comparison,
    compareOccurrenceBranches? mol state fuel left right = some comparison →
      compareFailClosedOccurrenceBranchProjectedKeys
        (buildFailClosedOccurrenceBranchProjectedKey mol state fuel left)
        (buildFailClosedOccurrenceBranchProjectedKey mol state fuel right) =
          comparison.ordering := by
  intro left right comparison computed
  cases constitutionalEq : certifiedConstitutionalStage? mol fuel left right with
  | none => simp [compareOccurrenceBranches?, constitutionalEq] at computed
  | some constitutional =>
      have constitutionalFactor :=
        ProductionCIPRerootComparatorLaws.certifiedConstitutionalStage?_success_dense_factors
            mol fuel left right constitutional constitutionalEq
      cases constitutional with
      | lt =>
          simp [compareOccurrenceBranches?, constitutionalEq] at computed
          subst comparison
          simp [compareFailClosedOccurrenceBranchProjectedKeys, compareLex, Ordering.byKey,
            buildFailClosedOccurrenceBranchProjectedKey, constitutionalFactor]
      | gt =>
          simp [compareOccurrenceBranches?, constitutionalEq] at computed
          subst comparison
          simp [compareFailClosedOccurrenceBranchProjectedKeys, compareLex, Ordering.byKey,
            buildFailClosedOccurrenceBranchProjectedKey, constitutionalFactor]
      | eq =>
          cases rule4aEq : compareOccurrenceDescriptorAtTiedRoot? mol state fuel .rule4a
              left right with
          | none =>
              simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq] at computed
          | some rule4a =>
              have rule4aFactor := compareOccurrenceRule4a_tied_success_factors mol state fuel
                left right rule4a rule4aEq
              cases rule4a with
              | lt =>
                  simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq] at computed
                  subst comparison
                  simp [compareFailClosedOccurrenceBranchProjectedKeys, compareLex,
                    Ordering.byKey, buildFailClosedOccurrenceBranchProjectedKey,
                    constitutionalFactor, rule4aFactor]
              | gt =>
                  simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq] at computed
                  subst comparison
                  simp [compareFailClosedOccurrenceBranchProjectedKeys, compareLex,
                    Ordering.byKey, buildFailClosedOccurrenceBranchProjectedKey,
                    constitutionalFactor, rule4aFactor]
              | eq =>
                  cases rule4bEq : compareOccurrenceRule4b? mol state fuel left right with
                  | none =>
                      simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq]
                        at computed
                  | some rule4b =>
                      have rule4bFactor := compareOccurrenceRule4b_success_factors mol state fuel
                        left right rule4b rule4bEq
                      cases rule4b with
                      | lt =>
                          simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq]
                            at computed
                          subst comparison
                          simp [compareFailClosedOccurrenceBranchProjectedKeys, compareLex,
                            Ordering.byKey, buildFailClosedOccurrenceBranchProjectedKey,
                            constitutionalFactor, rule4aFactor, rule4bFactor]
                      | gt =>
                          simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq, rule4bEq]
                            at computed
                          subst comparison
                          simp [compareFailClosedOccurrenceBranchProjectedKeys, compareLex,
                            Ordering.byKey, buildFailClosedOccurrenceBranchProjectedKey,
                            constitutionalFactor, rule4aFactor, rule4bFactor]
                      | eq =>
                          cases lowercase : state.any fun fact => !fact.uppercase
                          · cases rule5Eq : compareOccurrenceRule5? mol state fuel left right with
                            | none =>
                                simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq,
                                  rule4bEq, lowercase, rule5Eq] at computed
                            | some rule5 =>
                                have rule5Factor :=
                                  compareOccurrenceRule5_ordering_success_factors mol state fuel
                                    left right rule5 rule5Eq
                                simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq,
                                  rule4bEq, lowercase, rule5Eq] at computed
                                subst comparison
                                simp [compareFailClosedOccurrenceBranchProjectedKeys, compareLex,
                                  Ordering.byKey, buildFailClosedOccurrenceBranchProjectedKey,
                                  buildDenseProductionRule4cKey,
                                  compareDenseProductionRule4cKeys, constitutionalFactor,
                                  rule4aFactor, rule4bFactor, lowercase, rule5Factor,
                                  List.compareLex]
                          · let before :=
                                compareOccurrenceDescriptorBranchAt mol state fuel .rule4c
                            cases rule4cEq : compareOccurrenceRule4cWithWitness mol state before
                                before fuel [(left, right)] with
                            | none =>
                                simp [compareOccurrenceBranches?, constitutionalEq, rule4aEq,
                                  rule4bEq, lowercase, before, rule4cEq] at computed
                            | some rule4c =>
                                have rule4cFactor :=
                                  compareOccurrenceRule4cWithWitness_ordering_success_factors
                                    mol state fuel left right rule4c
                                    (by simpa [before] using rule4cEq)
                                cases rule4c with
                                | mk rule4cOrdering rule4cCarrier =>
                                  cases rule4cOrdering with
                                  | lt =>
                                      simp [compareOccurrenceBranches?, constitutionalEq,
                                        rule4aEq, rule4bEq, lowercase, before, rule4cEq] at computed
                                      subst comparison
                                      simp [compareFailClosedOccurrenceBranchProjectedKeys,
                                        compareLex, Ordering.byKey,
                                        buildFailClosedOccurrenceBranchProjectedKey,
                                        buildDenseProductionRule4cKey,
                                        compareDenseProductionRule4cKeys, constitutionalFactor,
                                        rule4aFactor, rule4bFactor, rule4cFactor, lowercase,
                                        List.compareLex]
                                  | gt =>
                                      simp [compareOccurrenceBranches?, constitutionalEq,
                                        rule4aEq, rule4bEq, lowercase, before, rule4cEq] at computed
                                      subst comparison
                                      simp [compareFailClosedOccurrenceBranchProjectedKeys,
                                        compareLex, Ordering.byKey,
                                        buildFailClosedOccurrenceBranchProjectedKey,
                                        buildDenseProductionRule4cKey,
                                        compareDenseProductionRule4cKeys, constitutionalFactor,
                                        rule4aFactor, rule4bFactor, rule4cFactor, lowercase,
                                        List.compareLex]
                                  | eq =>
                                      cases rule5Eq : compareOccurrenceRule5? mol state fuel left
                                          right with
                                      | none =>
                                          simp [compareOccurrenceBranches?, constitutionalEq,
                                            rule4aEq, rule4bEq, lowercase, before, rule4cEq,
                                            rule5Eq] at computed
                                      | some rule5 =>
                                          have rule5Factor :=
                                            compareOccurrenceRule5_ordering_success_factors mol
                                              state fuel left right rule5 rule5Eq
                                          simp [compareOccurrenceBranches?, constitutionalEq,
                                            rule4aEq, rule4bEq, lowercase, before, rule4cEq,
                                            rule5Eq] at computed
                                          subst comparison
                                          simp [compareFailClosedOccurrenceBranchProjectedKeys,
                                            compareLex, Ordering.byKey,
                                            buildFailClosedOccurrenceBranchProjectedKey,
                                            buildDenseProductionRule4cKey,
                                            compareDenseProductionRule4cKeys,
                                            constitutionalFactor, rule4aFactor, rule4bFactor,
                                            rule4cFactor, rule5Factor, lowercase, List.compareLex]

def failClosedOccurrenceOrderingAPI (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) :
    SuccessfulOccurrenceOrderingKeyAPI mol state fuel where
  Key := FailClosedOccurrenceBranchProjectedKey
  build := buildFailClosedOccurrenceBranchProjectedKey mol state fuel
  compare := compareFailClosedOccurrenceBranchProjectedKeys
  lawful := compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  factor := compareOccurrenceBranches_ordering_success_failClosed_factors mol state fuel

/-- Honest arbitrary-cursor transitivity for three successful production comparisons. -/
theorem compareOccurrenceBranches_ordering_isLE_trans_failClosed_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : OccurrenceComparison}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (leftMiddleLE : leftMiddle.ordering.isLE)
    (middleRightLE : middleRight.ordering.isLE) :
    leftRight.ordering.isLE :=
  SuccessfulOccurrenceOrderingKeyAPI.compareOccurrenceBranches_ordering_isLE_trans_of_three_success
      (failClosedOccurrenceOrderingAPI mol state fuel)
      leftMiddleEq middleRightEq leftRightEq leftMiddleLE middleRightLE

/-- If the first successful comparison is strict and the second is nonincreasing, the successful
endpoint comparison is strict in the same direction. -/
theorem compareOccurrenceBranches_ordering_lt_of_lt_of_isLE_failClosed_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : OccurrenceComparison}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (leftMiddleLT : leftMiddle.ordering = .lt)
    (middleRightLE : middleRight.ordering.isLE) :
    leftRight.ordering = .lt :=
  SuccessfulOccurrenceOrderingKeyAPI.compareOccurrenceBranches_ordering_lt_of_lt_of_isLE_three_success
      (failClosedOccurrenceOrderingAPI mol state fuel)
      leftMiddleEq middleRightEq leftRightEq leftMiddleLT middleRightLE

/-- Composition form with the same honest three-success boundary. -/
theorem compareOccurrenceBranches_ordering_compose_failClosed_of_three_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight leftRight : OccurrenceComparison}
    {composed : Ordering}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle = some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right = some middleRight)
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    leftRight.ordering = composed :=
  SuccessfulOccurrenceOrderingKeyAPI.compareOccurrenceBranches_ordering_compose_of_three_success
    (failClosedOccurrenceOrderingAPI mol state fuel)
    leftMiddleEq middleRightEq leftRightEq composition

/-! ## Orientational antisymmetry of the fail-closed occurrence comparison

Every successful production occurrence comparison factors through the unary projected key
(`compareOccurrenceBranches_ordering_success_failClosed_factors`).  That key is a `Std.TransCmp`,
hence an oriented comparator, so swapping the two key arguments swaps the reported ordering.  The
partial executable comparator inherits this antisymmetry on pairs where *both* directions succeed.

The production theorem below is deliberately conditional on the reverse call succeeding as well.
It does not assert reverse success: `OccurrenceComparatorRegression` refutes two-success endpoint
closure for the raw comparator, and the fail-closed automorphism gate can refuse both directions of
one pair, so no unconditional reversal theorem is available.  It also does not identify `none` with
any ordering value.  The scientific reading of a strict result therefore remains pair-directed: a
`gt` from `left` to `right` is not by itself evidence about any third cursor or about a collapsed
tie. -/

/-- `Ordering.swap` is an involution. -/
@[simp] theorem ordering_swap_swap (ordering : Ordering) :
    ordering.swap.swap = ordering := by
  cases ordering <;> rfl

/-- Every oriented comparator is skew-symmetric in its two arguments: for a total lawful
comparison, swapping the arguments swaps the reported ordering. -/
theorem orientedOrdering_swap_eq {alpha : Type*} {cmp : alpha → alpha → Ordering}
    (lawful : Std.TransCmp cmp) (left right : alpha) :
    cmp left right = (cmp right left).swap := by
  letI := lawful
  exact Std.OrientedCmp.eq_swap

/-- The certified fail-closed projected key is skew-symmetric.  This is the
antisymmetry of the ordering that every successful production occurrence comparison factors
through. -/
theorem compareFailClosedOccurrenceBranchProjectedKeys_swap
    (left right : FailClosedOccurrenceBranchProjectedKey) :
    compareFailClosedOccurrenceBranchProjectedKeys left right =
      (compareFailClosedOccurrenceBranchProjectedKeys right left).swap :=
  orientedOrdering_swap_eq (cmp := compareFailClosedOccurrenceBranchProjectedKeys)
    compareFailClosedOccurrenceBranchProjectedKeys_transCmp left right

/-- Production-facing antisymmetry on pairs where both directed calls succeed: comparing `right` to
`left` yields the swap of comparing `left` to `right`.  Both successful calls are premises; neither
direction is inferred from the other. -/
theorem compareOccurrenceBranches_ordering_swap_of_two_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    {left right : CanonicalRerootCursor}
    {leftRight rightLeft : OccurrenceComparison}
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (rightLeftEq : compareOccurrenceBranches? mol state fuel right left = some rightLeft) :
    rightLeft.ordering = leftRight.ordering.swap := by
  have keySwap := compareFailClosedOccurrenceBranchProjectedKeys_swap
    (buildFailClosedOccurrenceBranchProjectedKey mol state fuel left)
    (buildFailClosedOccurrenceBranchProjectedKey mol state fuel right)
  have leftFactor := compareOccurrenceBranches_ordering_success_failClosed_factors
    mol state fuel left right leftRight leftRightEq
  have rightFactor := compareOccurrenceBranches_ordering_success_failClosed_factors
    mol state fuel right left rightLeft rightLeftEq
  rw [leftFactor, rightFactor] at keySwap
  rw [keySwap]
  exact (ordering_swap_swap rightLeft.ordering).symm

/-- Applicability form of the antisymmetry law: on two successful opposite calls, a strict `gt`
from `left` to `right` forces the reverse call to report `lt`.  Neither the reverse success nor the
`lt` is available from `leftRight` alone. -/
theorem compareOccurrenceBranches_ordering_lt_reverse_of_gt_two_success
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    {left right : CanonicalRerootCursor}
    {leftRight rightLeft : OccurrenceComparison}
    (leftRightEq : compareOccurrenceBranches? mol state fuel left right = some leftRight)
    (rightLeftEq : compareOccurrenceBranches? mol state fuel right left = some rightLeft)
    (strict : leftRight.ordering = Ordering.gt) :
    rightLeft.ordering = Ordering.lt := by
  have swapLaw := compareOccurrenceBranches_ordering_swap_of_two_success
    mol state fuel leftRightEq rightLeftEq
  rw [strict] at swapLaw
  simpa [Ordering.swap] using swapLaw

/-! ## Conditional endpoint existence from unary compilation

The successful-factor theorems above prove only partial correctness: whenever the executable
comparator succeeds, its ordering is the lawful unary-key comparison.  They do not prove the
reverse implication that comparing two totalized keys makes the executable comparator succeed.

The interface below isolates the additional completeness boundary.  A unary compiler assigns a
domain tag and lawful key to each supported cursor.  Two compiled cursors in the same domain must
be executable-comparable.  No concrete production instance is declared here: the current
short-circuit comparator may succeed before later stages have been compiled, and its pair-specific
automorphism-conflict refusal is not implied by unary support alone. -/

/-- Unary compilation into independently total comparison domains.  Domain equality is the only
pairwise support condition; `compile_key` connects the compiler output to the already proved lawful
key rather than introducing a second ordering semantics. -/
structure UnaryDomainTotalOccurrenceOrderingAPI (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ)
    extends SuccessfulOccurrenceOrderingKeyAPI mol state fuel where
  Domain : Type
  compile? : CanonicalRerootCursor → Option (Domain × Key)
  compile_key : ∀ cursor domain key,
    compile? cursor = some (domain, key) → key = build cursor
  pair_complete : ∀ left right domain leftKey rightKey,
    compile? left = some (domain, leftKey) →
    compile? right = some (domain, rightKey) →
    ∃ comparison,
      compareOccurrenceBranches? mol state fuel left right = some comparison

namespace UnaryDomainTotalOccurrenceOrderingAPI

variable {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : ℕ}

/-- Logical minimum for eliminating the AC-success premise: unary certificates place A and C in
one total comparison domain.  Successful AB and BC comparisons plus their defined lawful
composition then determine the newly obtained AC result. -/
theorem endpoint_exists_and_eq_composed
    (api : UnaryDomainTotalOccurrenceOrderingAPI mol state fuel)
    {left middle right : CanonicalRerootCursor}
    {domain : api.Domain} {leftKey rightKey : api.Key}
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (leftCompiled : api.compile? left = some (domain, leftKey))
    (rightCompiled : api.compile? right = some (domain, rightKey))
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle =
      some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right =
      some middleRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol state fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases api.pair_complete left right domain leftKey rightKey
      leftCompiled rightCompiled with ⟨leftRight, leftRightEq⟩
  refine ⟨leftRight, leftRightEq, ?_⟩
  exact
    SuccessfulOccurrenceOrderingKeyAPI.compareOccurrenceBranches_ordering_compose_of_three_success
      api.toSuccessfulOccurrenceOrderingKeyAPI leftMiddleEq middleRightEq leftRightEq composition

/-- Optional stronger closure law: every successful pair has fully compiled endpoints in one
common domain.  Current production short-circuit success does not establish this proposition. -/
def SuccessCompilesInOneDomain
    (api : UnaryDomainTotalOccurrenceOrderingAPI mol state fuel) : Prop :=
  ∀ left right comparison,
    compareOccurrenceBranches? mol state fuel left right = some comparison →
    ∃ domain leftKey rightKey,
      api.compile? left = some (domain, leftKey) ∧
        api.compile? right = some (domain, rightKey)

/-- Under the explicitly named success-closure law, AB and BC success force A, B, and C into the
same deterministic unary domain: the two compiler results for B are equal.  AC therefore exists
and has the correct composed ordering without an AC-success premise. -/
theorem endpoint_exists_and_eq_composed_of_adjacent_success
    (api : UnaryDomainTotalOccurrenceOrderingAPI mol state fuel)
    (successCompiles : SuccessCompilesInOneDomain api)
    {left middle right : CanonicalRerootCursor}
    {leftMiddle middleRight : OccurrenceComparison} {composed : Ordering}
    (leftMiddleEq : compareOccurrenceBranches? mol state fuel left middle =
      some leftMiddle)
    (middleRightEq : compareOccurrenceBranches? mol state fuel middle right =
      some middleRight)
    (composition : composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering =
      some composed) :
    ∃ leftRight,
      compareOccurrenceBranches? mol state fuel left right = some leftRight ∧
        leftRight.ordering = composed := by
  rcases successCompiles left middle leftMiddle leftMiddleEq with
    ⟨leftDomain, leftKey, middleKeyFromLeft, leftCompiled, middleCompiledFromLeft⟩
  rcases successCompiles middle right middleRight middleRightEq with
    ⟨rightDomain, middleKeyFromRight, rightKey, middleCompiledFromRight, rightCompiled⟩
  have middleCompilationEq :
      (leftDomain, middleKeyFromLeft) = (rightDomain, middleKeyFromRight) :=
    Option.some.inj (middleCompiledFromLeft.symm.trans middleCompiledFromRight)
  cases middleCompilationEq
  exact endpoint_exists_and_eq_composed api leftCompiled rightCompiled
    leftMiddleEq middleRightEq composition

end UnaryDomainTotalOccurrenceOrderingAPI


end TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws
