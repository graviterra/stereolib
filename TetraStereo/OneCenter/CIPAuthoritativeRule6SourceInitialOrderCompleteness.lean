import TetraStereo.OneCenter.CIPAuthoritativeRule6Scheduler

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open AuthoritativeCIPCursorSupport
open AuthoritativeCIPOccurrenceCompleteness
open AuthoritativeCIPOccurrenceCompleteness.DescriptorRule6HierarchySupport
open AuthoritativeCIPOccurrenceDescriptorComparatorLaws
open AuthoritativeCIPRule6Completeness

/-!
# Exact orderedness of the uncapped source Rule-6 initial partition

The executable source scheduler uses stable insertion sort, but previously its chemical
completeness theorem separately assumed that the resulting adjacent comparisons contained no
`lt`.  This module derives that fact from the already certified unary-key factorization of every
successful unrestricted Rules-1a--5 occurrence comparison.
-/

/-- A harmless total cursor used only outside the in-range domain.  Every theorem connecting this
key to the source comparator assumes the corresponding position is in range, so this value is
never chemically observed. -/
private def fallbackInitialPositionCursor : CanonicalRerootCursor :=
  { node := canonicalCenterRoot 0 }

/-- Total unary key for a source-frame position.  In-range positions map to exactly the cursor key
through which the unrestricted authoritative comparator has already been proved to factor. -/
private def authoritativeInitialPositionKey (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (position : Nat) : FailClosedOccurrenceBranchProjectedKey :=
  buildFailClosedOccurrenceBranchProjectedKey mol state fuel
    ((roots[position]?).getD fallbackInitialPositionCursor)

/-- Nonincreasing order on source-frame positions, pulled back from the complete lawful unary
occurrence key. -/
def AuthoritativeInitialPositionGE (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (left right : Nat) : Prop :=
  compareFailClosedOccurrenceBranchProjectedKeys
      (authoritativeInitialPositionKey mol state fuel roots left)
      (authoritativeInitialPositionKey mol state fuel roots right) ≠ Ordering.lt

private instance authoritativeInitialPositionGE_decidable
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    DecidableRel (AuthoritativeInitialPositionGE mol state fuel roots) :=
  fun _left _right => by
    unfold AuthoritativeInitialPositionGE
    infer_instance

private theorem authoritativeInitialPositionGE_total
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    Std.Total (AuthoritativeInitialPositionGE mol state fuel roots) := by
  let cmp : Nat → Nat → Ordering := Ordering.byKey
    (authoritativeInitialPositionKey mol state fuel roots)
    compareFailClosedOccurrenceBranchProjectedKeys
  letI : Std.TransCmp compareFailClosedOccurrenceBranchProjectedKeys :=
    compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  letI : Std.TransCmp cmp := inferInstanceAs
    (Std.TransCmp (Ordering.byKey
      (authoritativeInitialPositionKey mol state fuel roots)
      compareFailClosedOccurrenceBranchProjectedKeys))
  constructor
  intro left right
  cases comparisonEq : cmp left right with
  | lt =>
      right
      change cmp right left ≠ Ordering.lt
      intro reverseEq
      have swapped := Std.OrientedCmp.eq_swap (cmp := cmp) (a := left) (b := right)
      rw [comparisonEq, reverseEq] at swapped
      cases swapped
  | eq =>
      left
      change cmp left right ≠ Ordering.lt
      rw [comparisonEq]
      decide
  | gt =>
      left
      change cmp left right ≠ Ordering.lt
      rw [comparisonEq]
      decide

private theorem authoritativeInitialPositionGE_trans
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    IsTrans Nat (AuthoritativeInitialPositionGE mol state fuel roots) := by
  let cmp : Nat → Nat → Ordering := Ordering.byKey
    (authoritativeInitialPositionKey mol state fuel roots)
    compareFailClosedOccurrenceBranchProjectedKeys
  letI : Std.TransCmp compareFailClosedOccurrenceBranchProjectedKeys :=
    compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  letI : Std.TransCmp cmp := inferInstanceAs
    (Std.TransCmp (Ordering.byKey
      (authoritativeInitialPositionKey mol state fuel roots)
      compareFailClosedOccurrenceBranchProjectedKeys))
  constructor
  intro left middle right leftMiddle middleRight
  exact Std.TransCmp.ge_trans (cmp := cmp) leftMiddle middleRight

/-- A successful in-range source position comparison is exactly comparison of the corresponding
total unary position keys. -/
theorem compareAuthoritativeRule6InitialPositions?_success_factors
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (left right : Nat)
    (leftBound : left < roots.length) (rightBound : right < roots.length)
    (decision : OccurrenceComparison)
    (computed : compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
      some decision) :
    compareFailClosedOccurrenceBranchProjectedKeys
        (authoritativeInitialPositionKey mol state fuel roots left)
        (authoritativeInitialPositionKey mol state fuel roots right) = decision.ordering := by
  have leftEq : roots[left]? = some roots[left] := List.getElem?_eq_getElem leftBound
  have rightEq : roots[right]? = some roots[right] := List.getElem?_eq_getElem rightBound
  have branchEq :
      compareOccurrenceBranchesUnrestrictedAuthoritative? mol state fuel roots[left] roots[right] =
        some decision := by
    simpa [compareAuthoritativeRule6InitialPositions?, leftEq, rightEq] using computed
  simpa [authoritativeInitialPositionKey, leftEq, rightEq] using
    (compareOccurrenceBranchesUnrestricted_ordering_success_factors
      mol state fuel roots[left] roots[right] decision branchEq)

/-- Source insertion is literal ordered insertion on the certified unary-key order whenever all
positions involved are in range and comparisons succeed. -/
theorem insertAuthoritativeRule6InitialPosition?_eq_orderedInsert
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left < roots.length → right < roots.length →
      ∃ decision,
        compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
          some decision)
    (candidate : Nat) (candidateBound : candidate < roots.length) :
    ∀ input, Rule6PositionsInRange roots input →
      insertAuthoritativeRule6InitialPosition? mol state fuel roots candidate input =
        some (input.orderedInsert
          (AuthoritativeInitialPositionGE mol state fuel roots) candidate)
  | [], _ => rfl
  | head :: tail, inRange => by
      have headBound : head < roots.length := inRange head (by simp)
      have tailRange : Rule6PositionsInRange roots tail := by
        intro position member
        exact inRange position (by simp [member])
      rcases comparisonTotal candidate head candidateBound headBound with
        ⟨decision, decisionEq⟩
      have factor := compareAuthoritativeRule6InitialPositions?_success_factors
        mol state fuel roots candidate head candidateBound headBound decision decisionEq
      by_cases senior : AuthoritativeInitialPositionGE mol state fuel roots candidate head
      · have notLt : decision.ordering ≠ Ordering.lt := by
          simpa [AuthoritativeInitialPositionGE, factor] using senior
        simp [insertAuthoritativeRule6InitialPosition?, decisionEq, notLt,
          List.orderedInsert, senior]
      · have isLt : decision.ordering = Ordering.lt := by
          unfold AuthoritativeInitialPositionGE at senior
          rw [factor] at senior
          cases orderingEq : decision.ordering <;> simp_all
        have deeper := insertAuthoritativeRule6InitialPosition?_eq_orderedInsert
          comparisonTotal candidate candidateBound tail tailRange
        simp [insertAuthoritativeRule6InitialPosition?, decisionEq, isLt, deeper,
          List.orderedInsert, senior]

/-- Source sorting is ordinary insertion sort on the lawful unary-key order. -/
theorem sortAuthoritativeRule6InitialPositions?_eq_insertionSort
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left < roots.length → right < roots.length →
      ∃ decision,
        compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
          some decision) :
    ∀ input, Rule6PositionsInRange roots input →
      sortAuthoritativeRule6InitialPositions? mol state fuel roots input =
        some (input.insertionSort
          (AuthoritativeInitialPositionGE mol state fuel roots))
  | [], _ => rfl
  | position :: positions, inRange => by
      have positionBound : position < roots.length := inRange position (by simp)
      have positionsRange : Rule6PositionsInRange roots positions := by
        intro candidate member
        exact inRange candidate (by simp [member])
      have tailEq := sortAuthoritativeRule6InitialPositions?_eq_insertionSort
        comparisonTotal positions positionsRange
      have insertEq := insertAuthoritativeRule6InitialPosition?_eq_orderedInsert
        comparisonTotal position positionBound
          (positions.insertionSort (AuthoritativeInitialPositionGE mol state fuel roots)) (by
            intro candidate member
            exact positionsRange candidate
              ((List.mem_insertionSort _).mp member))
      rw [List.insertionSort_cons]
      simp [sortAuthoritativeRule6InitialPositions?, tailEq, insertEq]

/-- Every successful source sort over supported in-range positions is pairwise nonincreasing in
the exact unary occurrence key. -/
theorem sortAuthoritativeRule6InitialPositions?_pairwise
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left < roots.length → right < roots.length →
      ∃ decision,
        compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
          some decision)
    {input sorted : List Nat} (inRange : Rule6PositionsInRange roots input)
    (sortedEq : sortAuthoritativeRule6InitialPositions? mol state fuel roots input = some sorted) :
    sorted.Pairwise (AuthoritativeInitialPositionGE mol state fuel roots) := by
  have modelEq := sortAuthoritativeRule6InitialPositions?_eq_insertionSort
    comparisonTotal input inRange
  have sortedModel : sorted = input.insertionSort
      (AuthoritativeInitialPositionGE mol state fuel roots) :=
    Option.some.inj (sortedEq.symm.trans modelEq)
  subst sorted
  letI : Std.Total (AuthoritativeInitialPositionGE mol state fuel roots) :=
    authoritativeInitialPositionGE_total mol state fuel roots
  letI : IsTrans Nat (AuthoritativeInitialPositionGE mol state fuel roots) :=
    authoritativeInitialPositionGE_trans mol state fuel roots
  exact List.pairwise_insertionSort
    (AuthoritativeInitialPositionGE mol state fuel roots) input

/-- Adjacent traversal of a pairwise unary-key order cannot contain a junior-before-senior
comparison. -/
theorem compareAuthoritativeRule6InitialAdjacent?_not_lt_of_pairwise
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left < roots.length → right < roots.length →
      ∃ decision,
        compareAuthoritativeRule6InitialPositions? mol state fuel roots left right =
          some decision) :
    ∀ positions adjacent,
      Rule6PositionsInRange roots positions →
      positions.Pairwise (AuthoritativeInitialPositionGE mol state fuel roots) →
      compareAuthoritativeRule6InitialAdjacent? mol state fuel roots positions = some adjacent →
      some Ordering.lt ∉ adjacent
  | [], adjacent, _inRange, _ordered, computed => by
      simp [compareAuthoritativeRule6InitialAdjacent?] at computed
      subst adjacent
      simp
  | [_], adjacent, _inRange, _ordered, computed => by
      simp [compareAuthoritativeRule6InitialAdjacent?] at computed
      subst adjacent
      simp
  | left :: right :: remaining, adjacent, inRange, ordered, computed => by
      have leftBound : left < roots.length := inRange left (by simp)
      have rightBound : right < roots.length := inRange right (by simp)
      have tailRange : Rule6PositionsInRange roots (right :: remaining) := by
        intro position member
        exact inRange position (by simp_all)
      have tailOrdered := ordered.of_cons
      rcases comparisonTotal left right leftBound rightBound with ⟨decision, decisionEq⟩
      cases deeperEq : compareAuthoritativeRule6InitialAdjacent?
          mol state fuel roots (right :: remaining) with
      | none => simp [compareAuthoritativeRule6InitialAdjacent?, decisionEq, deeperEq] at computed
      | some deeper =>
          simp [compareAuthoritativeRule6InitialAdjacent?, decisionEq, deeperEq] at computed
          subst adjacent
          have factor := compareAuthoritativeRule6InitialPositions?_success_factors
            mol state fuel roots left right leftBound rightBound decision decisionEq
          have headGE : AuthoritativeInitialPositionGE mol state fuel roots left right :=
            (List.pairwise_cons.mp ordered).1 right (by simp)
          have decisionNotLt : decision.ordering ≠ Ordering.lt := by
            simpa [AuthoritativeInitialPositionGE, factor] using headGE
          have deeperNotLt := compareAuthoritativeRule6InitialAdjacent?_not_lt_of_pairwise
            comparisonTotal (right :: remaining) deeper tailRange tailOrdered deeperEq
          intro member
          simp only [List.mem_cons, Option.some.injEq] at member
          rcases member with headEq | tailMember
          · exact decisionNotLt headEq.symm
          · exact deeperNotLt tailMember

/-- Exact source-level result: a supported successful initial sort and adjacent traversal is
automatically nonincreasing.  No separate chemical premise about the sort output is needed. -/
theorem authoritativeRule6InitialAdjacent_not_lt_of_support
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (roots : List CanonicalRerootCursor)
    (supported : ∀ root, root ∈ roots → CursorSupport mol fuel root)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sortedEq : sortAuthoritativeRule6InitialPositions? mol state fuel roots (List.range roots.length) =
      some sorted)
    (adjacentEq : compareAuthoritativeRule6InitialAdjacent? mol state fuel roots sorted =
      some adjacent) :
    some Ordering.lt ∉ adjacent := by
  let comparisonTotal := fun left right leftBound rightBound =>
    compareAuthoritativeRule6InitialPositions?_exists_of_support
      hierarchy roots supported left right leftBound rightBound
  have inputRange : Rule6PositionsInRange roots (List.range roots.length) := by
    intro position member
    exact List.mem_range.mp member
  have ordered := sortAuthoritativeRule6InitialPositions?_pairwise
    comparisonTotal inputRange sortedEq
  have sortedPerm := sortAuthoritativeRule6InitialPositions?_perm
    mol state fuel roots (List.range roots.length) sorted sortedEq
  have sortedRange : Rule6PositionsInRange roots sorted := by
    intro position member
    exact List.mem_range.mp ((sortedPerm.mem_iff).mp member)
  exact compareAuthoritativeRule6InitialAdjacent?_not_lt_of_pairwise
    comparisonTotal sorted adjacent sortedRange ordered adjacentEq

/-- The literal Boolean relation supplied by the source adapter to the constitutional topology
search: two in-range ligand positions belong to the same pre-Rule-6 priority class exactly when
the unrestricted ordinary comparator returns `eq`. -/
def AuthoritativeSourceInitialSameGroup (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (left right : Fin roots.length) : Prop :=
  (compareAuthoritativeRule6InitialPositions?
      mol state fuel roots left.val right.val).any
        (fun decision => decision.ordering = Ordering.eq) = true

private theorem authoritativeSourceInitialSameGroup_iff_key_eq
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (supported : ∀ root, root ∈ roots → CursorSupport mol fuel root)
    (left right : Fin roots.length) :
    AuthoritativeSourceInitialSameGroup mol state fuel roots left right ↔
      compareFailClosedOccurrenceBranchProjectedKeys
          (authoritativeInitialPositionKey mol state fuel roots left.val)
          (authoritativeInitialPositionKey mol state fuel roots right.val) = Ordering.eq := by
  rcases compareAuthoritativeRule6InitialPositions?_exists_of_support
      hierarchy roots supported left.val right.val left.isLt right.isLt with
    ⟨decision, decisionEq⟩
  have factor := compareAuthoritativeRule6InitialPositions?_success_factors
    mol state fuel roots left.val right.val left.isLt right.isLt decision decisionEq
  simp [AuthoritativeSourceInitialSameGroup, decisionEq, factor]

/-- The actual source pre-Rule-6 group relation is an equivalence relation on the complete ligand
position type.  Thus the topology search really preserves priority classes, rather than an
unconstrained Boolean relation. -/
theorem authoritativeSourceInitialSameGroup_equivalence_of_support
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (hierarchy : DescriptorRule6HierarchySupport mol state fuel)
    (supported : ∀ root, root ∈ roots → CursorSupport mol fuel root) :
    Equivalence (AuthoritativeSourceInitialSameGroup mol state fuel roots) := by
  let cmp := compareFailClosedOccurrenceBranchProjectedKeys
  letI : Std.TransCmp cmp := compareFailClosedOccurrenceBranchProjectedKeys_transCmp
  constructor
  · intro position
    rw [authoritativeSourceInitialSameGroup_iff_key_eq hierarchy supported]
    cases comparisonEq : cmp
        (authoritativeInitialPositionKey mol state fuel roots position.val)
        (authoritativeInitialPositionKey mol state fuel roots position.val) with
    | lt =>
        have swapped := Std.OrientedCmp.eq_swap (cmp := cmp)
          (a := authoritativeInitialPositionKey mol state fuel roots position.val)
          (b := authoritativeInitialPositionKey mol state fuel roots position.val)
        rw [comparisonEq] at swapped
        simp at swapped
    | eq => exact comparisonEq
    | gt =>
        have swapped := Std.OrientedCmp.eq_swap (cmp := cmp)
          (a := authoritativeInitialPositionKey mol state fuel roots position.val)
          (b := authoritativeInitialPositionKey mol state fuel roots position.val)
        rw [comparisonEq] at swapped
        simp at swapped
  · intro left right same
    rw [authoritativeSourceInitialSameGroup_iff_key_eq hierarchy supported] at same ⊢
    have swapped := Std.OrientedCmp.eq_swap (cmp := cmp)
      (a := authoritativeInitialPositionKey mol state fuel roots left.val)
      (b := authoritativeInitialPositionKey mol state fuel roots right.val)
    simpa [cmp, same] using swapped.symm
  · intro left middle right leftMiddle middleRight
    rw [authoritativeSourceInitialSameGroup_iff_key_eq hierarchy supported] at leftMiddle
    rw [authoritativeSourceInitialSameGroup_iff_key_eq hierarchy supported] at middleRight
    rw [authoritativeSourceInitialSameGroup_iff_key_eq hierarchy supported]
    exact Std.TransCmp.eq_trans leftMiddle middleRight

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter
