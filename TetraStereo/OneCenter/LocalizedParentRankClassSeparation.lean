import TetraStereo.OneCenter.LocalizedActualParentComparisonSeparation
import TetraStereo.OneCenter.LocalizedRankedPopulationMerge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Hierarchy-rank class separation of the actual parent from every outward child

`LocalizedActualParentComparisonSeparation` proves that, for an active-simple non-root carrier
occurrence, the actual parent-side cursor and every outward-side cursor compile cumulative keys
whose *constitutional* comparison is strict, and that the full cumulative comparator is already
decided at that constitutional component.  What it does not yet establish is the consequence for
the hierarchy-rank assignment `localizedRerootRankedChildren`: a strict comparison between two
siblings that are *not adjacent* in the sorted child list.  Adjacent strictness only increments the
rank at one adjacency; two non-adjacent strict siblings might in principle be separated by
comparator-equivalent siblings and still receive one rank each — but they cannot receive the *same*
rank, because reaching one from the other in a descending list must cross at least one strict
adjacency.

This module proves exactly that general fact, with no desired-rank equality assumed:

* `localizedRerootRankedChildren_exists_rank_ne_of_compare_ne_of_mem_of_descending`: in a
  descending child list, any two members with a strict cumulative comparison occupy distinct
  hierarchy ranks.  This is the "not mere adjacent strictness" step, derived by induction over the
  rank tail (Section 1).
* `prefixLayer_address_ne_of_slot_ne` and
  `mergeLocalizedRerootRankedLabelChildren_parent_child_addresses_disjoint` propagate distinct
  ranks into `mergeLocalizedRerootRankedLabelChildren`: at every depth the two siblings' label
  spheres are present in the merged sphere under *disjoint* rank-prefixed addresses (Section 2).
* `parentSide_outwardChild_rankClass_separated` ties the strict parent-vs-outward comparison from
  `LocalizedActualParentComparisonSeparation` to the sorted child list compiled inside the
  target-start cumulative key, exposing the parent key and the outward-child key as members of that
  sorted list and concluding distinct hierarchy ranks (Section 3).

Honesty bound: rank-class separation alone does **not** eliminate the parent label from the first
chiral population.  The two keys compared here are both compiled as children of the target-start
cursor, so the target-start key's own layer-0 head observation is the *target* occurrence, not the
parent; the parent-side key — whose own head is the parent occurrence — contributes the parent label
as a rank-prefixed child entry of the merged children population, not as the layer-0 head.  What
this module establishes is the weaker, exact statement that the parent key and every outward-child
key occupy *different* hierarchy-rank classes in `localizedRerootRankedChildren` of the sorted
compiled child list.  The remaining reference-selection dependency — which rank class (if any) the
parent's child entry contributes to the first chiral population — is outside this module, exactly as
flagged by `LocalizedRule4bReferenceDependencyAudit`.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Section 1: general rank separation from strict comparison

The rank assignment `localizedRerootRankedChildTail` is a single left-to-right pass: an adjacent
pair keeps the current rank when the comparator returns `eq`, and otherwise increments it.  In a
descending list the comparator never returns `lt`, so every strict step is a genuine descent, and
the rank function is monotone with strict growth exactly across strict adjacencies. -/

/-- Every rank assigned by the tail is at least the incoming rank. -/
theorem localizedRerootRankedChildTail_rank_ge
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ {children : List input.LocalizedRerootCumulativeRule45Key}
      {pair : input.LocalizedRerootCumulativeRule45Key × Nat},
      pair ∈ input.localizedRerootRankedChildTail previous rank children → rank ≤ pair.2 := by
  intro children
  induction children generalizing previous rank with
  | nil =>
      intro pair present
      simp [localizedRerootRankedChildTail] at present
  | cons child rest ih =>
      intro pair present
      rw [input.localizedRerootRankedChildTail_cons previous child rank rest] at present
      rcases List.mem_cons.mp present with same | tailPresent
      · rw [same]
        by_cases sameRank :
            input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
            <;> simp [sameRank]
      · have childRankGe : rank ≤
            (if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
              then rank else rank + 1) := by
          by_cases sameRank :
              input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
              <;> simp [sameRank]
        exact Nat.le_trans childRankGe
          (ih child (if input.compareLocalizedRerootCumulativeRule45Keys child previous =
            Ordering.eq then rank else rank + 1) tailPresent)

/-- Every member of the tail receives some rank. -/
theorem exists_rank_of_mem_localizedRerootRankedChildTail
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ {children : List input.LocalizedRerootCumulativeRule45Key}
      {key : input.LocalizedRerootCumulativeRule45Key},
      key ∈ children →
      ∃ keyRank : Nat,
        (key, keyRank) ∈ input.localizedRerootRankedChildTail previous rank children := by
  intro children
  induction children generalizing previous rank with
  | nil =>
      intro key keyMem
      cases keyMem
  | cons child rest ih =>
      intro key keyMem
      rcases List.mem_cons.mp keyMem with keyIsChild | keyInRest
      · subst key
        refine ⟨if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
          then rank else rank + 1, ?_⟩
        rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
        exact List.mem_cons_self
      · obtain ⟨keyRank, present⟩ := ih child
          (if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
            then rank else rank + 1) keyInRest
        refine ⟨keyRank, ?_⟩
        rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
        exact List.mem_cons_of_mem
          (child, if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
            then rank else rank + 1) present

/-- Every member of the child list receives some hierarchy rank. -/
theorem exists_rank_of_mem_localizedRerootRankedChildren
    (input : CertifiedLocalizedCIPInput) :
    ∀ {children : List input.LocalizedRerootCumulativeRule45Key}
      {key : input.LocalizedRerootCumulativeRule45Key},
      key ∈ children →
      ∃ keyRank : Nat,
        (key, keyRank) ∈ input.localizedRerootRankedChildren children := by
  intro children
  induction children with
  | nil =>
      intro key keyMem
      cases keyMem
  | cons child rest ih =>
      intro key keyMem
      rcases List.mem_cons.mp keyMem with keyIsChild | keyInRest
      · subst key
        refine ⟨0, ?_⟩
        rw [input.localizedRerootRankedChildren_cons child rest]
        exact List.mem_cons_self
      · obtain ⟨keyRank, present⟩ :=
          input.exists_rank_of_mem_localizedRerootRankedChildTail child 0 keyInRest
        refine ⟨keyRank, ?_⟩
        rw [input.localizedRerootRankedChildren_cons child rest]
        exact List.mem_cons_of_mem (child, 0) present

/-- If the incoming rank is strictly below the head's assigned rank, then it is strictly below
every rank assigned in the whole tail.  This is the single strict-adjacency step: the head's rank
differs from the incoming rank, and the tail only ever assigns ranks at least that large. -/
theorem localizedRerootRankedChildTail_rank_lt_of_head_compare_ne
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ {child : input.LocalizedRerootCumulativeRule45Key}
      {children : List input.LocalizedRerootCumulativeRule45Key}
      {key : input.LocalizedRerootCumulativeRule45Key} {keyRank : Nat},
      input.compareLocalizedRerootCumulativeRule45Keys previous child ≠ Ordering.eq →
      (key, keyRank) ∈ input.localizedRerootRankedChildTail previous rank (child :: children) →
      rank < keyRank := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  intro child children key keyRank headCompareNe present
  have childCompareNe : input.compareLocalizedRerootCumulativeRule45Keys child previous ≠
      Ordering.eq :=
    (Std.OrientedCmp.eq_comm
      (cmp := input.compareLocalizedRerootCumulativeRule45Keys)
      (a := previous) (b := child)).not.mp headCompareNe
  have childRankSucc : (if input.compareLocalizedRerootCumulativeRule45Keys child previous =
      Ordering.eq then rank else rank + 1) = rank + 1 := by
    simp [childCompareNe]
  rw [input.localizedRerootRankedChildTail_cons previous child rank children] at present
  rcases List.mem_cons.mp present with same | tailPresent
  · have keyRankEq : keyRank =
        (if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
          then rank else rank + 1) := congrArg Prod.snd same
    rw [keyRankEq]
    simp [childCompareNe]
  · have childRankLe : (if input.compareLocalizedRerootCumulativeRule45Keys child previous =
        Ordering.eq then rank else rank + 1) ≤ keyRank :=
      input.localizedRerootRankedChildTail_rank_ge child
        (if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
          then rank else rank + 1) tailPresent
    rw [childRankSucc] at childRankLe
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rank) childRankLe

/-- **Strict head-vs-member rank growth.**  In a descending list `previous :: children`, any member
`key ∈ children` with a strict comparison against `previous` receives a rank strictly above the
incoming rank.  The proof recurses exactly at comparator-equal heads (where the incoming rank is
carried over), and closes at the first strict head by the preceding head-strict step. -/
theorem localizedRerootRankedChildTail_exists_rank_gt_of_compare_ne_of_mem
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ {children : List input.LocalizedRerootCumulativeRule45Key},
      input.LocalizedRerootCumulativeRule45KeysDescending (previous :: children) →
      ∀ {key : input.LocalizedRerootCumulativeRule45Key},
        key ∈ children →
        input.compareLocalizedRerootCumulativeRule45Keys previous key ≠ Ordering.eq →
        ∃ keyRank : Nat,
          (key, keyRank) ∈ input.localizedRerootRankedChildTail previous rank children ∧
          rank < keyRank := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  intro children
  induction children generalizing previous rank with
  | nil =>
      intro descending key keyMem _
      cases keyMem
  | cons child rest ih =>
      intro descending key keyMem compareNe
      rcases List.mem_cons.mp keyMem with keyIsChild | keyInRest
      · subst key
        refine ⟨if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
            then rank else rank + 1, ?_⟩
        constructor
        · rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
          exact List.mem_cons_self
        · have childCompareNe : input.compareLocalizedRerootCumulativeRule45Keys child previous ≠
              Ordering.eq :=
            (Std.OrientedCmp.eq_comm
              (cmp := input.compareLocalizedRerootCumulativeRule45Keys)
              (a := previous) (b := child)).not.mp compareNe
          simp [childCompareNe]
      · by_cases headEq : input.compareLocalizedRerootCumulativeRule45Keys previous child =
            Ordering.eq
        · have childHeadEq : input.compareLocalizedRerootCumulativeRule45Keys child previous =
              Ordering.eq :=
            Std.OrientedCmp.eq_symm
              (cmp := input.compareLocalizedRerootCumulativeRule45Keys) headEq
          have childRestDescending :
              input.LocalizedRerootCumulativeRule45KeysDescending (child :: rest) :=
            (List.pairwise_cons.mp descending).2
          have childCompareNe : input.compareLocalizedRerootCumulativeRule45Keys child key ≠
              Ordering.eq := by
            have congr := Std.TransCmp.congr_left
              (cmp := input.compareLocalizedRerootCumulativeRule45Keys)
              (a := previous) (b := child) (c := key) headEq
            rw [congr] at compareNe
            exact compareNe
          obtain ⟨keyRank, present, rankLt⟩ :=
            ih child rank childRestDescending keyInRest childCompareNe
          have present' : (key, keyRank) ∈
              input.localizedRerootRankedChildTail child
                (if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
                  then rank else rank + 1) rest := by
            simpa [childHeadEq] using present
          refine ⟨keyRank, ?_, rankLt⟩
          rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
          exact List.mem_cons_of_mem
            (child, if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
              then rank else rank + 1) present'
        · let childRank : Nat :=
            if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
              then rank else rank + 1
          obtain ⟨keyRank, present⟩ :=
            input.exists_rank_of_mem_localizedRerootRankedChildTail child childRank keyInRest
          have memLifted : (key, keyRank) ∈
              input.localizedRerootRankedChildTail previous rank (child :: rest) := by
            rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
            exact List.mem_cons_of_mem (child, childRank) present
          exact ⟨keyRank, memLifted,
            input.localizedRerootRankedChildTail_rank_lt_of_head_compare_ne
              previous rank headEq memLifted⟩

/-- **Additive shift of the rank tail.**  Starting the rank tail at `rank + offset` instead of
`rank` shifts every assigned rank by exactly `offset`: the increments are governed solely by the
strict adjacencies, which are independent of the incoming rank.  This is the exact source-support
fact behind the offset between `localizedRerootRankedChildren rest` (starting at `0`) and
`localizedRerootRankedChildTail head 0 rest`. -/
theorem localizedRerootRankedChildTail_add_shift
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank offset : Nat) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key),
      input.localizedRerootRankedChildTail previous (rank + offset) children =
        (input.localizedRerootRankedChildTail previous rank children).map
          (fun pair => (pair.1, pair.2 + offset)) := by
  intro children
  induction children generalizing previous rank with
  | nil => rfl
  | cons child rest ih =>
      let childRank : Nat :=
        if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
          then rank else rank + 1
      have headShift :
          (if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
            then rank + offset else (rank + offset) + 1) = childRank + offset := by
        by_cases h : input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
        · simp [childRank, h]
        · simp [childRank, h]
          omega
      rw [input.localizedRerootRankedChildTail_cons previous child (rank + offset) rest,
        input.localizedRerootRankedChildTail_cons previous child rank rest]
      rw [headShift, ih child childRank]
      rfl

/-- **Offset between `localizedRerootRankedChildTail` and `localizedRerootRankedChildren`.**  The
rank tail at incoming rank `rank` over `first :: rest` is the children-rank list over
`first :: rest` with every rank shifted by the head's rank offset. -/
theorem localizedRerootRankedChildTail_eq_rankedChildren_map_add
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ (first : input.LocalizedRerootCumulativeRule45Key)
      (rest : List input.LocalizedRerootCumulativeRule45Key),
      input.localizedRerootRankedChildTail previous rank (first :: rest) =
        (input.localizedRerootRankedChildren (first :: rest)).map
          (fun pair => (pair.1, pair.2 +
            (if input.compareLocalizedRerootCumulativeRule45Keys first previous = Ordering.eq
              then rank else rank + 1))) := by
  intro first rest
  let offset : Nat :=
    if input.compareLocalizedRerootCumulativeRule45Keys first previous = Ordering.eq
      then rank else rank + 1
  rw [input.localizedRerootRankedChildren_cons first rest]
  rw [input.localizedRerootRankedChildTail_cons previous first rank rest]
  change (first, offset) :: input.localizedRerootRankedChildTail first offset rest =
      List.map (fun pair => (pair.1, pair.2 + offset))
        ((first, 0) :: input.localizedRerootRankedChildTail first 0 rest)
  have shifted : input.localizedRerootRankedChildTail first offset rest =
      (input.localizedRerootRankedChildTail first 0 rest).map
        (fun pair => (pair.1, pair.2 + offset)) := by
    simpa [Nat.zero_add] using
      (input.localizedRerootRankedChildTail_add_shift first 0 offset rest)
  rw [shifted]
  simp

/-- **General hierarchy-rank separation in the rank tail.**  In a descending list
`previous :: children`, any two members of `children` whose cumulative comparison is strict occupy
distinct hierarchy ranks in `localizedRerootRankedChildTail previous rank children`.  The earlier
member is either the list head (handled by the strict head-vs-member growth theorem) or both
members recurse into the tail with the carried rank. -/
theorem localizedRerootRankedChildTail_exists_rank_ne_of_compare_ne_of_mem_of_descending
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ {children : List input.LocalizedRerootCumulativeRule45Key},
      input.LocalizedRerootCumulativeRule45KeysDescending (previous :: children) →
      ∀ {left right : input.LocalizedRerootCumulativeRule45Key},
        left ∈ children → right ∈ children →
        input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.eq →
        ∃ leftRank rightRank : Nat,
          (left, leftRank) ∈ input.localizedRerootRankedChildTail previous rank children ∧
          (right, rightRank) ∈ input.localizedRerootRankedChildTail previous rank children ∧
          leftRank ≠ rightRank := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  intro children
  induction children generalizing previous rank with
  | nil =>
      intro descending left right leftMem _ _
      cases leftMem
  | cons child rest ih =>
      intro descending left right leftMem rightMem compareNe
      let childRank : Nat :=
        if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
          then rank else rank + 1
      have childRestDescending :
          input.LocalizedRerootCumulativeRule45KeysDescending (child :: rest) :=
        (List.pairwise_cons.mp descending).2
      rcases List.mem_cons.mp leftMem with leftIsChild | leftInRest
      · rcases List.mem_cons.mp rightMem with rightIsChild | rightInRest
        · subst left
          subst right
          have selfEq : input.compareLocalizedRerootCumulativeRule45Keys child child = Ordering.eq :=
            Std.ReflCmp.compare_self
              (cmp := input.compareLocalizedRerootCumulativeRule45Keys)
          exact (compareNe selfEq).elim
        · subst left
          obtain ⟨rightRank, rightPresent, rankLt⟩ :=
            input.localizedRerootRankedChildTail_exists_rank_gt_of_compare_ne_of_mem
              child childRank childRestDescending rightInRest compareNe
          have leftPresent : (child, childRank) ∈
              input.localizedRerootRankedChildTail previous rank (child :: rest) := by
            rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
            exact List.mem_cons_self
          have rightLifted : (right, rightRank) ∈
              input.localizedRerootRankedChildTail previous rank (child :: rest) := by
            rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
            exact List.mem_cons_of_mem (child, childRank) rightPresent
          exact ⟨childRank, rightRank, leftPresent, rightLifted, by omega⟩
      · rcases List.mem_cons.mp rightMem with rightIsChild | rightInRest
        · subst right
          have headLeftNe : input.compareLocalizedRerootCumulativeRule45Keys child left ≠
              Ordering.eq :=
            (Std.OrientedCmp.eq_comm
              (cmp := input.compareLocalizedRerootCumulativeRule45Keys)
              (a := left) (b := child)).not.mp compareNe
          obtain ⟨leftRank, leftPresent, rankLt⟩ :=
            input.localizedRerootRankedChildTail_exists_rank_gt_of_compare_ne_of_mem
              child childRank childRestDescending leftInRest headLeftNe
          have leftLifted : (left, leftRank) ∈
              input.localizedRerootRankedChildTail previous rank (child :: rest) := by
            rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
            exact List.mem_cons_of_mem (child, childRank) leftPresent
          have rightPresent : (child, childRank) ∈
              input.localizedRerootRankedChildTail previous rank (child :: rest) := by
            rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
            exact List.mem_cons_self
          exact ⟨leftRank, childRank, leftLifted, rightPresent, by omega⟩
        · obtain ⟨leftRank, rightRank, leftPresent, rightPresent, rankNe⟩ :=
            ih child childRank childRestDescending leftInRest rightInRest compareNe
          have leftLifted : (left, leftRank) ∈
              input.localizedRerootRankedChildTail previous rank (child :: rest) := by
            rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
            exact List.mem_cons_of_mem (child, childRank) leftPresent
          have rightLifted : (right, rightRank) ∈
              input.localizedRerootRankedChildTail previous rank (child :: rest) := by
            rw [input.localizedRerootRankedChildTail_cons previous child rank rest]
            exact List.mem_cons_of_mem (child, childRank) rightPresent
          exact ⟨leftRank, rightRank, leftLifted, rightLifted, rankNe⟩

/-- **General hierarchy-rank separation.**  In a descending child list, any two members whose
cumulative comparison is strict occupy distinct hierarchy ranks in `localizedRerootRankedChildren`.
This is the general "not mere adjacent strictness" fact: the earlier member is either the list head
(handled by the strict head-vs-member growth theorem) or both members recurse into the rank tail. -/
theorem localizedRerootRankedChildren_exists_rank_ne_of_compare_ne_of_mem_of_descending
    (input : CertifiedLocalizedCIPInput) :
    ∀ {children : List input.LocalizedRerootCumulativeRule45Key},
      input.LocalizedRerootCumulativeRule45KeysDescending children →
      ∀ {left right : input.LocalizedRerootCumulativeRule45Key},
        left ∈ children → right ∈ children →
        input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.eq →
        ∃ leftRank rightRank : Nat,
          (left, leftRank) ∈ input.localizedRerootRankedChildren children ∧
          (right, rightRank) ∈ input.localizedRerootRankedChildren children ∧
          leftRank ≠ rightRank := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  intro children
  cases children with
  | nil =>
      intro descending left right leftMem _
      cases leftMem
  | cons head rest =>
      intro descending left right leftMem rightMem compareNe
      rcases List.mem_cons.mp leftMem with leftIsHead | leftInRest
      · rcases List.mem_cons.mp rightMem with rightIsHead | rightInRest
        · subst left
          subst right
          have selfEq : input.compareLocalizedRerootCumulativeRule45Keys head head = Ordering.eq :=
            Std.ReflCmp.compare_self
              (cmp := input.compareLocalizedRerootCumulativeRule45Keys)
          exact (compareNe selfEq).elim
        · subst left
          obtain ⟨rightRank, rightPresent, rankLt⟩ :=
            input.localizedRerootRankedChildTail_exists_rank_gt_of_compare_ne_of_mem
              head 0 descending rightInRest compareNe
          refine ⟨0, rightRank, ?_, ?_, ?_⟩
          · rw [input.localizedRerootRankedChildren_cons head rest]
            exact List.mem_cons_self
          · rw [input.localizedRerootRankedChildren_cons head rest]
            exact List.mem_cons_of_mem (head, 0) rightPresent
          · omega
      · rcases List.mem_cons.mp rightMem with rightIsHead | rightInRest
        · subst right
          have headLeftNe : input.compareLocalizedRerootCumulativeRule45Keys head left ≠
              Ordering.eq :=
            (Std.OrientedCmp.eq_comm
              (cmp := input.compareLocalizedRerootCumulativeRule45Keys)
              (a := left) (b := head)).not.mp compareNe
          obtain ⟨leftRank, leftPresent, rankLt⟩ :=
            input.localizedRerootRankedChildTail_exists_rank_gt_of_compare_ne_of_mem
              head 0 descending leftInRest headLeftNe
          refine ⟨leftRank, 0, ?_, ?_, ?_⟩
          · rw [input.localizedRerootRankedChildren_cons head rest]
            exact List.mem_cons_of_mem (head, 0) leftPresent
          · rw [input.localizedRerootRankedChildren_cons head rest]
            exact List.mem_cons_self
          · omega
        · obtain ⟨leftRank, rightRank, leftPresent, rightPresent, rankNe⟩ :=
            input.localizedRerootRankedChildTail_exists_rank_ne_of_compare_ne_of_mem_of_descending
              head 0 descending leftInRest rightInRest compareNe
          refine ⟨leftRank, rightRank, ?_, ?_, rankNe⟩
          · rw [input.localizedRerootRankedChildren_cons head rest]
            exact List.mem_cons_of_mem (head, 0) leftPresent
          · rw [input.localizedRerootRankedChildren_cons head rest]
            exact List.mem_cons_of_mem (head, 0) rightPresent

/-! ## Section 2: prefix-rank propagation into the ranked-label merge -/

/-- Two rank-prefixed label spheres built under distinct rank slots have disjoint addresses: the
rank slot is the head of every address, so an equal address would force the two slots equal. -/
theorem prefixLayer_address_ne_of_slot_ne {α : Type*} {leftSlot rightSlot : Nat}
    (slotNe : leftSlot ≠ rightSlot) :
    ∀ (leftLayer rightLayer : List (OfficialSparseEntry α))
      (leftEntry rightEntry : OfficialSparseEntry α),
      leftEntry ∈ OfficialRuleMajorKey.prefixLayer leftSlot leftLayer →
      rightEntry ∈ OfficialRuleMajorKey.prefixLayer rightSlot rightLayer →
      leftEntry.1 ≠ rightEntry.1 := by
  intro leftLayer rightLayer leftEntry rightEntry leftPresent rightPresent
  rw [OfficialRuleMajorKey.prefixLayer, List.mem_map] at leftPresent rightPresent
  rcases leftPresent with ⟨leftSource, _leftSourcePresent, leftEq⟩
  rcases rightPresent with ⟨rightSource, _rightSourcePresent, rightEq⟩
  intro addressEq
  apply slotNe
  have leftAddr : leftEntry.1 = leftSlot :: leftSource.1 := by
    rw [← leftEq]
  have rightAddr : rightEntry.1 = rightSlot :: rightSource.1 := by
    rw [← rightEq]
  have both : leftSlot :: leftSource.1 = rightSlot :: rightSource.1 := by
    rw [← leftAddr, addressEq, rightAddr]
  exact (List.cons.inj both).1

/-- Membership in a `flatMap` from membership in one chunk. -/
private theorem mem_flatMap_of_mem_of_mem {α β : Type*} {blocks : List α} (f : α → List β)
    {a : α} {b : β} (aMem : a ∈ blocks) (bMem : b ∈ f a) :
    b ∈ blocks.flatMap f := by
  induction blocks with
  | nil => cases aMem
  | cons x rest ih =>
      rcases List.mem_cons.mp aMem with rfl | aInRest
      · rw [List.flatMap_cons]
        exact List.mem_append_left _ bMem
      · rw [List.flatMap_cons]
        exact List.mem_append_right _ (ih aInRest)

/-- **Propagation of distinct ranks into the merged ranked-label spheres.**  Whenever two
siblings carry distinct hierarchy ranks in `localizedRerootRankedChildren`, at every sphere depth
their respective rank-prefixed label entries both occur in the merged sphere, and any such pair of
entries has disjoint addresses.  This is the exact transport of rank-class separation through
`mergeLocalizedRerootRankedLabelChildren`; it says nothing about which rank the parent's own
layer-0 chiral observation occupies. -/
theorem mergeLocalizedRerootRankedLabelChildren_parent_child_addresses_disjoint
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    {leftRank rightRank : Nat}
    (leftRanked : (left, leftRank) ∈ input.localizedRerootRankedChildren children)
    (rightRanked : (right, rightRank) ∈ input.localizedRerootRankedChildren children)
    (rankNe : leftRank ≠ rightRank) :
    ∀ (depth : Nat)
      (leftEntry rightEntry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel)),
      leftEntry ∈ OfficialRuleMajorKey.prefixLayer leftRank
        (left.rankedLabels.getD depth []) →
      rightEntry ∈ OfficialRuleMajorKey.prefixLayer rightRank
        (right.rankedLabels.getD depth []) →
      leftEntry ∈ (input.mergeLocalizedRerootRankedLabelChildren children).getD depth [] ∧
      rightEntry ∈ (input.mergeLocalizedRerootRankedLabelChildren children).getD depth [] ∧
      leftEntry.1 ≠ rightEntry.1 := by
  intro depth leftEntry rightEntry leftPresent rightPresent
  have addressNe := prefixLayer_address_ne_of_slot_ne rankNe
    (left.rankedLabels.getD depth []) (right.rankedLabels.getD depth [])
    leftEntry rightEntry leftPresent rightPresent
  rw [input.getD_mergeLocalizedRerootRankedLabelChildren children depth]
  constructor
  · exact mem_flatMap_of_mem_of_mem
      (fun child => OfficialRuleMajorKey.prefixLayer child.2
        (child.1.rankedLabels.getD depth [])) leftRanked leftPresent
  · constructor
    · exact mem_flatMap_of_mem_of_mem
        (fun child => OfficialRuleMajorKey.prefixLayer child.2
          (child.1.rankedLabels.getD depth [])) rightRanked rightPresent
    · exact addressNe

/-! ## Section 3: application to the parent-side versus outward-side cursors -/

/-- Every executable child of the parent-cut cursor `{target, some parent}` is also an executable
child of the uncut target-start cursor `{target, none}`: cutting only the incoming parent address
removes one neighbor, so the remaining outward neighbors are already among the uncut neighbors. -/
theorem outwardChild_mem_executableLocalizedRerootChildren_uncut
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := none } := by
  intro child present
  have intendedCut : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames
        { occurrence := target, previous? := some certificate.parent } := by
    rw [← input.executableLocalizedRerootChildren_map
      { occurrence := target, previous? := some certificate.parent }]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have neighbor : child.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 :=
    input.mem_localizedRerootNeighborFrames_of_mem_intended
      { occurrence := target, previous? := some certificate.parent }
      child.occurrence.1 intendedCut
  have notDuplicate : target.1.node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, targetActive.1]
  have intendedUncut : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames
        { occurrence := target, previous? := none } := by
    simp [intendedLocalizedRerootChildFrames, notDuplicate, neighbor]
  unfold executableLocalizedRerootChildren
  rw [List.mem_map]
  refine ⟨⟨child.occurrence.1, intendedUncut⟩, List.mem_attach _ _, ?_⟩
  apply LocalizedRerootCursor.ext
  · exact Subtype.ext rfl
  · exact (input.executableLocalizedRerootChildren_previous
      { occurrence := target, previous? := some certificate.parent } child present).symm

/-! ## Local fuel-complete child compilation helpers

`LocalizedRerootFuelCompleteness` proves that every path-valid cursor compiles at
`2 * (carrierFuel + 1)`; these two lemmas assemble the compiled child list (the `mapM` result) and
recover membership of an individually compiled key in that list. -/

private theorem mapM_buildLocalizedRerootCumulativeRule45Key?_of_forall
    (input : CertifiedLocalizedCIPInput) {carrierFuel evaluationFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        input.buildLocalizedRerootCumulativeRule45Key?
          stage target view evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (input.buildLocalizedRerootCumulativeRule45Key?
          stage target view evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        input.mapM_buildLocalizedRerootCumulativeRule45Key?_of_forall
          stage target view cursors (fun child present =>
            complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

private theorem mapM_buildLocalizedRerootCumulativeRule45Key?_mem_of_mem
    (input : CertifiedLocalizedCIPInput) {carrierFuel evaluationFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45Key?
        stage target view evaluationFuel) = some keys →
      ∀ {cursor : input.LocalizedRerootCursor carrierFuel}
        {key : input.LocalizedRerootCumulativeRule45Key},
        cursor ∈ cursors →
        input.buildLocalizedRerootCumulativeRule45Key?
          stage target view evaluationFuel cursor = some key →
        key ∈ keys
  | [], keys, computed, cursor, key, present, built => by
      simp at present
  | cursor :: cursors, keys, computed, member, key, present, built => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCumulativeRule45Key?
          stage target view evaluationFuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCumulativeRule45Key?
                stage target view evaluationFuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with memberIsHead | tailPresent
              · subst member
                have eq : some key = some head := built.symm.trans headComputed
                have keyIsHead : key = head := by simpa using eq
                rw [keyIsHead]
                exact List.mem_cons_self
              · exact List.mem_cons_of_mem head
                  (input.mapM_buildLocalizedRerootCumulativeRule45Key?_mem_of_mem
                    stage target view cursors tail tailComputed tailPresent built)

/-- **Parent-side versus every outward-side cursor: distinct hierarchy ranks.**

For an active-simple non-root carrier occurrence `target`, the actual parent-side cursor and every
outward-side cursor compile (at fuel `2 * (carrierFuel + 1)`) into two cumulative keys whose
comparison is strict.  Both cursors are executable children of the uncut target-start cursor, so
both keys occur in the compiled-then-sorted child list inside the target-start key; by the general
rank-separation theorem they therefore occupy distinct hierarchy ranks in
`localizedRerootRankedChildren`.  All three facts — strict comparison, membership in the same
sorted child list, and distinct ranks — are derived, not assumed; in particular no desired-rank
equality is asserted. -/
theorem parentSide_outwardChild_rankClass_separated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (nonroot : target.1.address ≠ [])
    (stage : LocalizedCumulativeRule45Stage)
    (view : input.LocalizedDependencyView target) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target,
          previous? := some (input.localizedParentFrameHistory target nonroot).parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      ∃ parentKey childKey : input.LocalizedRerootCumulativeRule45Key,
        ∃ childKeys : List input.LocalizedRerootCumulativeRule45Key,
          ∃ parentRank childRank : Nat,
            input.buildLocalizedRerootCumulativeRule45Key? stage target view
              (2 * (carrierFuel + 1))
              { occurrence := (input.localizedParentFrameHistory target nonroot).parent,
                previous? := some target } = some parentKey ∧
            input.buildLocalizedRerootCumulativeRule45Key? stage target view
              (2 * (carrierFuel + 1)) child = some childKey ∧
            (input.executableLocalizedRerootChildren
              { occurrence := target, previous? := none }).mapM
              (input.buildLocalizedRerootCumulativeRule45Key? stage target view
                (2 * (carrierFuel + 1))) = some childKeys ∧
            input.LocalizedRerootCumulativeRule45KeysDescending
              (input.sortLocalizedRerootCumulativeRule45Keys childKeys) ∧
            parentKey ∈ input.sortLocalizedRerootCumulativeRule45Keys childKeys ∧
            childKey ∈ input.sortLocalizedRerootCumulativeRule45Keys childKeys ∧
            (parentKey, parentRank) ∈ input.localizedRerootRankedChildren
              (input.sortLocalizedRerootCumulativeRule45Keys childKeys) ∧
            (childKey, childRank) ∈ input.localizedRerootRankedChildren
              (input.sortLocalizedRerootCumulativeRule45Keys childKeys) ∧
            parentRank ≠ childRank := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  intro child slot childPresent childAddress
  let parent : input.LocalizedCIPOccurrence carrierFuel :=
    (input.localizedParentFrameHistory target nonroot).parent
  let uncutCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  let children : List (input.LocalizedRerootCursor carrierFuel) :=
    input.executableLocalizedRerootChildren uncutCursor
  let parentCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := parent, previous? := some target }
  have parentMember : parentCursor ∈ children :=
    input.parentCursor_mem_executableLocalizedRerootChildren target targetActive
      (input.localizedParentFrameHistory target nonroot)
  have childMember : child ∈ children :=
    input.outwardChild_mem_executableLocalizedRerootChildren_uncut target targetActive
      (input.localizedParentFrameHistory target nonroot) child childPresent
  obtain ⟨parentKey, childKey, parentBuilt, childBuilt, constitutionalNe, comparisonEq⟩ :=
    input.parentSide_outwardChild_constitutionalCompare_ne_eq target targetActive
      (input.localizedParentFrameHistory target nonroot) stage view child slot
      childPresent childAddress
  have compareNe : input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey ≠
      Ordering.eq := by
    rw [comparisonEq]
    exact constitutionalNe
  have childComplete : ∀ c ∈ children, ∃ key,
      input.buildLocalizedRerootCumulativeRule45Key? stage target view
        (2 * (carrierFuel + 1)) c = some key := by
    intro c cPresent
    have cValid : input.LocalizedRerootCursorValid c :=
      input.localizedRerootChild_valid uncutCursor c children
        (input.executableLocalizedRerootChildren_declarative uncutCursor) cPresent
    exact input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view c cValid
  obtain ⟨childKeys, childKeysComputed⟩ :=
    input.mapM_buildLocalizedRerootCumulativeRule45Key?_of_forall
      stage target view children childComplete
  let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
  have descending : input.LocalizedRerootCumulativeRule45KeysDescending sorted :=
    input.sortLocalizedRerootCumulativeRule45Keys_descending childKeys
  have parentKeyMem : parentKey ∈ sorted := by
    have perm := input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys
    have inChildKeys : parentKey ∈ childKeys :=
      input.mapM_buildLocalizedRerootCumulativeRule45Key?_mem_of_mem
        stage target view children childKeys childKeysComputed parentMember parentBuilt
    exact perm.mem_iff.mpr inChildKeys
  have childKeyMem : childKey ∈ sorted := by
    have perm := input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys
    have inChildKeys : childKey ∈ childKeys :=
      input.mapM_buildLocalizedRerootCumulativeRule45Key?_mem_of_mem
        stage target view children childKeys childKeysComputed childMember childBuilt
    exact perm.mem_iff.mpr inChildKeys
  obtain ⟨parentRank, childRank, parentRanked, childRanked, rankNe⟩ :=
    input.localizedRerootRankedChildren_exists_rank_ne_of_compare_ne_of_mem_of_descending
      descending parentKeyMem childKeyMem compareNe
  exact ⟨parentKey, childKey, childKeys, parentRank, childRank, parentBuilt, childBuilt,
    childKeysComputed, descending, parentKeyMem, childKeyMem, parentRanked, childRanked, rankNe⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority assertions

`assert_kernel_only` permits exactly `propext`, `Classical.choice` and `Quot.sound`, and rejects
`sorryAx`, project axioms and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_rank_ge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_rank_lt_of_head_compare_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_rank_of_mem_localizedRerootRankedChildTail
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_rank_of_mem_localizedRerootRankedChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_exists_rank_gt_of_compare_ne_of_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_add_shift
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_eq_rankedChildren_map_add
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_exists_rank_ne_of_compare_ne_of_mem_of_descending
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildren_exists_rank_ne_of_compare_ne_of_mem_of_descending
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prefixLayer_address_ne_of_slot_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootRankedLabelChildren_parent_child_addresses_disjoint
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardChild_mem_executableLocalizedRerootChildren_uncut
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentSide_outwardChild_rankClass_separated
