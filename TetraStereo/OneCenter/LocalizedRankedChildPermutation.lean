import TetraStereo.OneCenter.LocalizedRule4bPopulationInvariance

set_option autoImplicit false

open List

/-!
# Permutation invariance of hierarchy-rank assignment for descending cumulative keys

`localizedRerootRankedChildren` assigns hierarchy-equivalence ranks to a list of cumulative
Rule-4a--5 keys: the first key receives rank `0`, a key comparator-equal to its predecessor
inherits the predecessor's rank, and any strict class change increments the rank.  The independent
declarative key relation admits arbitrary *descending* sibling permutations, so Rule-4b population
extraction has to be independent of the chosen descending representative.

This module proves the generic statement: if two lists of arbitrary cumulative keys are both
descending and are related by `List.Perm`, then their ranked-children lists are related by
`List.Perm` as lists of `(key, rank)` pairs.  The proof is purely comparator-theoretic: it uses
only `Std.OrientedCmp`/`Std.TransCmp`, never any independent semantics of the keys.  Both
descending hypotheses are essential: an arbitrary permutation of the same multiset can reorder
strictly decreasing keys and change their ranks.

The supporting ingredients are

* `localizedRerootRankedChildTail_move_tied`: moving an element through a prefix of keys tied to
  it does not change the ranked tail up to permutation;
* `localizedRerootRankedChildTail_perm_of_descending`: for two descending permutations sharing a
  predecessor context, the ranked tails are permutation-equivalent;
* `localizedRerootRankedChildren_move_tied_head`: the analogous move for a full ranked-children
  list (first rank `0`).
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Basic comparator facts -/

/-- A comparison that is not `Ordering.lt` is a `greater-or-equal` comparison; this is the reading
used by the descending predicate. -/
private theorem isGE_of_compare_ne_lt
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (comparison :
      input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.lt) :
    (input.compareLocalizedRerootCumulativeRule45Keys left right).isGE := by
  cases h : input.compareLocalizedRerootCumulativeRule45Keys left right with
  | lt => exact absurd h comparison
  | eq => simp
  | gt => simp

/-- The maximal heads of two descending lists with the same elements are comparator-equal.
Totality of the `Ordering`-valued comparator is what makes the two maximal classes coincide. -/
private theorem compare_heads_eq_of_descending_perm
    (input : CertifiedLocalizedCIPInput)
    {leftHead rightHead : input.LocalizedRerootCumulativeRule45Key}
    {leftTail rightTail : List input.LocalizedRerootCumulativeRule45Key}
    (hLeft :
      input.LocalizedRerootCumulativeRule45KeysDescending (leftHead :: leftTail))
    (hRight :
      input.LocalizedRerootCumulativeRule45KeysDescending (rightHead :: rightTail))
    (perm : (leftHead :: leftTail).Perm (rightHead :: rightTail)) :
    input.compareLocalizedRerootCumulativeRule45Keys leftHead rightHead = Ordering.eq := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  unfold LocalizedRerootCumulativeRule45KeysDescending at hLeft hRight
  have leftGE :
      (input.compareLocalizedRerootCumulativeRule45Keys leftHead rightHead).isGE := by
    have member : rightHead ∈ leftHead :: leftTail :=
      perm.mem_iff.mpr (by simp)
    rcases List.mem_cons.mp member with same | inTail
    · subst rightHead
      simp [Std.ReflCmp.compare_self]
    · exact isGE_of_compare_ne_lt input
        ((List.pairwise_cons.mp hLeft).1 rightHead inTail)
  have rightGE :
      (input.compareLocalizedRerootCumulativeRule45Keys rightHead leftHead).isGE := by
    have member : leftHead ∈ rightHead :: rightTail :=
      perm.mem_iff.mp (by simp)
    rcases List.mem_cons.mp member with same | inTail
    · subst rightHead
      simp [Std.ReflCmp.compare_self]
    · exact isGE_of_compare_ne_lt input
        ((List.pairwise_cons.mp hRight).1 leftHead inTail)
  exact Std.OrientedCmp.isGE_antisymm leftGE rightGE

/-- Reordering a tied maximal head to the front of its list, starting from a descending list,
keeps the list descending: every element before the head is comparator-equal to it.  The
`rightHead :: rightTail = pre ++ leftHead :: suf` decomposition is the position of the head to be
moved. -/
private theorem tied_prefix_descending_reorder
    (input : CertifiedLocalizedCIPInput)
    {leftHead rightHead : input.LocalizedRerootCumulativeRule45Key}
    {leftTail rightTail : List input.LocalizedRerootCumulativeRule45Key}
    (hLeft :
      input.LocalizedRerootCumulativeRule45KeysDescending (leftHead :: leftTail))
    (hRight :
      input.LocalizedRerootCumulativeRule45KeysDescending (rightHead :: rightTail))
    (perm : (leftHead :: leftTail).Perm (rightHead :: rightTail))
    {pre suf : List input.LocalizedRerootCumulativeRule45Key}
    (decomposition : rightHead :: rightTail = pre ++ leftHead :: suf) :
    (∀ p ∈ pre,
        input.compareLocalizedRerootCumulativeRule45Keys p leftHead = Ordering.eq) ∧
      input.LocalizedRerootCumulativeRule45KeysDescending (leftHead :: (pre ++ suf)) := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  unfold LocalizedRerootCumulativeRule45KeysDescending at hLeft hRight
  rw [decomposition] at hRight
  have prePairwise := (List.pairwise_append.mp hRight).1
  have consSufPairwise := (List.pairwise_append.mp hRight).2.1
  have cross := (List.pairwise_append.mp hRight).2.2
  have sufPairwise := (List.pairwise_cons.mp consSufPairwise).2
  -- `leftHead` is maximal in the permuted list.
  have maximal :
      ∀ q ∈ rightHead :: rightTail,
        input.compareLocalizedRerootCumulativeRule45Keys leftHead q ≠ Ordering.lt := by
    intro q present
    have presentLeft : q ∈ leftHead :: leftTail := perm.mem_iff.mpr present
    rcases List.mem_cons.mp presentLeft with same | inTail
    · subst q
      simp [Std.ReflCmp.compare_self]
    · exact (List.pairwise_cons.mp hLeft).1 q inTail
  have tied :
      ∀ p ∈ pre,
        input.compareLocalizedRerootCumulativeRule45Keys p leftHead = Ordering.eq := by
    intro p inPre
    have presentRight : p ∈ rightHead :: rightTail := by
      rw [decomposition]
      exact List.mem_append_left _ inPre
    exact Std.OrientedCmp.isGE_antisymm
      (isGE_of_compare_ne_lt input (cross p inPre leftHead (by simp)))
      (isGE_of_compare_ne_lt input (maximal p presentRight))
  refine ⟨tied, ?_⟩
  unfold LocalizedRerootCumulativeRule45KeysDescending
  rw [List.pairwise_cons, List.pairwise_append]
  refine ⟨?_, prePairwise, sufPairwise, ?_⟩
  · intro q inReordered
    rcases List.mem_append.mp inReordered with inPre | inSuf
    · exact maximal q (by
        rw [decomposition]
        exact List.mem_append_left _ inPre)
    · exact maximal q (by
        rw [decomposition]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ inSuf))
  · intro a inPre b inSuf
    exact cross a inPre b (List.mem_cons_of_mem _ inSuf)

/-! ## Moving a tied element through a prefix -/

/-- Moving a key `c` through a prefix of keys that are all comparator-equal to it does not change
the ranked tail up to permutation.  This is the local move underlying the head-matching argument:
all moved keys receive the same rank, and the suffix sees a comparator-equivalent predecessor. -/
theorem localizedRerootRankedChildTail_move_tied
    (input : CertifiedLocalizedCIPInput)
    (c : input.LocalizedRerootCumulativeRule45Key)
    (pre suf : List input.LocalizedRerootCumulativeRule45Key) :
    ∀ (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat),
      input.LocalizedRerootCumulativeRule45KeysDescending (previous :: (pre ++ c :: suf)) →
      (∀ p ∈ pre,
          input.compareLocalizedRerootCumulativeRule45Keys p c = Ordering.eq) →
      (input.localizedRerootRankedChildTail previous rank (pre ++ c :: suf)).Perm
        (input.localizedRerootRankedChildTail previous rank (c :: (pre ++ suf))) := by
  induction pre with
  | nil =>
      intro previous rank _hdesc _htied
      exact List.Perm.refl _
  | cons p ps ih =>
      intro previous rank hdesc htied
      letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
        input.compareLocalizedRerootCumulativeRule45Keys_transCmp
      change
        (input.localizedRerootRankedChildTail previous rank
            (p :: (ps ++ c :: suf))).Perm
          (input.localizedRerootRankedChildTail previous rank
            (c :: (p :: (ps ++ suf))))
      simp only [localizedRerootRankedChildTail]
      have hpTied :
          input.compareLocalizedRerootCumulativeRule45Keys p c = Ordering.eq :=
        htied p (by simp)
      have hcp :
          input.compareLocalizedRerootCumulativeRule45Keys c p = Ordering.eq :=
        Std.OrientedCmp.eq_symm hpTied
      have hpsTied :
          ∀ q ∈ ps,
            input.compareLocalizedRerootCumulativeRule45Keys q c = Ordering.eq :=
        fun q inPs => htied q (List.mem_cons_of_mem p inPs)
      have hdescTail :
          input.LocalizedRerootCumulativeRule45KeysDescending
            (p :: (ps ++ c :: suf)) :=
        (List.pairwise_cons.mp hdesc).2
      let ifP : Nat :=
        (if input.compareLocalizedRerootCumulativeRule45Keys p previous = Ordering.eq
          then rank else rank + 1)
      let ifC : Nat :=
        (if input.compareLocalizedRerootCumulativeRule45Keys c previous = Ordering.eq
          then rank else rank + 1)
      change
        (p, ifP) :: input.localizedRerootRankedChildTail p ifP (ps ++ c :: suf) ~
          (c, ifC) :: input.localizedRerootRankedChildTail c ifC (p :: (ps ++ suf))
      have hrankEq : ifC = ifP := by
        show
          (if input.compareLocalizedRerootCumulativeRule45Keys c previous = Ordering.eq
            then rank else rank + 1) =
            (if input.compareLocalizedRerootCumulativeRule45Keys p previous = Ordering.eq
              then rank else rank + 1)
        rw [Std.TransCmp.congr_left hpTied]
      rw [hrankEq]
      have hmove := ih p ifP hdescTail hpsTied
      have hcongr :
          input.localizedRerootRankedChildTail c ifP (ps ++ suf) =
            input.localizedRerootRankedChildTail p ifP (ps ++ suf) :=
        localizedRerootRankedChildTail_congr_previous input c p hcp ifP (ps ++ suf)
      have hunfoldC :
          input.localizedRerootRankedChildTail p ifP (c :: (ps ++ suf)) =
            (c, ifP) :: input.localizedRerootRankedChildTail p ifP (ps ++ suf) := by
        rw [localizedRerootRankedChildTail_eq_of_compare_eq input p c ifP hcp (ps ++ suf),
          hcongr]
      have hmove' :
          (input.localizedRerootRankedChildTail p ifP (ps ++ c :: suf)).Perm
            ((c, ifP) :: input.localizedRerootRankedChildTail p ifP (ps ++ suf)) :=
        hmove.trans (List.Perm.of_eq hunfoldC)
      have hunfoldP :
          input.localizedRerootRankedChildTail c ifP (p :: (ps ++ suf)) =
            (p, ifP) :: input.localizedRerootRankedChildTail p ifP (ps ++ suf) :=
        localizedRerootRankedChildTail_eq_of_compare_eq input c p ifP hpTied (ps ++ suf)
      calc
        (p, ifP) :: input.localizedRerootRankedChildTail p ifP (ps ++ c :: suf)
            ~ (p, ifP) ::
                ((c, ifP) :: input.localizedRerootRankedChildTail p ifP (ps ++ suf)) :=
              hmove'.cons (p, ifP)
        _ ~ (c, ifP) ::
              ((p, ifP) :: input.localizedRerootRankedChildTail p ifP (ps ++ suf)) :=
              List.Perm.swap (c, ifP) (p, ifP) _
        _ = (c, ifP) ::
              input.localizedRerootRankedChildTail c ifP (p :: (ps ++ suf)) := by
              rw [hunfoldP]

/-! ## Tail invariance for descending permutations -/

/-- The ranked tail of two descending permutations is permutation-invariant in the same
predecessor context.  The proof matches the two heads (which must be comparator-equal), moves the
matching head through the tied prefix of the second list, and recurses on the common tail. -/
theorem localizedRerootRankedChildTail_perm_of_descending
    (input : CertifiedLocalizedCIPInput) :
    ∀ (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat)
      {children permuted : List input.LocalizedRerootCumulativeRule45Key},
      input.LocalizedRerootCumulativeRule45KeysDescending (previous :: children) →
      input.LocalizedRerootCumulativeRule45KeysDescending (previous :: permuted) →
      children.Perm permuted →
      (input.localizedRerootRankedChildTail previous rank children).Perm
        (input.localizedRerootRankedChildTail previous rank permuted) := by
  intro previous rank children permuted hLeft hRight perm
  induction children generalizing previous rank permuted with
  | nil =>
      have empty : permuted = [] := perm.symm.eq_nil
      subst empty
      exact List.Perm.refl _
  | cons c cs ih =>
      cases permuted with
      | nil =>
          exact absurd perm.eq_nil (by simp)
      | cons b bs =>
          letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
            input.compareLocalizedRerootCumulativeRule45Keys_transCmp
          have hLeftC :
              input.LocalizedRerootCumulativeRule45KeysDescending (c :: cs) :=
            (List.pairwise_cons.mp hLeft).2
          have hRightB :
              input.LocalizedRerootCumulativeRule45KeysDescending (b :: bs) :=
            (List.pairwise_cons.mp hRight).2
          have hcmp :
              input.compareLocalizedRerootCumulativeRule45Keys c b = Ordering.eq :=
            compare_heads_eq_of_descending_perm input hLeftC hRightB perm
          have member : c ∈ b :: bs :=
            perm.mem_iff.mp (by simp)
          obtain ⟨pre, suf, decomposition⟩ := List.append_of_mem member
          obtain ⟨htied, hdescReorder⟩ :=
            tied_prefix_descending_reorder input hLeftC hRightB perm decomposition
          have hdescMove :
              input.LocalizedRerootCumulativeRule45KeysDescending
                (previous :: (pre ++ c :: suf)) := by
            rw [← decomposition]
            exact hRight
          have hmove :=
            localizedRerootRankedChildTail_move_tied input c pre suf previous rank
              hdescMove htied
          have htailPerm : cs.Perm (pre ++ suf) := by
            have combined : c :: cs ~ pre ++ c :: suf :=
              perm.trans (List.Perm.of_eq decomposition)
            have middle : c :: cs ~ c :: (pre ++ suf) :=
              combined.trans List.perm_middle
            exact List.Perm.cons_inv middle
          let r0 : Nat :=
            (if input.compareLocalizedRerootCumulativeRule45Keys c previous = Ordering.eq
              then rank else rank + 1)
          have ihTail := ih c r0 hLeftC hdescReorder htailPerm
          calc
            input.localizedRerootRankedChildTail previous rank (c :: cs)
                = (c, r0) :: input.localizedRerootRankedChildTail c r0 cs := rfl
            _ ~ (c, r0) :: input.localizedRerootRankedChildTail c r0 (pre ++ suf) :=
                  ihTail.cons (c, r0)
            _ = input.localizedRerootRankedChildTail previous rank (c :: (pre ++ suf)) := rfl
            _ ~ input.localizedRerootRankedChildTail previous rank (pre ++ c :: suf) :=
                  hmove.symm
            _ = input.localizedRerootRankedChildTail previous rank (b :: bs) := by
                  rw [decomposition]

/-! ## Moving a tied head through a prefix of a full ranked list -/

/-- Moving a maximal tied head to the front preserves the full ranked-children list up to
permutation (the first key always receives rank `0`). -/
theorem localizedRerootRankedChildren_move_tied_head
    (input : CertifiedLocalizedCIPInput)
    (c : input.LocalizedRerootCumulativeRule45Key)
    (pre suf : List input.LocalizedRerootCumulativeRule45Key)
    (hdesc :
      input.LocalizedRerootCumulativeRule45KeysDescending (pre ++ c :: suf))
    (htied :
      ∀ p ∈ pre,
        input.compareLocalizedRerootCumulativeRule45Keys p c = Ordering.eq) :
    (input.localizedRerootRankedChildren (pre ++ c :: suf)).Perm
      (input.localizedRerootRankedChildren (c :: (pre ++ suf))) := by
  cases pre with
  | nil => exact List.Perm.refl _
  | cons p ps =>
      letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
        input.compareLocalizedRerootCumulativeRule45Keys_transCmp
      have hpTied :
          input.compareLocalizedRerootCumulativeRule45Keys p c = Ordering.eq :=
        htied p (by simp)
      have hcp :
          input.compareLocalizedRerootCumulativeRule45Keys c p = Ordering.eq :=
        Std.OrientedCmp.eq_symm hpTied
      have hpsTied :
          ∀ q ∈ ps,
            input.compareLocalizedRerootCumulativeRule45Keys q c = Ordering.eq :=
        fun q inPs => htied q (List.mem_cons_of_mem p inPs)
      have hdescTail :
          input.LocalizedRerootCumulativeRule45KeysDescending
            (p :: (ps ++ c :: suf)) :=
        hdesc
      have hmove :=
        localizedRerootRankedChildTail_move_tied input c ps suf p 0 hdescTail hpsTied
      have hcongr :
          input.localizedRerootRankedChildTail c 0 (ps ++ suf) =
            input.localizedRerootRankedChildTail p 0 (ps ++ suf) :=
        localizedRerootRankedChildTail_congr_previous input c p hcp 0 (ps ++ suf)
      have hunfoldC :
          input.localizedRerootRankedChildTail p 0 (c :: (ps ++ suf)) =
            (c, 0) :: input.localizedRerootRankedChildTail p 0 (ps ++ suf) := by
        rw [localizedRerootRankedChildTail_eq_of_compare_eq input p c 0 hcp (ps ++ suf),
          hcongr]
      have hmove' :
          (input.localizedRerootRankedChildTail p 0 (ps ++ c :: suf)).Perm
            ((c, 0) :: input.localizedRerootRankedChildTail p 0 (ps ++ suf)) :=
        hmove.trans (List.Perm.of_eq hunfoldC)
      have hunfoldP :
          input.localizedRerootRankedChildTail c 0 (p :: (ps ++ suf)) =
            (p, 0) :: input.localizedRerootRankedChildTail p 0 (ps ++ suf) :=
        localizedRerootRankedChildTail_eq_of_compare_eq input c p 0 hpTied (ps ++ suf)
      calc
        input.localizedRerootRankedChildren (p :: (ps ++ c :: suf))
            = (p, 0) ::
                input.localizedRerootRankedChildTail p 0 (ps ++ c :: suf) := rfl
        _ ~ (p, 0) ::
              ((c, 0) :: input.localizedRerootRankedChildTail p 0 (ps ++ suf)) :=
              hmove'.cons (p, 0)
        _ ~ (c, 0) ::
              ((p, 0) :: input.localizedRerootRankedChildTail p 0 (ps ++ suf)) :=
              List.Perm.swap (c, 0) (p, 0) _
        _ = (c, 0) ::
              input.localizedRerootRankedChildTail c 0 (p :: (ps ++ suf)) := by
              rw [hunfoldP]
        _ = input.localizedRerootRankedChildren (c :: (p :: (ps ++ suf))) := rfl

/-! ## Main permutation-invariance theorem -/

/-- **Hierarchy-rank permutation invariance.**  Two descending permutations of the same list of
cumulative keys have permutation-equivalent ranked-children lists.  Consequently permutation-invariant
consumers of `localizedRerootRankedChildren`, such as the multiset of labels at a fixed rank,
are independent of the chosen descending representative. -/
theorem localizedRerootRankedChildren_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    {first second : List input.LocalizedRerootCumulativeRule45Key}
    (perm : first.Perm second)
    (hFirst : input.LocalizedRerootCumulativeRule45KeysDescending first)
    (hSecond : input.LocalizedRerootCumulativeRule45KeysDescending second) :
    (input.localizedRerootRankedChildren first).Perm
      (input.localizedRerootRankedChildren second) := by
  cases first with
  | nil =>
      have empty : second = [] := perm.symm.eq_nil
      subst empty
      exact List.Perm.refl _
  | cons a as =>
      cases second with
      | nil =>
          exact absurd perm.eq_nil (by simp)
      | cons b bs =>
          letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
            input.compareLocalizedRerootCumulativeRule45Keys_transCmp
          have hcmp :
              input.compareLocalizedRerootCumulativeRule45Keys a b = Ordering.eq :=
            compare_heads_eq_of_descending_perm input hFirst hSecond perm
          have member : a ∈ b :: bs :=
            perm.mem_iff.mp (by simp)
          obtain ⟨pre, suf, decomposition⟩ := List.append_of_mem member
          obtain ⟨htied, hdescReorder⟩ :=
            tied_prefix_descending_reorder input hFirst hSecond perm decomposition
          have hdescPre :
              input.LocalizedRerootCumulativeRule45KeysDescending (pre ++ a :: suf) := by
            rw [← decomposition]
            exact hSecond
          have hmove :=
            localizedRerootRankedChildren_move_tied_head input a pre suf hdescPre htied
          have htailPerm : as.Perm (pre ++ suf) := by
            have combined : a :: as ~ pre ++ a :: suf :=
              perm.trans (List.Perm.of_eq decomposition)
            have middle : a :: as ~ a :: (pre ++ suf) :=
              combined.trans List.perm_middle
            exact List.Perm.cons_inv middle
          have ihTail :=
            localizedRerootRankedChildTail_perm_of_descending input a 0
              hFirst hdescReorder htailPerm
          calc
            input.localizedRerootRankedChildren (a :: as)
                = (a, 0) ::
                    input.localizedRerootRankedChildTail a 0 as := rfl
            _ ~ (a, 0) ::
                  input.localizedRerootRankedChildTail a 0 (pre ++ suf) :=
                  ihTail.cons (a, 0)
            _ = input.localizedRerootRankedChildren (a :: (pre ++ suf)) := rfl
            _ ~ input.localizedRerootRankedChildren (pre ++ a :: suf) := hmove.symm
            _ = input.localizedRerootRankedChildren (b :: bs) := by
                  rw [decomposition]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
