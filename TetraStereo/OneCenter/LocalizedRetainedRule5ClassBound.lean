import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingProjection
import TetraStereo.OneCenter.DeclarativeCIPCompleteRootDescriptor
import TetraStereo.OneCenter.DeclarativeCIPRetainedCompleteSignatures
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Retained Rule 5 class bound

Equal retained prior keys and equal Boolean tag color determine the full Rule 5 key.
The color is the leading tagged alternative:

`(retainedTaggedAlternativeReferencesAt ...).headD none == some .junior`.

Count priority separates empty, one reference, and both references. Color separates the
two senses, and the two tagged orders of a both-reference signature. A complete tie stays
in the senior-first branch. Full-key injectivity then limits each prior class to two slots,
so `completeRule5PairCount` is `0`, `1`, or `2`. Counts `3` and `6` do not occur.

Sorted-permutation sign is not proved here.
-/

namespace TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound

open DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)
open scoped Classical

noncomputable section
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
variable (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)

local instance classBoundNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

def retainedRule5Color (graph : RootedDigraph Atom) (W D : ℕ) : Bool :=
  (retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).headD none ==
    some .junior

private def rule4bComponents (graph : RootedDigraph Atom) (W D : ℕ) : List (Key StereoLabel) :=
  (ofLex (ofLex (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D)).2).1

private def rule4cComponents (graph : RootedDigraph Atom) (W D : ℕ) : List (Key StereoLabel) :=
  (ofLex (ofLex (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D)).2).2

private theorem signature_eq_of_prior (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) :
    retainedCompletePriorSignatureAt molecule descriptorMap unit left W D =
      retainedCompletePriorSignatureAt molecule descriptorMap unit right W D := by
  simpa [retainedCompleteLigandPriorKeyAt_signature] using
    congrArg (fun key : CompleteLigandPriorKey => (ofLex key).2) hprior

private theorem countPriority_eq_of_prior (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) :
    (retainedReferenceSelection molecule descriptorMap unit left).countPriority =
      (retainedReferenceSelection molecule descriptorMap unit right).countPriority := by
  simpa [retainedCompletePriorSignatureAt_count] using
    congrArg (fun signature : CompletePriorSignature => (ofLex signature).1)
      (signature_eq_of_prior molecule descriptorMap unit left right W D hprior)

private theorem components_eq_of_prior (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) :
    rule4bComponents molecule descriptorMap unit left W D =
        rule4bComponents molecule descriptorMap unit right W D ∧
      rule4cComponents molecule descriptorMap unit left W D =
        rule4cComponents molecule descriptorMap unit right W D := by
  have hsig := signature_eq_of_prior molecule descriptorMap unit left right W D hprior
  refine ⟨?_, ?_⟩
  · simpa [rule4bComponents] using
      congrArg (fun signature : CompletePriorSignature => (ofLex (ofLex signature).2).1) hsig
  · simpa [rule4cComponents] using
      congrArg (fun signature : CompletePriorSignature => (ofLex (ofLex signature).2).2) hsig

private theorem rule4c_empty (graph : RootedDigraph Atom) (W D : ℕ)
    (hempty : retainedReferenceSelection molecule descriptorMap unit graph = .empty) :
    rule4cComponents molecule descriptorMap unit graph W D =
      [(ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D none)).2] := by
  simp [rule4cComponents, retainedCompletePriorSignatureAt, retainedCompleteReadingsAt, hempty,
    ofLex_toLex]

private theorem rule4b_one (graph : RootedDigraph Atom) (W D : ℕ) (sense : DescriptorSense)
    (hone : retainedReferenceSelection molecule descriptorMap unit graph = .one sense) :
    rule4bComponents molecule descriptorMap unit graph W D =
      [(ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some sense))).1] := by
  simp [rule4bComponents, retainedCompletePriorSignatureAt, retainedCompleteReadingsAt, hone,
    ofLex_toLex, ReferenceSelection.countPriority]

private theorem rule4b_both_lt (graph : RootedDigraph Atom) (W D : ℕ)
    (hboth : retainedReferenceSelection molecule descriptorMap unit graph = .both)
    (hlt : compare
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) = .lt) :
    rule4bComponents molecule descriptorMap unit graph W D =
      [(ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior))).1,
        (ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))).1] := by
  simp [rule4bComponents, retainedCompletePriorSignatureAt, retainedCompleteReadingsAt, hboth,
    ofLex_toLex, ReferenceSelection.countPriority]
  have strict := (completeReading_compare_lt_iff _ _).1 hlt
  rw [max_eq_right strict.le, min_eq_left strict.le]
  exact ⟨rfl, rfl⟩

private theorem rule4b_both_not_lt (graph : RootedDigraph Atom) (W D : ℕ)
    (hboth : retainedReferenceSelection molecule descriptorMap unit graph = .both)
    (hlt : ¬ compare
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) = .lt) :
    rule4bComponents molecule descriptorMap unit graph W D =
      [(ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))).1,
        (ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior))).1] := by
  simp [rule4bComponents, retainedCompletePriorSignatureAt, retainedCompleteReadingsAt, hboth,
    ofLex_toLex, ReferenceSelection.countPriority]
  have le :
      retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior) ≤
        retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior) :=
    le_of_not_gt fun strict => hlt ((completeReading_compare_lt_iff _ _).2 strict)
  rw [max_eq_left le, min_eq_right le]
  exact ⟨rfl, rfl⟩

private theorem stream_empty (graph : RootedDigraph Atom) (W D : ℕ)
    (hempty : retainedReferenceSelection molecule descriptorMap unit graph = .empty) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D .senior =
      [retainedCompleteRule5ReadingAt molecule descriptorMap unit graph W D none .senior] := by
  simp [retainedCompleteRule5ReadingsAt, retainedTaggedAlternativeReferencesAt, hempty]

private theorem stream_one (graph : RootedDigraph Atom) (W D : ℕ) (sense : DescriptorSense)
    (hone : retainedReferenceSelection molecule descriptorMap unit graph = .one sense) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D .senior =
      [retainedCompleteRule5ReadingAt molecule descriptorMap unit graph W D (some sense) .senior] := by
  simp [retainedCompleteRule5ReadingsAt, retainedTaggedAlternativeReferencesAt, hone]

private theorem none_reading_congr (left right : RootedDigraph Atom) (W D : ℕ)
    (hc : (ofLex (retainedCompleteReadingAt molecule descriptorMap unit left W D none)).2 =
      (ofLex (retainedCompleteReadingAt molecule descriptorMap unit right W D none)).2) :
    retainedCompleteRule5ReadingAt molecule descriptorMap unit left W D none .senior =
      retainedCompleteRule5ReadingAt molecule descriptorMap unit right W D none .senior := by
  simp [retainedCompleteRule5ReadingAt, hc]

private theorem some_reading_congr (left right : RootedDigraph Atom) (W D : ℕ)
    (sense : DescriptorSense)
    (hb : (ofLex (retainedCompleteReadingAt molecule descriptorMap unit left W D (some sense))).1 =
      (ofLex (retainedCompleteReadingAt molecule descriptorMap unit right W D (some sense))).1) :
    retainedCompleteRule5ReadingAt molecule descriptorMap unit left W D (some sense) .senior =
      retainedCompleteRule5ReadingAt molecule descriptorMap unit right W D (some sense) .senior := by
  simp [retainedCompleteRule5ReadingAt, hb]

private theorem color_one (graph : RootedDigraph Atom) (W D : ℕ) (sense : DescriptorSense)
    (hone : retainedReferenceSelection molecule descriptorMap unit graph = .one sense) :
    retainedRule5Color molecule descriptorMap unit graph W D = (some sense == some .junior) := by
  simp [retainedRule5Color, retainedTaggedAlternativeReferencesAt, hone, List.headD]

private theorem head_both (graph : RootedDigraph Atom) (W D : ℕ)
    (hboth : retainedReferenceSelection molecule descriptorMap unit graph = .both) :
    (retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).headD none =
      let senior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
      let junior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      if compare senior junior = .lt then some .junior else some .senior := by
  simp [retainedTaggedAlternativeReferencesAt, hboth, List.headD]
  by_cases hlt : compare
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) = .lt
  · simp [hlt]
  · simp [hlt]

private theorem key_of_streams (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hstream : retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
      retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D := by
  unfold retainedCompleteLigandRule5KeyAt
  rw [hprior, hstream]

/-- Equal prior keys and equal leading tag color determine the retained Rule 5 key. -/
theorem retainedCompleteLigandRule5KeyAt_eq_of_prior_of_color
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hcolor : retainedRule5Color molecule descriptorMap unit left W D =
      retainedRule5Color molecule descriptorMap unit right W D) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D := by
  have hcount := countPriority_eq_of_prior molecule descriptorMap unit left right W D hprior
  have hcomp := components_eq_of_prior molecule descriptorMap unit left right W D hprior
  cases hL : retainedReferenceSelection molecule descriptorMap unit left with
  | empty =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty =>
          have hcLists := hcomp.2
          rw [rule4c_empty molecule descriptorMap unit left W D hL,
            rule4c_empty molecule descriptorMap unit right W D hR] at hcLists
          have hc := (List.cons_eq_cons.mp hcLists).1
          have hreading := none_reading_congr molecule descriptorMap unit left right W D hc
          have hstream :
              retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior := by
            rw [stream_empty molecule descriptorMap unit left W D hL,
              stream_empty molecule descriptorMap unit right W D hR, hreading]
          exact key_of_streams molecule descriptorMap unit left right W D hprior hstream
      | one sense =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | both =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
  | one senseL =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | both =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | one senseR =>
          cases senseL <;> cases senseR
          · have hbLists := hcomp.1
            rw [rule4b_one molecule descriptorMap unit left W D .senior hL,
              rule4b_one molecule descriptorMap unit right W D .senior hR] at hbLists
            have hb := (List.cons_eq_cons.mp hbLists).1
            have hreading :=
              some_reading_congr molecule descriptorMap unit left right W D .senior hb
            have hstream :
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                  retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior := by
              rw [stream_one molecule descriptorMap unit left W D .senior hL,
                stream_one molecule descriptorMap unit right W D .senior hR, hreading]
            exact key_of_streams molecule descriptorMap unit left right W D hprior hstream
          · rw [color_one molecule descriptorMap unit left W D .senior hL,
              color_one molecule descriptorMap unit right W D .junior hR] at hcolor
            exact absurd hcolor (by decide)
          · rw [color_one molecule descriptorMap unit left W D .junior hL,
              color_one molecule descriptorMap unit right W D .senior hR] at hcolor
            exact absurd hcolor (by decide)
          · have hbLists := hcomp.1
            rw [rule4b_one molecule descriptorMap unit left W D .junior hL,
              rule4b_one molecule descriptorMap unit right W D .junior hR] at hbLists
            have hb := (List.cons_eq_cons.mp hbLists).1
            have hreading :=
              some_reading_congr molecule descriptorMap unit left right W D .junior hb
            have hstream :
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                  retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior := by
              rw [stream_one molecule descriptorMap unit left W D .junior hL,
                stream_one molecule descriptorMap unit right W D .junior hR, hreading]
            exact key_of_streams molecule descriptorMap unit left right W D hprior hstream
  | both =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | one sense =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | both =>
          let seniorL := retainedCompleteReadingAt molecule descriptorMap unit left W D (some .senior)
          let juniorL := retainedCompleteReadingAt molecule descriptorMap unit left W D (some .junior)
          let seniorR := retainedCompleteReadingAt molecule descriptorMap unit right W D (some .senior)
          let juniorR := retainedCompleteReadingAt molecule descriptorMap unit right W D (some .junior)
          by_cases hltL : compare seniorL juniorL = .lt <;>
            by_cases hltR : compare seniorR juniorR = .lt
          · have hbLists := hcomp.1
            rw [rule4b_both_lt molecule descriptorMap unit left W D hL hltL,
              rule4b_both_lt molecule descriptorMap unit right W D hR hltR] at hbLists
            have hj := (List.cons_eq_cons.mp hbLists).1
            have hs := (List.cons_eq_cons.mp (List.cons_eq_cons.mp hbLists).2).1
            have hstream :
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                  retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior := by
              unfold retainedCompleteRule5ReadingsAt retainedTaggedAlternativeReferencesAt
              simp only [hL, hR]
              rw [if_pos hltL, if_pos hltR]
              simp [retainedCompleteRule5ReadingAt, hj, hs]
            exact key_of_streams molecule descriptorMap unit left right W D hprior hstream
          · have hheadL := head_both molecule descriptorMap unit left W D hL
            have hheadR := head_both molecule descriptorMap unit right W D hR
            rw [retainedRule5Color, retainedRule5Color, hheadL, hheadR, if_pos hltL,
              if_neg hltR] at hcolor
            exact absurd hcolor (by decide)
          · have hheadL := head_both molecule descriptorMap unit left W D hL
            have hheadR := head_both molecule descriptorMap unit right W D hR
            rw [retainedRule5Color, retainedRule5Color, hheadL, hheadR, if_neg hltL,
              if_pos hltR] at hcolor
            exact absurd hcolor (by decide)
          · have hbLists := hcomp.1
            rw [rule4b_both_not_lt molecule descriptorMap unit left W D hL hltL,
              rule4b_both_not_lt molecule descriptorMap unit right W D hR hltR] at hbLists
            have hs := (List.cons_eq_cons.mp hbLists).1
            have hj := (List.cons_eq_cons.mp (List.cons_eq_cons.mp hbLists).2).1
            have hstream :
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                  retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior := by
              unfold retainedCompleteRule5ReadingsAt retainedTaggedAlternativeReferencesAt
              simp only [hL, hR]
              rw [if_neg hltL, if_neg hltR]
              simp [retainedCompleteRule5ReadingAt, hs, hj]
            exact key_of_streams molecule descriptorMap unit left right W D hprior hstream

private theorem bool3_distinct (a b c : Bool) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  cases a <;> cases b <;> cases c <;> first | exact hab rfl | exact hac rfl | exact hbc rfl

/-- Distinct full keys give each prior class at most two slots. -/
theorem retainedPriorClass_atMostTwo
    (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ)
    (inj : Function.Injective (fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D))
    (i j k : Fin 4)
    (hij : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs i) W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs j) W D)
    (hik : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs i) W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs k) W D) :
    j = k ∨ j = i ∨ k = i := by
  by_cases hjk : j = k
  · exact Or.inl hjk
  by_cases hji : j = i
  · exact Or.inr (Or.inl hji)
  by_cases hki : k = i
  · exact Or.inr (Or.inr hki)
  have color_ne {a b : Fin 4} (hne : a ≠ b)
      (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs a) W D =
        retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs b) W D) :
      retainedRule5Color molecule descriptorMap unit (graphs a) W D ≠
        retainedRule5Color molecule descriptorMap unit (graphs b) W D := by
    intro same
    exact hne (inj (retainedCompleteLigandRule5KeyAt_eq_of_prior_of_color molecule descriptorMap
      unit (graphs a) (graphs b) W D hprior same))
  have cij := color_ne (Ne.symm hji) hij
  have cik := color_ne (Ne.symm hki) hik
  have cjk := color_ne hjk (hij.symm.trans hik)
  exact (bool3_distinct _ _ _ cij cik cjk).elim

private theorem priorPair_partner
    (keys : Fin 4 → CompleteLigandRule5Key)
    (atMost : ∀ i j k : Fin 4, (ofLex (keys i)).1 = (ofLex (keys j)).1 →
      (ofLex (keys i)).1 = (ofLex (keys k)).1 → j = k ∨ j = i ∨ k = i)
    {i j k : Fin 4} (hij : CompletePriorPair keys i j) (hik : CompletePriorPair keys i k) :
    j = k := by
  rcases atMost i j k hij.2 hik.2 with h | h | h
  · exact h
  · exact (hij.1 h.symm).elim
  · exact (hik.1 h.symm).elim

private theorem ite3_le_one {a b c : Prop} [Decidable a] [Decidable b] [Decidable c]
    (hab : a → b → False) (hac : a → c → False) (hbc : b → c → False) :
    (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) ≤ 1 := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c
  · exact (hab ha hb).elim
  · exact (hab ha hb).elim
  · exact (hac ha hc).elim
  · simp [ha, hb, hc]
  · exact (hbc hb hc).elim
  · simp [ha, hb, hc]
  · simp [ha, hb, hc]
  · simp [ha, hb, hc]

/-- Injective retained Rule 5 keys have at most two prior ties among four slots. -/
theorem completeRule5PairCount_le_two_of_injective
    (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ)
    (inj : Function.Injective (fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)) :
    completeRule5PairCount (fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D) ≤ 2 := by
  let keys := fun slot =>
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D
  have atMost : ∀ i j k : Fin 4, (ofLex (keys i)).1 = (ofLex (keys j)).1 →
      (ofLex (keys i)).1 = (ofLex (keys k)).1 → j = k ∨ j = i ∨ k = i := by
    intro i j k hij hik
    exact retainedPriorClass_atMostTwo molecule descriptorMap unit graphs W D inj i j k
      (by simpa [keys, retainedCompleteLigandRule5KeyAt_prior] using hij)
      (by simpa [keys, retainedCompleteLigandRule5KeyAt_prior] using hik)
  let P := CompletePriorPair keys
  have flip {i j : Fin 4} (h : P i j) : P j i := ⟨h.1.symm, h.2.symm⟩
  have exclusive {i j k : Fin 4} (hij : P i j) (hik : P i k) (hne : j ≠ k) : False :=
    hne (priorPair_partner keys atMost hij hik)
  have d0 := ite3_le_one (a := P 0 1) (b := P 0 2) (c := P 0 3)
    (fun h1 h2 => exclusive h1 h2 (by decide))
    (fun h1 h3 => exclusive h1 h3 (by decide))
    (fun h2 h3 => exclusive h2 h3 (by decide))
  have d1 := ite3_le_one (a := P 0 1) (b := P 1 2) (c := P 1 3)
    (fun h1 h2 => exclusive (flip h1) h2 (by decide))
    (fun h1 h3 => exclusive (flip h1) h3 (by decide))
    (fun h2 h3 => exclusive h2 h3 (by decide))
  have d2 := ite3_le_one (a := P 0 2) (b := P 1 2) (c := P 2 3)
    (fun h1 h2 => exclusive (flip h1) (flip h2) (by decide))
    (fun h1 h3 => exclusive (flip h1) h3 (by decide))
    (fun h2 h3 => exclusive (flip h2) h3 (by decide))
  have d3 := ite3_le_one (a := P 0 3) (b := P 1 3) (c := P 2 3)
    (fun h1 h2 => exclusive (flip h1) (flip h2) (by decide))
    (fun h1 h3 => exclusive (flip h1) (flip h3) (by decide))
    (fun h2 h3 => exclusive (flip h2) (flip h3) (by decide))
  have hdouble :
      ((if P 0 1 then 1 else 0) + (if P 0 2 then 1 else 0) + (if P 0 3 then 1 else 0)) +
        ((if P 0 1 then 1 else 0) + (if P 1 2 then 1 else 0) + (if P 1 3 then 1 else 0)) +
        ((if P 0 2 then 1 else 0) + (if P 1 2 then 1 else 0) + (if P 2 3 then 1 else 0)) +
        ((if P 0 3 then 1 else 0) + (if P 1 3 then 1 else 0) + (if P 2 3 then 1 else 0)) =
      2 * completeRule5PairCount keys := by
    simp [completeRule5PairCount, sourceEnantiomorphicPairCount, P]
    omega
  have hsum :
      ((if P 0 1 then 1 else 0) + (if P 0 2 then 1 else 0) + (if P 0 3 then 1 else 0)) +
        ((if P 0 1 then 1 else 0) + (if P 1 2 then 1 else 0) + (if P 1 3 then 1 else 0)) +
        ((if P 0 2 then 1 else 0) + (if P 1 2 then 1 else 0) + (if P 2 3 then 1 else 0)) +
        ((if P 0 3 then 1 else 0) + (if P 1 3 then 1 else 0) + (if P 2 3 then 1 else 0)) ≤ 4 := by
    omega
  have htwo : 2 * completeRule5PairCount keys ≤ 4 := by
    rw [← hdouble]
    exact hsum
  have : completeRule5PairCount keys ≤ 2 := by omega
  simpa [keys] using this

/-- The only injective prior-pair counts are the ones that match uppercase reflection. -/
theorem completeRule5PairCount_even_or_one_of_injective
    (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ)
    (inj : Function.Injective (fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)) :
    Even (completeRule5PairCount (fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)) ∨
      completeRule5PairCount (fun slot =>
        retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D) = 1 := by
  have hle := completeRule5PairCount_le_two_of_injective molecule descriptorMap unit graphs W D inj
  generalize hcount : completeRule5PairCount (fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D) = n at hle
  have hsplit : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hsplit with rfl | rfl | rfl
  · exact Or.inl ⟨0, by omega⟩
  · exact Or.inr rfl
  · exact Or.inl ⟨1, by omega⟩

end

end TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound

assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound.retainedCompleteLigandRule5KeyAt_eq_of_prior_of_color
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound.retainedPriorClass_atMostTwo
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound.completeRule5PairCount_le_two_of_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound.completeRule5PairCount_even_or_one_of_injective
