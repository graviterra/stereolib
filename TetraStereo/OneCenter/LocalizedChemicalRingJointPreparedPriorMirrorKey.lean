import TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound
import TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Common-layout prior-tie mirror key equality

This module proves the cross-map Rule-5 key algebra needed by the physical mirror bridge.
The source side is an original descriptor map at a graph `left`; the image side is the
reflected descriptor map at a graph `right`.  Both sides use the *same* layout parameters
`W` and `D`.  Equality of the retained prior keys and injectivity of the original full key
table force the two original full keys to be distinct, hence their binary Rule-5 colors to
differ.  The reflected senior stream at `right` then equals the original senior stream at
`left`, and the corresponding full keys agree.

The result is deliberately stated for one common graph family and one common `(W, D)`.
It does not assert equality of independently chosen `rawStateFrames` windows.  A producer
that has the actual generated states must transfer these keys to the common mosaic layout
by the existing builder-locality lemmas.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey

open DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)
open LocalizedRetainedRule5ClassBound
open LocalizedRetainedDescriptorTransport
open scoped Classical

noncomputable section
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
variable (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)

local instance priorMirrorKeyNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

/-- The prior projection of a tied prior key gives equal complete prior signatures. -/
private theorem priorSignature_eq_of_prior
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) :
    retainedCompletePriorSignatureAt molecule descriptorMap unit left W D =
      retainedCompletePriorSignatureAt molecule descriptorMap unit right W D := by
  simpa [retainedCompleteLigandPriorKeyAt_signature] using
    congrArg (fun key : CompleteLigandPriorKey => (ofLex key).2) hprior

private def priorRule4bList (signature : CompletePriorSignature) : List (Key StereoLabel) :=
  (ofLex (ofLex signature).2).1

private def priorRule4cList (signature : CompletePriorSignature) : List (Key StereoLabel) :=
  (ofLex (ofLex signature).2).2

private theorem priorRule4bList_eq (graph : RootedDigraph Atom) (W D : ℕ) :
    priorRule4bList (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D) =
      let selection := retainedReferenceSelection molecule descriptorMap unit graph
      let readings := retainedCompleteReadingsAt molecule descriptorMap unit graph W D
      if selection = .empty then [] else readings.map fun key => (ofLex key).1 := by
  simp [priorRule4bList, retainedCompletePriorSignatureAt]

private theorem priorRule4cList_eq (graph : RootedDigraph Atom) (W D : ℕ) :
    priorRule4cList (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D) =
      (retainedCompleteReadingsAt molecule descriptorMap unit graph W D).map fun key =>
        (ofLex key).2 := by
  simp [priorRule4cList, retainedCompletePriorSignatureAt]

private theorem priorRule4bList_one (graph : RootedDigraph Atom) (W D : ℕ)
    (sense : DescriptorSense)
    (hone : retainedReferenceSelection molecule descriptorMap unit graph = .one sense) :
    priorRule4bList (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D) =
      [(ofLex (retainedCompleteReadingAt molecule descriptorMap unit graph W D
        (some sense))).1] := by
  simp [priorRule4bList, retainedCompletePriorSignatureAt, retainedCompleteReadingsAt, hone,
    ofLex_toLex, ReferenceSelection.countPriority]

/-- The binary Rule-5 color of a `both`-reference graph is the truth value of the strict
senior-before-junior comparison. -/
private theorem priorColor_both (graph : RootedDigraph Atom) (W D : ℕ)
    (hboth : retainedReferenceSelection molecule descriptorMap unit graph = .both) :
    retainedRule5Color molecule descriptorMap unit graph W D =
      decide (compare
        (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
        (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) =
          Ordering.lt) := by
  unfold retainedRule5Color
  have hhead :
      (retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D).headD none =
        let senior := retainedCompleteReadingAt molecule descriptorMap unit graph W D
          (some .senior)
        let junior := retainedCompleteReadingAt molecule descriptorMap unit graph W D
          (some .junior)
        if compare senior junior = Ordering.lt then some .junior else some .senior := by
    simp only [retainedTaggedAlternativeReferencesAt, hboth]
    split_ifs <;> rfl
  rw [hhead]
  by_cases hlt : compare
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) =
        Ordering.lt
  · simp [hlt]
  · simp [hlt]

private theorem priorColor_empty (graph : RootedDigraph Atom) (W D : ℕ)
    (hempty : retainedReferenceSelection molecule descriptorMap unit graph = .empty) :
    retainedRule5Color molecule descriptorMap unit graph W D = false := by
  simp [retainedRule5Color, retainedTaggedAlternativeReferencesAt, hempty, List.headD]

private theorem priorColor_one (graph : RootedDigraph Atom) (W D : ℕ)
    (sense : DescriptorSense)
    (hone : retainedReferenceSelection molecule descriptorMap unit graph = .one sense) :
    retainedRule5Color molecule descriptorMap unit graph W D =
      (some sense == some .junior) := by
  simp [retainedRule5Color, retainedTaggedAlternativeReferencesAt, hone, List.headD]

private theorem priorColor_both_tie (graph : RootedDigraph Atom) (W D : ℕ)
    (hboth : retainedReferenceSelection molecule descriptorMap unit graph = .both)
    (htie : compare
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) =
        Ordering.eq) :
    retainedRule5Color molecule descriptorMap unit graph W D = false := by
  rw [priorColor_both molecule descriptorMap unit graph W D hboth]
  simp [htie]

private theorem priorStream_one (graph : RootedDigraph Atom) (W D : ℕ)
    (sense : DescriptorSense) (common : DescriptorSense)
    (hone : retainedReferenceSelection molecule descriptorMap unit graph = .one sense) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common =
      [retainedCompleteRule5ReadingAt molecule descriptorMap unit graph W D
        (some sense) common] := by
  simp [retainedCompleteRule5ReadingsAt, retainedTaggedAlternativeReferencesAt, hone]

private theorem priorReading_some_congr
    (left right : RootedDigraph Atom) (W D : ℕ)
    (senseL senseR commonL commonR : DescriptorSense)
    (hcomp : (ofLex (retainedCompleteReadingAt molecule descriptorMap unit left W D
      (some senseL))).1 =
      (ofLex (retainedCompleteReadingAt molecule descriptorMap unit right W D
        (some senseR))).1)
    (hlabel : absoluteRule5Label senseL commonL = absoluteRule5Label senseR commonR) :
    retainedCompleteRule5ReadingAt molecule descriptorMap unit left W D
        (some senseL) commonL =
      retainedCompleteRule5ReadingAt molecule descriptorMap unit right W D
        (some senseR) commonR := by
  simp [retainedCompleteRule5ReadingAt, hcomp, hlabel]

private def priorBothStream (seniorComp juniorComp : Key StereoLabel) (seniorNotLt : Bool)
    (common : DescriptorSense) : List (Key StereoLabel) :=
  if seniorNotLt then
    [mapObservationKey (absoluteRule5Label .senior common) seniorComp,
      mapObservationKey (absoluteRule5Label .junior common) juniorComp]
  else
    [mapObservationKey (absoluteRule5Label .junior common) seniorComp,
      mapObservationKey (absoluteRule5Label .senior common) juniorComp]

private theorem priorAbsoluteRule5Label_cross (own : DescriptorSense) :
    absoluteRule5Label own own.mirror = absoluteRule5Label own.mirror own := by
  cases own <;> rfl

private theorem priorAbsoluteRule5Label_same (own : DescriptorSense) :
    absoluteRule5Label own own = absoluteRule5Label own.mirror own.mirror := by
  cases own <;> rfl

private theorem priorBothStream_junior (seniorComp juniorComp : Key StereoLabel)
    (seniorNotLt : Bool) :
    priorBothStream seniorComp juniorComp seniorNotLt .junior =
      priorBothStream seniorComp juniorComp (!seniorNotLt) .senior := by
  cases seniorNotLt with
  | false =>
      simp only [priorBothStream, Bool.not_false]
      rw [if_neg (by decide : ¬ false = true)]
      exact congrArg₂ (fun x y => [x, y])
        (congrArg (fun label => mapObservationKey label seniorComp)
          (priorAbsoluteRule5Label_same .junior))
        (congrArg (fun label => mapObservationKey label juniorComp)
          (priorAbsoluteRule5Label_cross .senior))
  | true =>
      simp only [priorBothStream, Bool.not_true]
      rw [if_neg (by decide : ¬ false = true)]
      exact congrArg₂ (fun x y => [x, y])
        (congrArg (fun label => mapObservationKey label seniorComp)
          (priorAbsoluteRule5Label_cross .senior))
        (congrArg (fun label => mapObservationKey label juniorComp)
          (priorAbsoluteRule5Label_same .junior))

private theorem priorReadings_both (graph : RootedDigraph Atom) (W D : ℕ)
    (hboth : retainedReferenceSelection molecule descriptorMap unit graph = .both)
    (common : DescriptorSense) :
    let senior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
    let junior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common =
      priorBothStream (ofLex (max senior junior)).1 (ofLex (min senior junior)).1
        (decide (compare senior junior ≠ .lt)) common := by
  intro senior junior
  unfold retainedCompleteRule5ReadingsAt retainedTaggedAlternativeReferencesAt
  simp only [hboth]
  by_cases hlt : compare senior junior = Ordering.lt
  · rw [if_pos hlt]
    have hsj : senior < junior := (completeReading_compare_lt_iff senior junior).1 hlt
    have hdec : decide (compare senior junior ≠ Ordering.lt) = false := by simp [hlt]
    simp only [List.map_cons, List.map_nil, retainedCompleteRule5ReadingAt, hdec,
      max_eq_right (le_of_lt hsj), min_eq_left (le_of_lt hsj), priorBothStream,
      Bool.false_eq_true, if_false]
    rfl
  · rw [if_neg hlt]
    have hle : junior ≤ senior := le_of_not_gt fun strict =>
      hlt ((completeReading_compare_lt_iff senior junior).2 strict)
    have hdec : decide (compare senior junior ≠ Ordering.lt) = true := by simp [hlt]
    simp only [List.map_cons, List.map_nil, retainedCompleteRule5ReadingAt, hdec,
      max_eq_left hle, min_eq_right hle, priorBothStream, if_true]
    rfl

/-- Prior-signature equality extracts the two descending Rule-4b components and the equivalence
of complete ties for two `both`-reference readings. -/
private theorem priorSignature_components_both
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hselL : retainedReferenceSelection molecule descriptorMap unit left = .both)
    (hselR : retainedReferenceSelection molecule descriptorMap unit right = .both)
    (hsig : retainedCompletePriorSignatureAt molecule descriptorMap unit left W D =
      retainedCompletePriorSignatureAt molecule descriptorMap unit right W D) :
    let sL := retainedCompleteReadingAt molecule descriptorMap unit left W D (some .senior)
    let jL := retainedCompleteReadingAt molecule descriptorMap unit left W D (some .junior)
    let sR := retainedCompleteReadingAt molecule descriptorMap unit right W D (some .senior)
    let jR := retainedCompleteReadingAt molecule descriptorMap unit right W D (some .junior)
    (ofLex (max sL jL)).1 = (ofLex (max sR jR)).1 ∧
      (ofLex (min sL jL)).1 = (ofLex (min sR jR)).1 ∧
        ((compare sL jL = .eq) ↔ (compare sR jR = .eq)) := by
  intro sL jL sR jR
  have hlists := congrArg priorRule4bList hsig
  rw [priorRule4bList_eq molecule descriptorMap unit left W D,
    priorRule4bList_eq molecule descriptorMap unit right W D, hselL, hselR] at hlists
  simp only [retainedCompleteReadingsAt, hselL, hselR, List.map_cons, List.map_nil] at hlists
  injection hlists with hmax htail
  injection htail with hmin _
  refine ⟨hmax, hmin, ?_⟩
  have h4cLists := congrArg priorRule4cList hsig
  rw [priorRule4cList_eq molecule descriptorMap unit left W D,
    priorRule4cList_eq molecule descriptorMap unit right W D] at h4cLists
  simp only [retainedCompleteReadingsAt, hselL, hselR, List.map_cons, List.map_nil] at h4cLists
  injection h4cLists with h4cMax h4cTail
  injection h4cTail with h4cMin _
  constructor
  · intro heq
    have hsj : sL = jL := (completeReading_compare_eq_iff sL jL).1 heq
    have hpair : max sL jL = min sL jL := by simp [hsj]
    have h4b : (ofLex (max sR jR)).1 = (ofLex (min sR jR)).1 := by
      rw [← hmax, ← hmin, hpair]
    have h4c : (ofLex (max sR jR)).2 = (ofLex (min sR jR)).2 := by
      rw [← h4cMax, ← h4cMin, hpair]
    have hR : max sR jR = min sR jR :=
      Equiv.injective ofLex (Prod.ext h4b h4c)
    have hsr : sR = jR := by
      rcases le_total jR sR with hle | hle
      · rwa [max_eq_left hle, min_eq_right hle] at hR
      · have hflip := hR
        rw [max_eq_right hle, min_eq_left hle] at hflip
        exact hflip.symm
    exact (completeReading_compare_eq_iff sR jR).2 hsr
  · intro heq
    have hsj : sR = jR := (completeReading_compare_eq_iff sR jR).1 heq
    have hpair : max sR jR = min sR jR := by simp [hsj]
    have h4b : (ofLex (max sL jL)).1 = (ofLex (min sL jL)).1 := by
      rw [hmax, hmin, hpair]
    have h4c : (ofLex (max sL jL)).2 = (ofLex (min sL jL)).2 := by
      rw [h4cMax, h4cMin, hpair]
    have hKeys : max sL jL = min sL jL :=
      Equiv.injective ofLex (Prod.ext h4b h4c)
    have hsr : sL = jL := by
      rcases le_total jL sL with hle | hle
      · rwa [max_eq_left hle, min_eq_right hle] at hKeys
      · have hflip := hKeys
        rw [max_eq_right hle, min_eq_left hle] at hflip
        exact hflip.symm
    exact (completeReading_compare_eq_iff sL jL).2 hsr

private theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

private theorem decide_ne_lt_eq_not_decide_eq_lt {o : Ordering} (hne : o ≠ .eq) :
    decide (o ≠ .lt) = !decide (o = .lt) := by
  cases o <;> simp_all

/-- Equal prior keys and unequal original full keys force unequal binary Rule-5 colors. -/
private theorem priorColor_ne_of_prior_of_key_ne
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) :
    retainedRule5Color molecule descriptorMap unit left W D ≠
      retainedRule5Color molecule descriptorMap unit right W D := by
  intro hcolor
  exact hkey (retainedCompleteLigandRule5KeyAt_eq_of_prior_of_color
    molecule descriptorMap unit left right W D hprior hcolor)

/-- Under a prior tie with different binary colors, the original senior stream at `left`
equals the original junior stream at `right`.  This is the exact reading algebra behind the
cross-map key equality; it is proved from the common prior signature, not assumed. -/
private theorem priorReadings_cross_of_prior_of_color_ne
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hcolor_ne : retainedRule5Color molecule descriptorMap unit left W D ≠
      retainedRule5Color molecule descriptorMap unit right W D) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
      retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .junior := by
  have hsig := priorSignature_eq_of_prior molecule descriptorMap unit left right W D hprior
  have hcount :=
    congrArg (fun signature : CompletePriorSignature => (ofLex signature).1) hsig
  have hcount' :
      (retainedReferenceSelection molecule descriptorMap unit left).countPriority =
        (retainedReferenceSelection molecule descriptorMap unit right).countPriority := by
    simpa only [retainedCompletePriorSignatureAt_count] using hcount
  cases hL : retainedReferenceSelection molecule descriptorMap unit left with
  | empty =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty =>
          have hcL := priorColor_empty molecule descriptorMap unit left W D hL
          have hcR := priorColor_empty molecule descriptorMap unit right W D hR
          exact False.elim (hcolor_ne (hcL.trans hcR.symm))
      | one sense =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount'
      | both =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount'
  | one senseL =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount'
      | both =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount'
      | one senseR =>
          have hcomp := congrArg priorRule4bList hsig
          rw [priorRule4bList_one molecule descriptorMap unit left W D senseL hL,
            priorRule4bList_one molecule descriptorMap unit right W D senseR hR] at hcomp
          have hb : (ofLex (retainedCompleteReadingAt molecule descriptorMap unit left W D
              (some senseL))).1 =
              (ofLex (retainedCompleteReadingAt molecule descriptorMap unit right W D
                (some senseR))).1 :=
            (List.cons_eq_cons.mp hcomp).1
          have hsenses : senseL ≠ senseR := by
            intro hsame
            apply hcolor_ne
            rw [priorColor_one molecule descriptorMap unit left W D senseL hL,
              priorColor_one molecule descriptorMap unit right W D senseR hR, hsame]
          have hlabel : absoluteRule5Label senseL .senior =
              absoluteRule5Label senseR .junior := by
            cases senseL <;> cases senseR
            · exact (hsenses rfl).elim
            · simpa [DescriptorSense.mirror] using priorAbsoluteRule5Label_same .senior
            · simpa [DescriptorSense.mirror] using priorAbsoluteRule5Label_cross .junior
            · exact (hsenses rfl).elim
          have hreading := priorReading_some_congr molecule descriptorMap unit left right W D
            senseL senseR .senior .junior hb hlabel
          rw [priorStream_one molecule descriptorMap unit left W D senseL .senior hL,
            priorStream_one molecule descriptorMap unit right W D senseR .junior hR,
            hreading]
  | both =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount'
      | one sense =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount'
      | both =>
          let sL := retainedCompleteReadingAt molecule descriptorMap unit left W D
            (some .senior)
          let jL := retainedCompleteReadingAt molecule descriptorMap unit left W D
            (some .junior)
          let sR := retainedCompleteReadingAt molecule descriptorMap unit right W D
            (some .senior)
          let jR := retainedCompleteReadingAt molecule descriptorMap unit right W D
            (some .junior)
          obtain ⟨hmax, hmin, heqIff⟩ :=
            priorSignature_components_both molecule descriptorMap unit left right W D
              hL hR hsig
          have hcolorBool :
              decide (compare sL jL = Ordering.lt) ≠
                decide (compare sR jR = Ordering.lt) := by
            intro hdec
            apply hcolor_ne
            rw [priorColor_both molecule descriptorMap unit left W D hL,
              priorColor_both molecule descriptorMap unit right W D hR]
            exact hdec
          have hneL : compare sL jL ≠ Ordering.eq := by
            intro heqL
            have heqR : compare sR jR = Ordering.eq := heqIff.1 heqL
            have hfalseL : decide (compare sL jL = Ordering.lt) = false := by
              simp [heqL]
            have hfalseR : decide (compare sR jR = Ordering.lt) = false := by
              simp [heqR]
            exact hcolorBool (hfalseL.trans hfalseR.symm)
          have hneR : compare sR jR ≠ Ordering.eq := by
            intro heqR
            have heqL : compare sL jL = Ordering.eq := heqIff.2 heqR
            have hfalseL : decide (compare sL jL = Ordering.lt) = false := by
              simp [heqL]
            have hfalseR : decide (compare sR jR = Ordering.lt) = false := by
              simp [heqR]
            exact hcolorBool (hfalseL.trans hfalseR.symm)
          let oL : Bool := decide (compare sL jL ≠ Ordering.lt)
          let oR : Bool := decide (compare sR jR ≠ Ordering.lt)
          have ho : oL = !oR := by
            have hdecL : oL = !decide (compare sL jL = Ordering.lt) :=
              decide_ne_lt_eq_not_decide_eq_lt hneL
            have hdecR : oR = !decide (compare sR jR = Ordering.lt) :=
              decide_ne_lt_eq_not_decide_eq_lt hneR
            rw [hdecL, hdecR]
            exact congrArg Bool.not (bool_eq_not_of_ne hcolorBool)
          have sourceL := priorReadings_both molecule descriptorMap unit left W D hL .senior
          have sourceR := priorReadings_both molecule descriptorMap unit right W D hR .junior
          have sourceR' :
              retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .junior =
                priorBothStream (ofLex (max sR jR)).1 (ofLex (min sR jR)).1 (!oR)
                  .senior := by
            rw [show retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D
                  .junior =
                priorBothStream (ofLex (max sR jR)).1 (ofLex (min sR jR)).1 oR .junior
                from sourceR]
            exact priorBothStream_junior _ _ oR
          rw [(show retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D
                .senior =
              priorBothStream (ofLex (max sL jL)).1 (ofLex (min sL jL)).1 oL .senior
              from sourceL),
            sourceR', hmax, hmin, ho]

/-- A right-side `both` complete tie would force equal colors and hence equal full keys. -/
private theorem priorNotBothTie_of_prior_of_color_ne
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hsig : retainedCompletePriorSignatureAt molecule descriptorMap unit left W D =
      retainedCompletePriorSignatureAt molecule descriptorMap unit right W D)
    (hcolor_ne : retainedRule5Color molecule descriptorMap unit left W D ≠
      retainedRule5Color molecule descriptorMap unit right W D) :
    ¬ (retainedReferenceSelection molecule descriptorMap unit right = .both ∧
        compare
          (retainedCompleteReadingAt molecule descriptorMap unit right W D (some .senior))
          (retainedCompleteReadingAt molecule descriptorMap unit right W D (some .junior)) =
            Ordering.eq) := by
  rintro ⟨hbothR, heqR⟩
  have hcount :=
    congrArg (fun signature : CompletePriorSignature => (ofLex signature).1) hsig
  have hcount' :
      (retainedReferenceSelection molecule descriptorMap unit left).countPriority =
        (retainedReferenceSelection molecule descriptorMap unit right).countPriority := by
    simpa only [retainedCompletePriorSignatureAt_count] using hcount
  cases hL : retainedReferenceSelection molecule descriptorMap unit left with
  | empty =>
      simp [hL, hbothR, ReferenceSelection.countPriority] at hcount'
  | one sense =>
      simp [hL, hbothR, ReferenceSelection.countPriority] at hcount'
  | both =>
      obtain ⟨_, _, heqIff⟩ :=
        priorSignature_components_both molecule descriptorMap unit left right W D
          hL hbothR hsig
      have heqL := heqIff.2 heqR
      have hcL : retainedRule5Color molecule descriptorMap unit left W D = false :=
        priorColor_both_tie molecule descriptorMap unit left W D hL heqL
      have hcR : retainedRule5Color molecule descriptorMap unit right W D = false :=
        priorColor_both_tie molecule descriptorMap unit right W D hbothR heqR
      exact hcolor_ne (hcL.trans hcR.symm)

/-- The exact cross-map Rule-5 reading equality under a distinct prior tie: the reflected
senior stream at `right` equals the original senior stream at `left`. -/
theorem mirrored_right_readings_eq_original_left_of_distinct_prior_tie
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit right W D .senior =
      retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior := by
  have hsig := priorSignature_eq_of_prior molecule descriptorMap unit left right W D hprior
  have hcolor_ne := priorColor_ne_of_prior_of_key_ne molecule descriptorMap unit left right
    W D hprior hkey
  have hstream := priorReadings_cross_of_prior_of_color_ne molecule descriptorMap unit
    left right W D hprior hcolor_ne
  have hnotTie := priorNotBothTie_of_prior_of_color_ne molecule descriptorMap unit left right
    W D hsig hcolor_ne
  rw [retainedCompleteRule5ReadingsAt_reflect molecule descriptorMap unit right W D .senior]
  rw [if_neg hnotTie]
  simpa [DescriptorSense.mirror] using hstream.symm

/-- Common-layout cross-map key equality: when the original full keys at `left` and `right`
are distinct but their prior keys tie, the reflected key at `right` equals the original key
at `left`. -/
theorem original_left_eq_reflected_right_of_distinct_prior_tie
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit right W D := by
  have hstreamReflect :=
    mirrored_right_readings_eq_original_left_of_distinct_prior_tie molecule descriptorMap unit
      left right W D hprior hkey
  unfold retainedCompleteLigandRule5KeyAt
  rw [retainedCompleteLigandPriorKeyAt_reflect molecule descriptorMap unit right W D,
    ← hprior, hstreamReflect]

/-- Reverse orientation of the common-layout key equality. -/
theorem reflected_right_eq_original_left_of_distinct_prior_tie
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit right W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D :=
  (original_left_eq_reflected_right_of_distinct_prior_tie molecule descriptorMap unit
    left right W D hprior hkey).symm

/-- Symmetric common-layout key equality, with the reflected side on the left graph. -/
theorem original_right_eq_reflected_left_of_distinct_prior_tie
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D)
    (hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit left W D := by
  exact original_left_eq_reflected_right_of_distinct_prior_tie
    (molecule := molecule) (descriptorMap := descriptorMap) (unit := unit)
    (left := right) (right := left) (W := W) (D := D) hprior.symm hkey.symm

/-- Common-layout full-key equality on a four-slot table, under a distinct prior tie and
original full-key injectivity. -/
theorem retainedKeys_reflected_right_eq_original_left_of_injective_priorTie
    (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ) {i j : Fin 4}
    (hij : i ≠ j)
    (hinj : Function.Injective fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs i) W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs j) W D) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit (graphs j) W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs i) W D := by
  have hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs i) W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs j) W D := by
    intro h
    exact hij (hinj h)
  exact (original_left_eq_reflected_right_of_distinct_prior_tie
    (molecule := molecule) (descriptorMap := descriptorMap) (unit := unit)
    (left := graphs i) (right := graphs j) (W := W) (D := D) hprior hkey).symm

/-- Symmetric four-slot form: the reflected key at the left slot equals the original key at
the right slot. -/
theorem retainedKeys_reflected_left_eq_original_right_of_injective_priorTie
    (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ) {i j : Fin 4}
    (hij : i ≠ j)
    (hinj : Function.Injective fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs i) W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs j) W D) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit (graphs i) W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs j) W D := by
  have hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs i) W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs j) W D := by
    intro h
    exact hij (hinj h)
  exact (original_right_eq_reflected_left_of_distinct_prior_tie
    (molecule := molecule) (descriptorMap := descriptorMap) (unit := unit)
    (left := graphs i) (right := graphs j) (W := W) (D := D) hprior hkey).symm

/-- The original-left, reflected-right equality in its positive orientation on a four-slot
common graph family. -/
theorem retainedKeys_original_left_eq_reflected_right_of_injective_priorTie
    (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ) {i j : Fin 4}
    (hij : i ≠ j)
    (hinj : Function.Injective fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
    (hprior : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs i) W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs j) W D) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs i) W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit (graphs j) W D := by
  have hkey : retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs i) W D ≠
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs j) W D := by
    intro h
    exact hij (hinj h)
  exact original_left_eq_reflected_right_of_distinct_prior_tie
    (molecule := molecule) (descriptorMap := descriptorMap) (unit := unit)
    (left := graphs i) (right := graphs j) (W := W) (D := D) hprior hkey

end

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey.mirrored_right_readings_eq_original_left_of_distinct_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey.original_left_eq_reflected_right_of_distinct_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey.reflected_right_eq_original_left_of_distinct_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey.original_right_eq_reflected_left_of_distinct_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey.retainedKeys_reflected_right_eq_original_left_of_injective_priorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey.retainedKeys_reflected_left_eq_original_right_of_injective_priorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey.retainedKeys_original_left_eq_reflected_right_of_injective_priorTie
