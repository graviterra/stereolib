import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingProjection
import TetraStereo.OneCenter.DeclarativeCIPCompleteRootDescriptor
import TetraStereo.OneCenter.DeclarativeCIPRetainedCompleteSignatures
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# One-step retained descriptor transport

The image descriptor map is the source map, or that map reflected. This abstract map relation
is not derived here from actual strict dependencies or a molecular automorphism. Keys and
coordinates move by the same arbitrary slot permutation, so its orientation signs cancel;
identification with an occurrence-derived frame permutation remains a separate connection.
The reflected-map judgment is proved only when the prior-pair count is zero. General comparison
reflection is proved, but the proposed sort sign `(-1) ^ completeRule5PairCount` is not yet
derived for the reflected sorted permutation.

No acyclicity, comparator strictness, sorting success, selected reference, or final letter is
assumed. Refusal is the absence of a strict geometric judgment. `RootedDigraph.Iso` is not the
carrier. Configuration signs are not read as `R` or `S`.
-/

namespace TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport

open DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)
open RationalTetrahedralPermutation
open scoped Classical

noncomputable section
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

local instance transportNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem compare_comm_swap {α : Type _} [Ord α] [Std.OrientedOrd α] (a b : α) :
    compare b a = (compare a b).swap :=
  Std.OrientedOrd.eq_swap (a := b) (b := a)

theorem compare_singleton {α : Type _} [Ord α] (a b : α) :
    compare ([a] : List α) [b] = compare a b := by
  rw [List.compare_cons_cons]
  have tail : compare ([] : List α) [] = .eq := by
    rw [List.compare_eq_compareLex]
    rfl
  rw [tail]
  cases compare a b <;> rfl

def reflectZ (point : CartesianPoint3) : CartesianPoint3 where
  x := point.x
  y := point.y
  z := -point.z

theorem orientedVolume_reflectZ (a b c d : CartesianPoint3) :
    CartesianPoint3.orientedVolume (reflectZ a) (reflectZ b) (reflectZ c) (reflectZ d) =
      -CartesianPoint3.orientedVolume a b c d := by
  simp only [CartesianPoint3.orientedVolume, reflectZ]
  ring

def applySpace (spaceMirror : Bool) (point : CartesianPoint3) : CartesianPoint3 :=
  if spaceMirror then reflectZ point else point

theorem orientedVolume_applySpace (spaceMirror : Bool) (a b c d : CartesianPoint3) :
    CartesianPoint3.orientedVolume (applySpace spaceMirror a) (applySpace spaceMirror b)
        (applySpace spaceMirror c) (applySpace spaceMirror d) =
      (if spaceMirror then (-1 : ℤ) else 1) *
        CartesianPoint3.orientedVolume a b c d := by
  cases spaceMirror with
  | true => simp [applySpace, orientedVolume_reflectZ]
  | false => simp [applySpace]

/-- Same permutation of ligand keys and ligand coordinates. The two signs are equal, hence cancel. -/
theorem framePerm_sign_cancels (framePerm : Equiv.Perm (Fin 4)) :
    permHandedness framePerm * permHandedness framePerm⁻¹ = 1 := by
  rw [permHandedness_inv, permHandedness_mul_self]

def dependencyMap {Unit : Type _} (dependencyMirror : Bool) (sourceMap : DescriptorMap Unit) :
    DescriptorMap Unit :=
  if dependencyMirror then sourceMap.reflect else sourceMap

def spaceSign (spaceMirror : Bool) : ℤ :=
  if spaceMirror then -1 else 1

def sortSign (dependencyMirror : Bool) (count : ℕ) : ℤ :=
  if dependencyMirror then (-1 : ℤ) ^ count else 1

def orientationFactor (spaceMirror dependencyMirror : Bool) (count : ℕ) : ℤ :=
  spaceSign spaceMirror * sortSign dependencyMirror count

theorem negOnePow_dichotomy (n : ℕ) : (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rcases ih with h | h
      · right
        simp [pow_succ, h]
      · left
        simp [pow_succ, h]

theorem orientationFactor_dichotomy (spaceMirror dependencyMirror : Bool) (count : ℕ) :
    orientationFactor spaceMirror dependencyMirror count = 1 ∨
      orientationFactor spaceMirror dependencyMirror count = -1 := by
  unfold orientationFactor spaceSign sortSign
  cases spaceMirror <;> cases dependencyMirror <;>
    simp <;> rcases negOnePow_dichotomy count with h | h <;> simp [h]

def rawAdjust (raw : RS) (factor : ℤ) : RS :=
  if factor = -1 then RS.swap raw else raw

section Readings

variable (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

theorem retainedMolecularRankPairAt_reflect (W D : ℕ) :
    retainedMolecularRankPairAt molecule descriptorMap.reflect unit graph W D =
      retainedMolecularRankPairAt molecule descriptorMap unit graph W D := by
  unfold retainedMolecularRankPairAt
  rw [retainedRankEvidence_reflect molecule descriptorMap unit graph]

theorem retainedCompleteLigandPriorKeyAt_reflect (W D : ℕ) :
    retainedCompleteLigandPriorKeyAt molecule descriptorMap.reflect unit graph W D =
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit graph W D := by
  unfold retainedCompleteLigandPriorKeyAt
  exact congrArg (fun pair : MolecularRankPair × CompletePriorSignature => toLex pair)
    (Prod.ext (retainedMolecularRankPairAt_reflect molecule descriptorMap unit graph W D)
      (retainedCompletePriorSignatureAt_reflect molecule descriptorMap unit graph W D))

theorem retainedCompleteRule5Reading_reflect_arg (W D : ℕ)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    retainedCompleteRule5ReadingAt molecule descriptorMap.reflect unit graph W D reference common =
      retainedCompleteRule5ReadingAt molecule descriptorMap unit graph W D
        (reference.map DescriptorSense.mirror) common.mirror := by
  have reflected := retainedCompleteRule5ReadingAt_reflect molecule descriptorMap unit graph W D
    (reference.map DescriptorSense.mirror) common.mirror
  simpa [Option.map_map, Function.comp_def, DescriptorSense.mirror_mirror] using reflected

/-- Tagged Rule-5 references after `descriptorMap.reflect`. A complete reading tie keeps
senior-before-junior in both maps, so that one case is not the mirror of the tag list. -/
theorem retainedTaggedAlternativeReferencesAt_reflect (W D : ℕ) :
    retainedTaggedAlternativeReferencesAt molecule descriptorMap.reflect unit graph W D =
      let original := retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D
      if retainedReferenceSelection molecule descriptorMap unit graph = .both ∧
          compare
            (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
            (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) = .eq
      then original
      else original.map (Option.map DescriptorSense.mirror) := by
  unfold retainedTaggedAlternativeReferencesAt
  rw [retainedReferenceSelection_reflect molecule descriptorMap unit graph]
  cases hsel : retainedReferenceSelection molecule descriptorMap unit graph with
  | empty => simp [ReferenceSelection.mirror]
  | one sense => simp [ReferenceSelection.mirror]
  | both =>
      simp only [ReferenceSelection.mirror]
      let senior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
      let junior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      have seniorR :
          retainedCompleteReadingAt molecule descriptorMap.reflect unit graph W D (some .senior) =
            junior := by
        simpa [DescriptorSense.mirror] using
          (retainedCompleteReadingAt_reflect molecule descriptorMap unit graph W D (some .senior))
      have juniorR :
          retainedCompleteReadingAt molecule descriptorMap.reflect unit graph W D (some .junior) =
            senior := by
        simpa [DescriptorSense.mirror] using
          (retainedCompleteReadingAt_reflect molecule descriptorMap unit graph W D (some .junior))
      have swapCmp : compare junior senior = (compare senior junior).swap :=
        compare_comm_swap senior junior
      rw [seniorR, juniorR, swapCmp]
      by_cases heq : compare senior junior = Ordering.eq
      · rw [heq, show Ordering.eq.swap = Ordering.eq from rfl,
          if_neg (by decide : Ordering.eq ≠ Ordering.lt)]
        simp
      · by_cases hlt : compare senior junior = Ordering.lt
        · rw [hlt, show Ordering.lt.swap = Ordering.gt from rfl,
            if_neg (by decide : Ordering.gt ≠ Ordering.lt)]
          simp [DescriptorSense.mirror]
        · have hgt : compare senior junior = Ordering.gt := by
            cases hcmp : compare senior junior with
            | lt => exact absurd hcmp hlt
            | eq => exact absurd hcmp heq
            | gt => rfl
          rw [hgt, show Ordering.gt.swap = Ordering.lt from rfl, if_pos rfl]
          simp [DescriptorSense.mirror]

theorem retainedCompleteRule5ReadingsAt_reflect (W D : ℕ) (common : DescriptorSense) :
    retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit graph W D common =
      let original :=
        retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common.mirror
      if retainedReferenceSelection molecule descriptorMap unit graph = .both ∧
          compare
            (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
            (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) = .eq
      then original.reverse
      else original := by
  unfold retainedCompleteRule5ReadingsAt
  rw [retainedTaggedAlternativeReferencesAt_reflect molecule descriptorMap unit graph W D]
  by_cases htie :
      retainedReferenceSelection molecule descriptorMap unit graph = .both ∧
        compare
          (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior))
          (retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)) = .eq
  · rw [if_pos htie, if_pos htie]
    rcases htie with ⟨hboth, heq⟩
    have tags :
        retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D =
          [some .senior, some .junior] := by
      unfold retainedTaggedAlternativeReferencesAt
      simp [hboth, heq]
    rw [tags]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, DescriptorSense.mirror]
    have seniorR := retainedCompleteRule5Reading_reflect_arg molecule descriptorMap unit graph
      W D (some .senior) common
    have juniorR := retainedCompleteRule5Reading_reflect_arg molecule descriptorMap unit graph
      W D (some .junior) common
    simp only [Option.map_some, DescriptorSense.mirror] at seniorR juniorR
    rw [seniorR, juniorR]
  · rw [if_neg htie, if_neg htie, List.map_map]
    refine List.map_congr_left ?_
    intro reference _
    simpa [DescriptorSense.mirror_mirror] using
      retainedCompleteRule5ReadingAt_reflect molecule descriptorMap unit graph W D reference
        common.mirror

end Readings

variable (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)

theorem completeRule5PairCount_reflect (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ) :
    completeRule5PairCount (fun slot =>
        retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit (graphs slot) W D) =
      completeRule5PairCount (fun slot =>
        retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D) := by
  apply sourceEnantiomorphicPairCount_congr_of_forall
  intro i j
  simp only [CompletePriorPair, retainedCompleteLigandRule5KeyAt_prior,
    retainedCompleteLigandPriorKeyAt_reflect molecule descriptorMap unit]

private def rule4bList (signature : CompletePriorSignature) : List (Key StereoLabel) :=
  (ofLex (ofLex signature).2).1

private def rule4cList (signature : CompletePriorSignature) : List (Key StereoLabel) :=
  (ofLex (ofLex signature).2).2

private theorem rule4bList_eq (graph : RootedDigraph Atom) (W D : ℕ) :
    rule4bList (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D) =
      let selection := retainedReferenceSelection molecule descriptorMap unit graph
      let readings := retainedCompleteReadingsAt molecule descriptorMap unit graph W D
      if selection = .empty then [] else readings.map fun key => (ofLex key).1 := by
  simp [rule4bList, retainedCompletePriorSignatureAt]

private theorem rule4cList_eq (graph : RootedDigraph Atom) (W D : ℕ) :
    rule4cList (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D) =
      (retainedCompleteReadingsAt molecule descriptorMap unit graph W D).map fun key =>
        (ofLex key).2 := by
  simp [rule4cList, retainedCompletePriorSignatureAt]

private def bothStream (seniorComp juniorComp : Key StereoLabel) (seniorNotLt : Bool)
    (common : DescriptorSense) : List (Key StereoLabel) :=
  if seniorNotLt then
    [mapObservationKey (absoluteRule5Label .senior common) seniorComp,
      mapObservationKey (absoluteRule5Label .junior common) juniorComp]
  else
    [mapObservationKey (absoluteRule5Label .junior common) seniorComp,
      mapObservationKey (absoluteRule5Label .senior common) juniorComp]

private theorem absoluteRule5Label_cross (own : DescriptorSense) :
    absoluteRule5Label own own.mirror = absoluteRule5Label own.mirror own := by
  cases own <;> rfl

private theorem absoluteRule5Label_same (own : DescriptorSense) :
    absoluteRule5Label own own = absoluteRule5Label own.mirror own.mirror := by
  cases own <;> rfl

private theorem bothStream_junior (seniorComp juniorComp : Key StereoLabel) (seniorNotLt : Bool) :
    bothStream seniorComp juniorComp seniorNotLt .junior =
      bothStream seniorComp juniorComp (!seniorNotLt) .senior := by
  cases seniorNotLt with
  | false =>
      simp only [bothStream, Bool.not_false]
      rw [if_neg (by decide : ¬ false = true)]
      exact congrArg₂ (fun x y => [x, y])
        (congrArg (fun label => mapObservationKey label seniorComp)
          (absoluteRule5Label_same .junior))
        (congrArg (fun label => mapObservationKey label juniorComp)
          (absoluteRule5Label_cross .senior))
  | true =>
      simp only [bothStream, Bool.not_true]
      rw [if_neg (by decide : ¬ false = true)]
      exact congrArg₂ (fun x y => [x, y])
        (congrArg (fun label => mapObservationKey label seniorComp)
          (absoluteRule5Label_cross .senior))
        (congrArg (fun label => mapObservationKey label juniorComp)
          (absoluteRule5Label_same .junior))

private theorem readings_both (graph : RootedDigraph Atom) (W D : ℕ)
    (hboth : retainedReferenceSelection molecule descriptorMap unit graph = .both)
    (common : DescriptorSense) :
    let senior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior)
    let junior := retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
    retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common =
      bothStream (ofLex (max senior junior)).1 (ofLex (min senior junior)).1
        (decide (compare senior junior ≠ .lt)) common := by
  intro senior junior
  unfold retainedCompleteRule5ReadingsAt retainedTaggedAlternativeReferencesAt
  simp only [hboth]
  by_cases hlt : compare senior junior = Ordering.lt
  · rw [if_pos hlt]
    have hsj : senior < junior := (completeReading_compare_lt_iff senior junior).1 hlt
    have hdec : decide (compare senior junior ≠ Ordering.lt) = false := by simp [hlt]
    simp only [List.map_cons, List.map_nil, retainedCompleteRule5ReadingAt, hdec,
      max_eq_right (le_of_lt hsj), min_eq_left (le_of_lt hsj), bothStream, Bool.false_eq_true,
      if_false]
    rfl
  · rw [if_neg hlt]
    have hle : junior ≤ senior := le_of_not_gt fun strict =>
      hlt ((completeReading_compare_lt_iff senior junior).2 strict)
    have hdec : decide (compare senior junior ≠ Ordering.lt) = true := by simp [hlt]
    simp only [List.map_cons, List.map_nil, retainedCompleteRule5ReadingAt, hdec,
      max_eq_left hle, min_eq_right hle, bothStream, if_true]
    rfl

private theorem signature_components_both
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
  have hlists := congrArg rule4bList hsig
  rw [rule4bList_eq molecule descriptorMap unit left W D,
    rule4bList_eq molecule descriptorMap unit right W D, hselL, hselR] at hlists
  simp only [retainedCompleteReadingsAt, hselL, hselR, List.map_cons, List.map_nil] at hlists
  injection hlists with hmax htail
  injection htail with hmin _
  refine ⟨hmax, hmin, ?_⟩
  have h4cLists := congrArg rule4cList hsig
  rw [rule4cList_eq molecule descriptorMap unit left W D,
    rule4cList_eq molecule descriptorMap unit right W D] at h4cLists
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

/-- Equal prior signatures make the reflected senior Rule-5 comparison the swap of the source
comparison. Ties stay ties. This is derived from the tagged readings, not assumed alignment. -/
theorem retainedRule5SeniorCompare_swap_of_equalSignature
    (left right : RootedDigraph Atom) (W D : ℕ)
    (hsig : retainedCompletePriorSignatureAt molecule descriptorMap unit left W D =
      retainedCompletePriorSignatureAt molecule descriptorMap unit right W D) :
    compare
        (retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit left W D .senior)
        (retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit right W D .senior) =
      (compare
        (retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior)
        (retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior)).swap := by
  have hcount := congrArg (fun signature => (ofLex signature).1) hsig
  simp only [retainedCompletePriorSignatureAt_count] at hcount
  cases hL : retainedReferenceSelection molecule descriptorMap unit left with
  | empty =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty =>
          have streams :
              retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior := by
            have h4c := congrArg rule4cList hsig
            rw [rule4cList_eq molecule descriptorMap unit left W D,
              rule4cList_eq molecule descriptorMap unit right W D] at h4c
            simp only [retainedCompleteReadingsAt, hL, hR, List.map_cons, List.map_nil] at h4c
            injection h4c with hcomp _
            unfold retainedCompleteRule5ReadingsAt retainedTaggedAlternativeReferencesAt
              retainedCompleteRule5ReadingAt
            simp only [hL, hR, List.map_cons, List.map_nil, hcomp]
          have indep (graph : RootedDigraph Atom) (common : DescriptorSense)
              (hempty : retainedReferenceSelection molecule descriptorMap unit graph = .empty) :
              retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common =
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D .senior := by
            unfold retainedCompleteRule5ReadingsAt retainedTaggedAlternativeReferencesAt
              retainedCompleteRule5ReadingAt
            simp [hempty]
          have imageStreams :
              retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit left W D .senior =
                retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit right W D
                  .senior := by
            rw [retainedCompleteRule5ReadingsAt_reflect molecule descriptorMap unit left W D .senior,
              retainedCompleteRule5ReadingsAt_reflect molecule descriptorMap unit right W D .senior]
            have hnotL : ¬ (retainedReferenceSelection molecule descriptorMap unit left = .both ∧
                compare
                  (retainedCompleteReadingAt molecule descriptorMap unit left W D (some .senior))
                  (retainedCompleteReadingAt molecule descriptorMap unit left W D (some .junior)) =
                    Ordering.eq) := by simp [hL]
            have hnotR : ¬ (retainedReferenceSelection molecule descriptorMap unit right = .both ∧
                compare
                  (retainedCompleteReadingAt molecule descriptorMap unit right W D (some .senior))
                  (retainedCompleteReadingAt molecule descriptorMap unit right W D (some .junior)) =
                    Ordering.eq) := by simp [hR]
            rw [if_neg hnotL, if_neg hnotR]
            simp only [DescriptorSense.mirror]
            rw [indep left .junior hL, indep right .junior hR]
            exact streams
          rw [imageStreams, streams, Std.ReflOrd.compare_self, Std.ReflOrd.compare_self]
          rfl
      | one sense =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | both =>
          simp [hL, hR, ReferenceSelection.countPriority] at hcount
  | one senseL =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty => simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | both => simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | one senseR =>
          have hlists := congrArg rule4bList hsig
          rw [rule4bList_eq molecule descriptorMap unit left W D,
            rule4bList_eq molecule descriptorMap unit right W D, hL, hR] at hlists
          simp only [retainedCompleteReadingsAt, hL, hR, List.map_cons, List.map_nil] at hlists
          have hcomp :
              (ofLex (retainedCompleteReadingAt molecule descriptorMap unit left W D
                (some senseL))).1 =
              (ofLex (retainedCompleteReadingAt molecule descriptorMap unit right W D
                (some senseR))).1 := by
            injection hlists with hhead _
          let component :=
            (ofLex (retainedCompleteReadingAt molecule descriptorMap unit left W D
              (some senseL))).1
          have sourceL :
              retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                [mapObservationKey (absoluteRule5Label senseL .senior) component] := by
            simp [retainedCompleteRule5ReadingsAt, retainedTaggedAlternativeReferencesAt, hL,
              retainedCompleteRule5ReadingAt, component]
          have sourceR :
              retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior =
                [mapObservationKey (absoluteRule5Label senseR .senior) component] := by
            simp [retainedCompleteRule5ReadingsAt, retainedTaggedAlternativeReferencesAt, hR,
              retainedCompleteRule5ReadingAt, hcomp, component]
          have imageL :
              retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit left W D .senior =
                [mapObservationKey (absoluteRule5Label senseL.mirror .senior) component] := by
            have readingEq := retainedCompleteReadingAt_reflect molecule descriptorMap unit left W D
              (some senseL.mirror)
            simp only [Option.map_some, DescriptorSense.mirror_mirror] at readingEq
            simp [retainedCompleteRule5ReadingsAt, retainedTaggedAlternativeReferencesAt,
              retainedReferenceSelection_reflect, hL, ReferenceSelection.mirror,
              retainedCompleteRule5ReadingAt, readingEq, component]
          have imageR :
              retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit right W D .senior =
                [mapObservationKey (absoluteRule5Label senseR.mirror .senior) component] := by
            have readingEq := retainedCompleteReadingAt_reflect molecule descriptorMap unit right W D
              (some senseR.mirror)
            simp only [Option.map_some, DescriptorSense.mirror_mirror] at readingEq
            simp [retainedCompleteRule5ReadingsAt, retainedTaggedAlternativeReferencesAt,
              retainedReferenceSelection_reflect, hR, ReferenceSelection.mirror,
              retainedCompleteRule5ReadingAt, readingEq, hcomp, component]
          rw [sourceL, sourceR, imageL, imageR, compare_singleton, compare_singleton]
          cases senseL <;> cases senseR <;> simp only [DescriptorSense.mirror]
          · rw [Std.ReflOrd.compare_self, Std.ReflOrd.compare_self]; rfl
          · rw [compare_comm_swap]
          · rw [compare_comm_swap]
          · rw [Std.ReflOrd.compare_self, Std.ReflOrd.compare_self]; rfl
  | both =>
      cases hR : retainedReferenceSelection molecule descriptorMap unit right with
      | empty => simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | one sense => simp [hL, hR, ReferenceSelection.countPriority] at hcount
      | both =>
          let sL := retainedCompleteReadingAt molecule descriptorMap unit left W D (some .senior)
          let jL := retainedCompleteReadingAt molecule descriptorMap unit left W D (some .junior)
          let sR := retainedCompleteReadingAt molecule descriptorMap unit right W D (some .senior)
          let jR := retainedCompleteReadingAt molecule descriptorMap unit right W D (some .junior)
          obtain ⟨hmax, hmin, heqIff⟩ := signature_components_both molecule descriptorMap unit
            left right W D hL hR hsig
          have sourceL := readings_both molecule descriptorMap unit left W D hL .senior
          have sourceR := readings_both molecule descriptorMap unit right W D hR .senior
          by_cases heq : compare sL jL = .eq
          · have heqR : compare sR jR = .eq := heqIff.1 heq
            have hsL : sL = jL := (completeReading_compare_eq_iff sL jL).1 heq
            have hsR : sR = jR := (completeReading_compare_eq_iff sR jR).1 heqR
            have sameMaxL : max sL jL = sL := by rw [hsL]; simp
            have sameMaxR : max sR jR = sR := by rw [hsR]; simp
            have sameMinL : min sL jL = sL := by rw [hsL]; simp
            have sameMinR : min sR jR = sR := by rw [hsR]; simp
            have hcomp : (ofLex sL).1 = (ofLex sR).1 := by
              rw [← sameMaxL, ← sameMaxR]
              exact hmax
            have sourceEq :
                retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                  retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior := by
              rw [sourceL, sourceR, sameMaxL, sameMaxR, sameMinL, sameMinR, heq, heqR]
              have hd : decide (Ordering.eq ≠ Ordering.lt) = true := by decide
              rw [hd]
              simp only [hcomp, bothStream, if_true]
            have imageEq :
                retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit left W D
                    .senior =
                  retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit right W D
                    .senior := by
              rw [retainedCompleteRule5ReadingsAt_reflect molecule descriptorMap unit left W D
                  .senior,
                retainedCompleteRule5ReadingsAt_reflect molecule descriptorMap unit right W D
                  .senior]
              have htieL : retainedReferenceSelection molecule descriptorMap unit left = .both ∧
                  compare sL jL = Ordering.eq := ⟨hL, heq⟩
              have htieR : retainedReferenceSelection molecule descriptorMap unit right = .both ∧
                  compare sR jR = Ordering.eq := ⟨hR, heqR⟩
              rw [if_pos htieL, if_pos htieR]
              simp only [DescriptorSense.mirror]
              have juniorL := readings_both molecule descriptorMap unit left W D hL .junior
              have juniorR := readings_both molecule descriptorMap unit right W D hR .junior
              rw [juniorL, juniorR, bothStream_junior, bothStream_junior, sameMaxL, sameMaxR,
                sameMinL, sameMinR, heq, heqR]
              have hd : decide (Ordering.eq ≠ Ordering.lt) = true := by decide
              rw [hd]
              simp only [hcomp, bothStream, Bool.not_true]
            rw [sourceEq, imageEq, Std.ReflOrd.compare_self, Std.ReflOrd.compare_self]
            rfl
          · have hneR : compare sR jR ≠ .eq := by
              intro h
              exact heq (heqIff.2 h)
            let oL : Bool := decide (compare sL jL ≠ .lt)
            let oR : Bool := decide (compare sR jR ≠ .lt)
            have imageL :
                retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit left W D
                    .senior =
                  bothStream (ofLex (max sL jL)).1 (ofLex (min sL jL)).1 (!oL) .senior := by
              rw [retainedCompleteRule5ReadingsAt_reflect molecule descriptorMap unit left W D
                  .senior]
              have hnot : ¬ (retainedReferenceSelection molecule descriptorMap unit left = .both ∧
                  compare sL jL = Ordering.eq) := by simp [hL, heq]
              rw [if_neg hnot]
              simp only [DescriptorSense.mirror]
              rw [readings_both molecule descriptorMap unit left W D hL .junior, bothStream_junior]
            have imageR :
                retainedCompleteRule5ReadingsAt molecule descriptorMap.reflect unit right W D
                    .senior =
                  bothStream (ofLex (max sR jR)).1 (ofLex (min sR jR)).1 (!oR) .senior := by
              rw [retainedCompleteRule5ReadingsAt_reflect molecule descriptorMap unit right W D
                  .senior]
              have hnot : ¬ (retainedReferenceSelection molecule descriptorMap unit right = .both ∧
                  compare sR jR = Ordering.eq) := by simp [hR, hneR]
              rw [if_neg hnot]
              simp only [DescriptorSense.mirror]
              rw [readings_both molecule descriptorMap unit right W D hR .junior, bothStream_junior]
            rw [(show retainedCompleteRule5ReadingsAt molecule descriptorMap unit left W D .senior =
                bothStream (ofLex (max sL jL)).1 (ofLex (min sL jL)).1 oL .senior from sourceL),
              (show retainedCompleteRule5ReadingsAt molecule descriptorMap unit right W D .senior =
                bothStream (ofLex (max sR jR)).1 (ofLex (min sR jR)).1 oR .senior from sourceR),
              imageL, imageR, hmax, hmin]
            cases oL <;> cases oR <;>
              simp only [bothStream, Bool.not_false, Bool.not_true]
            · rw [Std.ReflOrd.compare_self, Std.ReflOrd.compare_self]; rfl
            · rw [compare_comm_swap]
            · rw [compare_comm_swap]
            · rw [Std.ReflOrd.compare_self, Std.ReflOrd.compare_self]; rfl

theorem retainedPairCompare_reflect (left right : RootedDigraph Atom) (W D : ℕ) :
    compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit left W D)
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit right W D) =
      if retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
          retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D then
        (compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
          (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)).swap
      else
        compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
          (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) := by
  have pL := retainedCompleteLigandPriorKeyAt_reflect molecule descriptorMap unit left W D
  have pR := retainedCompleteLigandPriorKeyAt_reflect molecule descriptorMap unit right W D
  have sourceThen := retainedCompleteLigandRule5KeyAt_compare_eq_then molecule descriptorMap unit
    left right W D
  have imageThen := retainedCompleteLigandRule5KeyAt_compare_eq_then molecule descriptorMap.reflect
    unit left right W D
  rw [sourceThen, imageThen, pL, pR]
  by_cases htied :
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
        retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D
  · rw [if_pos htied]
    have hsig :
        retainedCompletePriorSignatureAt molecule descriptorMap unit left W D =
          retainedCompletePriorSignatureAt molecule descriptorMap unit right W D := by
      simpa [retainedCompleteLigandPriorKeyAt_signature] using
        congrArg (fun key : CompleteLigandPriorKey => (ofLex key).2) htied
    have hprior :
        compare (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D)
          (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) = Ordering.eq :=
      (completeLigandPriorKey_compare_eq_iff _ _).2 htied
    rw [hprior, Ordering.eq_then, Ordering.eq_then]
    exact retainedRule5SeniorCompare_swap_of_equalSignature molecule descriptorMap unit
      left right W D hsig
  · rw [if_neg htied]
    have hprior :
        compare (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D)
          (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) ≠ Ordering.eq :=
      fun h => htied ((completeLigandPriorKey_compare_eq_iff _ _).1 h)
    cases hcmp : compare
        (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D)
        (retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D) with
    | eq => exact absurd hcmp hprior
    | lt => simp only [Ordering.lt_then]
    | gt => simp only [Ordering.gt_then]

def labelAdjust (spaceMirror : Bool)
    (descriptor : _root_.TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel) :
    _root_.TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel :=
  if spaceMirror then descriptor.swap else descriptor

theorem rationalDescriptor_map_applySpace {points : List CartesianPoint3} {raw : RS}
    (spaceMirror : Bool)
    (h : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor points raw) :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      (points.map (applySpace spaceMirror))
      (rawAdjust raw (spaceSign spaceMirror)) := by
  obtain ⟨a, b, c, d, rfl, hsign⟩ := h
  refine ⟨applySpace spaceMirror a, applySpace spaceMirror b, applySpace spaceMirror c,
    applySpace spaceMirror d, by simp, ?_⟩
  have hvol := orientedVolume_applySpace spaceMirror a b c d
  cases spaceMirror with
  | false =>
      cases raw <;> simpa [rawAdjust, spaceSign] using hsign
  | true =>
      have hneg :
          CartesianPoint3.orientedVolume (applySpace true a) (applySpace true b)
              (applySpace true c) (applySpace true d) =
            -CartesianPoint3.orientedVolume a b c d := by
        simpa [spaceSign] using hvol
      cases raw with
      | R =>
          have hpos : 0 < CartesianPoint3.orientedVolume (applySpace true a) (applySpace true b)
              (applySpace true c) (applySpace true d) := by
            rw [hneg]
            linarith
          simpa [rawAdjust, spaceSign, RS.swap] using hpos
      | S =>
          have hnegVol : CartesianPoint3.orientedVolume (applySpace true a) (applySpace true b)
              (applySpace true c) (applySpace true d) < 0 := by
            rw [hneg]
            linarith
          simpa [rawAdjust, spaceSign, RS.swap] using hnegVol

/-- Proper ligand reindexing. `slotPerm` is the occurrence `framePerm`: it moves retained keys and
coordinates together, so its sign cancels. `spaceMirror` is an independent `reflectZ`. The
descriptor map is not reflected here, so a coordinate mirror complements both letter cases.
Dependency reflection is the separate compare law `retainedPairCompare_reflect`. -/
theorem completeRootJudgment_frameTransport
    (graphs : Fin 4 → RootedDigraph Atom) (points : Fin 4 → CartesianPoint3)
    (slotPerm : Equiv.Perm (Fin 4)) (spaceMirror : Bool) (W D : ℕ)
    (descriptor : _root_.TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (h : CompleteRootDescriptorJudgment
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
      points descriptor) :
    CompleteRootDescriptorJudgment
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (graphs (slotPerm⁻¹ slot)) W D)
      (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot)))
      (labelAdjust spaceMirror descriptor) := by
  obtain ⟨order, raw, hperm, hpair, hgeom, hdesc⟩ := h
  let sourceKey := fun slot =>
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D
  let imageKey := fun slot =>
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs (slotPerm⁻¹ slot)) W D
  have hkey : ∀ slot, imageKey (slotPerm slot) = sourceKey slot := by
    intro slot
    simp [imageKey, sourceKey]
  refine ⟨order.map slotPerm, rawAdjust raw (spaceSign spaceMirror), ?_, ?_, ?_, ?_⟩
  · exact (hperm.map slotPerm).trans slotPerm.map_finRange_perm
  · exact hpair.map slotPerm fun left right hab => by
      simpa [hkey left, hkey right] using hab
  · have hpts :
        (order.map slotPerm).map (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot))) =
          (order.map points).map (applySpace spaceMirror) := by
      simp [List.map_map]
    rw [hpts]
    exact rationalDescriptor_map_applySpace spaceMirror hgeom
  · have hcount : completeRule5PairCount imageKey = completeRule5PairCount sourceKey := by
      have agree : ∀ first second,
          CompletePriorPair imageKey first second ↔
            CompletePriorPair sourceKey (slotPerm⁻¹ first) (slotPerm⁻¹ second) := by
        intro first second
        constructor
        · intro hpair
          refine ⟨slotPerm⁻¹.injective.ne hpair.1, ?_⟩
          have hleft : imageKey first = sourceKey (slotPerm⁻¹ first) := by
            simp [imageKey, sourceKey]
          have hright : imageKey second = sourceKey (slotPerm⁻¹ second) := by
            simp [imageKey, sourceKey]
          simpa [hleft, hright] using hpair.2
        · intro hpair
          refine ⟨by simpa using slotPerm.injective.ne hpair.1, ?_⟩
          have hleft : imageKey first = sourceKey (slotPerm⁻¹ first) := by
            simp [imageKey, sourceKey]
          have hright : imageKey second = sourceKey (slotPerm⁻¹ second) := by
            simp [imageKey, sourceKey]
          simpa [hleft, hright] using hpair.2
      have symm : ∀ first second,
          CompletePriorPair sourceKey first second →
            CompletePriorPair sourceKey second first := fun _ _ hpair => ⟨hpair.1.symm, hpair.2.symm⟩
      have moved := sourceEnantiomorphicPairCount_perm (CompletePriorPair sourceKey) symm slotPerm⁻¹
      have rewritten := sourceEnantiomorphicPairCount_congr_of_forall
        (CompletePriorPair imageKey)
        (fun first second => CompletePriorPair sourceKey (slotPerm⁻¹ first) (slotPerm⁻¹ second))
        agree
      simpa [completeRule5PairCount] using rewritten.trans moved
    unfold sourceKey imageKey at hcount
    cases spaceMirror with
    | false =>
        have hlab : labelAdjust false descriptor = descriptor := by
          unfold labelAdjust
          rfl
        have hraw : rawAdjust raw (spaceSign false) = raw := by
          unfold rawAdjust spaceSign
          rfl
        rw [hlab, hraw, hdesc, hcount]
    | true =>
        have hlab : labelAdjust true descriptor = descriptor.swap := by
          unfold labelAdjust
          rfl
        have hraw : rawAdjust raw (spaceSign true) = RS.swap raw := by
          unfold rawAdjust spaceSign
          rfl
        rw [hlab, hraw, hdesc, hcount]
        exact (classifyTetrahedralRSPseudo_swap raw _).symm

theorem classify_oneStep_reflectUppercase (raw : RS) (count : ℕ)
    (admittedCount : Even count ∨ count = 1) :
    classifyTetrahedralRSPseudo (rawAdjust raw (orientationFactor true true count)) count =
      CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel
        (classifyTetrahedralRSPseudo raw count) := by
  rcases admittedCount with hEven | rfl
  · have hne : count ≠ 1 := by
      intro h1
      rw [h1] at hEven
      obtain ⟨k, hk⟩ := hEven
      omega
    have hpow : (-1 : ℤ) ^ count = 1 := by
      obtain ⟨k, hk⟩ := hEven
      have hk' : count = 2 * k := by omega
      rw [hk', pow_mul]
      norm_num
    simp [orientationFactor, spaceSign, sortSign, rawAdjust, hpow,
      classifyTetrahedralRSPseudo_chiral_of_ne_one _ hne,
      CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel]
  · simp [orientationFactor, spaceSign, sortSign, rawAdjust, classifyTetrahedralRSPseudo,
      CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel, pseudoRSOfRS]

theorem classify_oneStep_count3 (raw : RS) :
    classifyTetrahedralRSPseudo (rawAdjust raw (orientationFactor true true 3)) 3 =
      .chiral raw ∧
    CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel
        (classifyTetrahedralRSPseudo raw 3) =
      .chiral (RS.swap raw) := by
  cases raw <;>
    simp [orientationFactor, spaceSign, sortSign, rawAdjust, classifyTetrahedralRSPseudo,
      CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel, RS.swap]

theorem applySpace_involutive (spaceMirror : Bool) (point : CartesianPoint3) :
    applySpace spaceMirror (applySpace spaceMirror point) = point := by
  cases spaceMirror with
  | false =>
      unfold applySpace
      rfl
  | true =>
      cases point
      simp [applySpace, reflectZ, neg_neg]

theorem labelAdjust_involutive (spaceMirror : Bool)
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel) :
    labelAdjust spaceMirror (labelAdjust spaceMirror descriptor) = descriptor := by
  cases spaceMirror with
  | false =>
      unfold labelAdjust
      rfl
  | true =>
      unfold labelAdjust
      cases descriptor with
      | chiral d => cases d <;> rfl
      | pseudoasymmetric d => cases d <;> rfl

/-- An image judgment pulls back. `reflectZ` and `labelAdjust` are involutions, and the ligand
permutation is inverted, so refusal of a source judgment is refusal of the image judgment. -/
theorem completeRootJudgment_frameTransport_symm
    (graphs : Fin 4 → RootedDigraph Atom) (points : Fin 4 → CartesianPoint3)
    (slotPerm : Equiv.Perm (Fin 4)) (spaceMirror : Bool) (W D : ℕ)
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (h : CompleteRootDescriptorJudgment
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (graphs (slotPerm⁻¹ slot)) W D)
      (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot)))
      (labelAdjust spaceMirror descriptor)) :
    CompleteRootDescriptorJudgment
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
      points descriptor := by
  have hback := completeRootJudgment_frameTransport molecule descriptorMap unit
    (fun slot => graphs (slotPerm⁻¹ slot))
    (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot)))
    slotPerm⁻¹ spaceMirror W D (labelAdjust spaceMirror descriptor) h
  have hkeys :
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (graphs (slotPerm⁻¹ ((slotPerm⁻¹)⁻¹ slot))) W D) =
        fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D := by
    funext slot
    simp [Equiv.symm_apply_apply]
  have hpoints :
      (fun slot => applySpace spaceMirror
        (applySpace spaceMirror (points (slotPerm⁻¹ ((slotPerm⁻¹)⁻¹ slot))))) =
        points := by
    funext slot
    simp [applySpace_involutive, Equiv.symm_apply_apply]
  have hEq :
      CompleteRootDescriptorJudgment
        (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
          (graphs (slotPerm⁻¹ ((slotPerm⁻¹)⁻¹ slot))) W D)
        (fun slot => applySpace spaceMirror
          (applySpace spaceMirror (points (slotPerm⁻¹ ((slotPerm⁻¹)⁻¹ slot)))))
        (labelAdjust spaceMirror (labelAdjust spaceMirror descriptor)) =
      CompleteRootDescriptorJudgment
        (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
        points descriptor := by
    rw [hkeys, hpoints, labelAdjust_involutive]
  exact hEq ▸ hback

theorem completeRootOutcome_frameTransport
    (graphs : Fin 4 → RootedDigraph Atom) (points : Fin 4 → CartesianPoint3)
    (slotPerm : Equiv.Perm (Fin 4)) (spaceMirror : Bool) (W D : ℕ)
    (outcome : Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (h : CompleteRootOutcome
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
      points outcome) :
    CompleteRootOutcome
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
        (graphs (slotPerm⁻¹ slot)) W D)
      (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot)))
      (outcome.map (labelAdjust spaceMirror)) := by
  cases outcome with
  | some descriptor =>
      simpa using completeRootJudgment_frameTransport molecule descriptorMap unit graphs points
        slotPerm spaceMirror W D descriptor h
  | none =>
      intro ⟨d, hd⟩
      have hd' :
          CompleteRootDescriptorJudgment
            (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
              (graphs (slotPerm⁻¹ slot)) W D)
            (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot)))
            (labelAdjust spaceMirror (labelAdjust spaceMirror d)) := by
        simpa [labelAdjust_involutive] using hd
      exact h ⟨labelAdjust spaceMirror d,
        completeRootJudgment_frameTransport_symm molecule descriptorMap unit graphs points
          slotPerm spaceMirror W D (labelAdjust spaceMirror d) hd'⟩

private theorem not_completePriorPair_of_count_zero
    (keys : Fin 4 → CompleteLigandRule5Key)
    (h0 : completeRule5PairCount keys = 0) {i j : Fin 4}
    (hpair : CompletePriorPair keys i j) : False := by
  have hsym : CompletePriorPair keys j i := ⟨hpair.1.symm, hpair.2.symm⟩
  match i, j with
  | 0, 0 => exact hpair.1 rfl
  | 1, 1 => exact hpair.1 rfl
  | 2, 2 => exact hpair.1 rfl
  | 3, 3 => exact hpair.1 rfl
  | 0, 1 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hpair] at h0
  | 1, 0 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hsym] at h0
  | 0, 2 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hpair] at h0
  | 2, 0 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hsym] at h0
  | 1, 2 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hpair] at h0
  | 2, 1 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hsym] at h0
  | 0, 3 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hpair] at h0
  | 3, 0 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hsym] at h0
  | 1, 3 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hpair] at h0
  | 3, 1 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hsym] at h0
  | 2, 3 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hpair] at h0
  | 3, 2 => simp [completeRule5PairCount, sourceEnantiomorphicPairCount, hsym] at h0

private theorem completeRule5PairCount_reindex
    (keys : Fin 4 → CompleteLigandRule5Key) (slotPerm : Equiv.Perm (Fin 4)) :
    completeRule5PairCount (fun slot => keys (slotPerm⁻¹ slot)) = completeRule5PairCount keys := by
  let sourceKey := keys
  let imageKey := fun slot => keys (slotPerm⁻¹ slot)
  have agree : ∀ first second,
      CompletePriorPair imageKey first second ↔
        CompletePriorPair sourceKey (slotPerm⁻¹ first) (slotPerm⁻¹ second) := by
    intro first second
    constructor
    · intro hpair
      refine ⟨slotPerm⁻¹.injective.ne hpair.1, ?_⟩
      have hleft : imageKey first = sourceKey (slotPerm⁻¹ first) := by simp [imageKey, sourceKey]
      have hright : imageKey second = sourceKey (slotPerm⁻¹ second) := by simp [imageKey, sourceKey]
      simpa [hleft, hright] using hpair.2
    · intro hpair
      refine ⟨by simpa using slotPerm.injective.ne hpair.1, ?_⟩
      have hleft : imageKey first = sourceKey (slotPerm⁻¹ first) := by simp [imageKey, sourceKey]
      have hright : imageKey second = sourceKey (slotPerm⁻¹ second) := by simp [imageKey, sourceKey]
      simpa [hleft, hright] using hpair.2
  have symm : ∀ first second,
      CompletePriorPair sourceKey first second → CompletePriorPair sourceKey second first :=
    fun _ _ hpair => ⟨hpair.1.symm, hpair.2.symm⟩
  have moved := sourceEnantiomorphicPairCount_perm (CompletePriorPair sourceKey) symm slotPerm⁻¹
  have rewritten := sourceEnantiomorphicPairCount_congr_of_forall
    (CompletePriorPair imageKey)
    (fun first second => CompletePriorPair sourceKey (slotPerm⁻¹ first) (slotPerm⁻¹ second)) agree
  simpa [completeRule5PairCount, imageKey, sourceKey] using rewritten.trans moved

/-- Dependency reflection with no prior tie. The same ligand permutation moves keys and
coordinates. Every distinct pair has unequal prior keys, so `retainedPairCompare_reflect` leaves
the comparison unchanged and the sort sign is `+1`. A coordinate mirror therefore swaps only the
uppercase letter: the count is zero, not one, and not the count-three case. -/
theorem completeRootJudgment_dependencyMirror_countZero
    (graphs : Fin 4 → RootedDigraph Atom) (points : Fin 4 → CartesianPoint3)
    (slotPerm : Equiv.Perm (Fin 4)) (spaceMirror : Bool) (W D : ℕ)
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (hcount0 : completeRule5PairCount
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D) = 0)
    (h : CompleteRootDescriptorJudgment
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D)
      points descriptor) :
    CompleteRootDescriptorJudgment
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
        (graphs (slotPerm⁻¹ slot)) W D)
      (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot)))
      (if spaceMirror then
        CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel descriptor else descriptor) := by
  obtain ⟨order, raw, hperm, hpair, hgeom, hdesc⟩ := h
  let sourceKey := fun slot =>
    retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D
  let imageKey := fun slot =>
    retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
      (graphs (slotPerm⁻¹ slot)) W D
  have hkey : ∀ slot,
      imageKey (slotPerm slot) =
        retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit (graphs slot) W D := by
    intro slot
    simp [imageKey]
  have himageCount : completeRule5PairCount imageKey = 0 := by
    have hreindex := completeRule5PairCount_reindex
      (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
        (graphs slot) W D) slotPerm
    have hrefl := completeRule5PairCount_reflect molecule descriptorMap unit graphs W D
    have hsource : completeRule5PairCount sourceKey = 0 := by simpa [sourceKey] using hcount0
    simpa [imageKey, sourceKey, hsource] using hreindex.trans hrefl
  refine ⟨order.map slotPerm, rawAdjust raw (spaceSign spaceMirror), ?_, ?_, ?_, ?_⟩
  · exact (hperm.map slotPerm).trans slotPerm.map_finRange_perm
  · exact hpair.map slotPerm fun left right hab => by
      have hne : left ≠ right := by
        intro heq
        subst heq
        exact lt_irrefl _ hab
      have hprior :
          retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs right) W D ≠
            retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs left) W D := by
        intro heq
        exact not_completePriorPair_of_count_zero sourceKey (by simpa [sourceKey] using hcount0)
          ⟨hne.symm, by
            simpa [sourceKey, retainedCompleteLigandRule5KeyAt_prior] using heq⟩
      have hcmp := retainedPairCompare_reflect molecule descriptorMap unit
        (graphs right) (graphs left) W D
      rw [if_neg hprior] at hcmp
      have hlt : compare (sourceKey right) (sourceKey left) = Ordering.lt :=
        (completeLigandRule5Key_compare_lt_iff (sourceKey right) (sourceKey left)).2 hab
      have himg :
          compare (imageKey (slotPerm right)) (imageKey (slotPerm left)) = Ordering.lt := by
        simpa [hkey right, hkey left, sourceKey, hlt] using hcmp
      exact (completeLigandRule5Key_compare_lt_iff _ _).1 himg
  · have hpts :
        (order.map slotPerm).map (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot))) =
          (order.map points).map (applySpace spaceMirror) := by
      simp [List.map_map]
    rw [hpts]
    exact rationalDescriptor_map_applySpace spaceMirror hgeom
  · rw [himageCount]
    cases spaceMirror with
    | false =>
        have hraw : rawAdjust raw (spaceSign false) = raw := by
          unfold rawAdjust spaceSign
          rfl
        rw [hraw, hdesc]
        have hzero : completeRule5PairCount sourceKey = 0 := by simpa [sourceKey] using hcount0
        rw [hzero, if_neg (by decide : ¬ false = true)]
    | true =>
        have hraw : rawAdjust raw (spaceSign true) = RS.swap raw := by
          unfold rawAdjust spaceSign
          rfl
        rw [hraw, hdesc]
        have hzero : completeRule5PairCount sourceKey = 0 := by simpa [sourceKey] using hcount0
        rw [hzero]
        have hclass : classifyTetrahedralRSPseudo raw 0 = .chiral raw := by
          simp [classifyTetrahedralRSPseudo, show ¬ 0 = 1 by decide]
        rw [hclass]
        cases raw <;>
          simp [classifyTetrahedralRSPseudo,
            CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel, RS.swap,
            show ¬ 0 = 1 by decide]

end

end TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.retainedPairCompare_reflect
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.retainedRule5SeniorCompare_swap_of_equalSignature
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.retainedTaggedAlternativeReferencesAt_reflect
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.retainedCompleteRule5ReadingsAt_reflect
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.completeRule5PairCount_reflect
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.framePerm_sign_cancels
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.rationalDescriptor_map_applySpace
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.completeRootJudgment_frameTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.completeRootJudgment_frameTransport_symm
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.completeRootOutcome_frameTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.completeRootJudgment_dependencyMirror_countZero
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.classify_oneStep_reflectUppercase
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport.classify_oneStep_count3
