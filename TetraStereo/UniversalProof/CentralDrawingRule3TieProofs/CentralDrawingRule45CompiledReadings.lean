import TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
import TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingLeafRefusal
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45Exact

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

/-!
# Actual compiled central common-reference readings

The actual production frame determines each compound builder output at its original central
cursor.  Under the corrected geometry calibration the source-derived scheduled labels are `S` at
slot `2` and `R` at slot `3` (the upstream declarations keep their historical `_R`/`_S` names with
corrected statements).  Those labels determine the singleton reference populations and Rule-5
reading populations, and the four genuine common-reference descriptor heads:

* slot `2` (`S`): common `R` head `[2, 1, 0, 0]`, common `S` head `[2, 1, 0, 1]`;
* slot `3` (`R`): common `R` head `[2, 1, 0, 1]`, common `S` head `[2, 1, 0, 0]`.

Hence the actual common-`R` comparison of the slot-2/slot-3 reading lists is `lt` and the actual
common-`S` comparison is `gt`, both without any caller reading/head hypothesis.  The reversed
slot order swaps those results.  Earlier Rule-3 and complete Rule-4b/4c ties remain explicit
obligations; these facts alone do not establish the central descriptor or scientific approval.

The historical declaration names `central_actual_commonR_gt`, `central_actual_commonS_lt`,
`central_actual_commonR_reversed_lt` and `central_actual_commonS_reversed_gt` are retained because
they are kernel-certificate keys.  Their statements now record the actual corrected directions,
and accurately named siblings (`..._lt`, `..._gt`, ...) are provided alongside them.
-/

private theorem mapM_actual_outputs {α β : Type*} (f : α → Option β) :
    ∀ inputs outputs, inputs.mapM f = some outputs →
      List.Forall₂ (fun input output => f input = some output) inputs outputs
  | [], outputs, computed => by
      simp at computed
      subst outputs
      exact .nil
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases first : f input with
      | none => simp [first] at computed
      | some output =>
          cases rest : inputs.mapM f with
          | none => simp [first, rest] at computed
          | some tail =>
              simp [first, rest] at computed
              subst outputs
              exact .cons first (mapM_actual_outputs f inputs tail rest)

private theorem keyFrame_actual_outputs
    (input : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : input.AromaticCanonicalOccurrence carrierFuel)
    (view : input.AromaticCanonicalDependencyView target) (fuel : Nat)
    (roots : List (input.AromaticCanonicalRerootCursor carrierFuel))
    (frame : input.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : input.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel roots = some frame) :
    List.Forall₂ (fun cursor key => input.buildAromaticCanonicalRerootCompoundRule45Key?
      target view fuel cursor = some key) roots frame.rule45Keys := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? at computed
  cases rule3Computed : input.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel roots with
  | none => simp [rule3Computed] at computed
  | some rule3Frame =>
      by_cases length3 : rule3Frame.keys.length = 4
      · cases keysComputed : roots.mapM
            (input.buildAromaticCanonicalRerootCompoundRule45Key? target view fuel) with
        | none => simp [rule3Computed, keysComputed] at computed
        | some keys =>
            by_cases length45 : keys.length = 4
            · simp [rule3Computed, length3, keysComputed, length45] at computed
              subst frame
              exact mapM_actual_outputs _ roots keys keysComputed
            · simp [rule3Computed, keysComputed, length45] at computed
      · simp [rule3Computed, length3] at computed

theorem central_rule45_keyAt_computed (slot : Fin 4) :
    source.buildAromaticCanonicalRerootCompoundRule45Key? centralTarget centralView 4
      (centralRootAt slot) = some (centralKeyFrame.keyAt slot).rule45 := by
  have outputs := keyFrame_actual_outputs source centralTarget centralView 4 centralRoots
    centralKeyFrame centralKeyFrame_computed
  exact outputs.get (i := slot.val)
    (by rw [central_roots_length]; exact slot.isLt)
    (by rw [centralKeyFrame.rule45Length]; exact slot.isLt)

private theorem singleton_rule4bc_reading
    (input : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : input.AromaticCanonicalOccurrence carrierFuel)
    (view : input.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursor : input.AromaticCanonicalRerootCursor carrierFuel) (reference : RS)
    (readings : List input.AromaticCanonicalRerootRule4bcReading)
    (derived : input.CanonicalAromaticCanonicalRerootRule4bcReadings
      target view fuel cursor [some reference] readings) :
    ∃ reading, readings = [reading] ∧ reading.reference? = some reference := by
  cases derived with
  | cons first rest =>
      cases rest
      cases first with
      | reference rule4b rule4c => exact ⟨_, rfl, rfl⟩

private theorem singleton_rule5_reading
    (input : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : input.AromaticCanonicalOccurrence carrierFuel)
    (view : input.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursor : input.AromaticCanonicalRerootCursor carrierFuel)
    (prior : input.AromaticCanonicalRerootRule4bcReading)
    (readings : List input.AromaticCanonicalRerootRule5Reading)
    (derived : input.CanonicalAromaticCanonicalRerootRule5Readings
      target view fuel cursor [prior] readings) :
    ∃ reading, readings = [reading] ∧
      input.CanonicalAromaticCanonicalRerootRule5Reading target view fuel cursor prior reading := by
  cases derived with
  | cons first rest =>
      cases rest
      exact ⟨_, rfl, first⟩

/-- Successful compilation plus the actual source label supplies the singleton and both heads.
This generic intermediate lemma is instantiated below on the internally constructed frame. -/
theorem actual_compound_rule5_reading_of_chiral_label
    (input : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : input.AromaticCanonicalOccurrence carrierFuel)
    (view : input.AromaticCanonicalDependencyView target) (fuel : Nat)
    (cursor : input.AromaticCanonicalRerootCursor carrierFuel)
    (key : input.AromaticCanonicalRerootCompoundRule45Key) (reference : RS)
    (computed : input.buildAromaticCanonicalRerootCompoundRule45Key?
      target view fuel cursor = some key)
    (label : input.aromaticCanonicalDependencyLabel target view cursor = some (.chiral reference)) :
    key.prior.references = [reference] ∧ ∃ reading,
      key.rule5Readings = [reading] ∧ reading.prior.reference? = some reference ∧
      reading.commonR.descriptor.head? = some [([], localizedCumulativeRule45Priority
        (.rule5 reference RS.R) (some (.chiral reference)))] ∧
      reading.commonS.descriptor.head? = some [([], localizedCumulativeRule45Priority
        (.rule5 reference RS.S) (some (.chiral reference)))] := by
  have canonical := (input.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
    target view fuel cursor key).mp computed
  have rule4aComputed := (input.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
    .rule4a target view fuel cursor key.prior.rule4aKey).mpr canonical.1.1
  have rankedHead := buildAromaticCanonicalCumulativeRule45Key?_rankedLabels_head
    input .rule4a target view fuel cursor key.prior.rule4aKey rule4aComputed
  rw [label] at rankedHead
  have refsComputed := (localizedRule4bReferencesFromRankedLabels_eq_iff
    key.prior.rule4aKey.rankedLabels key.prior.references).mpr canonical.1.2.1
  have references : key.prior.references = [reference] := by
    cases layersEq : key.prior.rule4aKey.rankedLabels with
    | nil => simp [layersEq] at rankedHead
    | cons first tail =>
        have firstEq : first = [([], some (.chiral reference))] := by
          simpa [layersEq] using rankedHead
        rw [layersEq, firstEq] at refsComputed
        cases reference with
        | R => exact refsComputed.symm.trans (localizedRule4bReferencesFromRankedLabels_cons_chiral_R tail)
        | S => exact refsComputed.symm.trans (localizedRule4bReferencesFromRankedLabels_cons_chiral_S tail)
  have priorReadings := canonical.1.2.2.2
  have alternatives : aromaticCanonicalRule4bcReferenceAlternatives key.prior.references =
      [some reference] := by simp [references, aromaticCanonicalRule4bcReferenceAlternatives]
  rw [alternatives] at priorReadings
  obtain ⟨prior, priorList, priorReference⟩ := singleton_rule4bc_reading
    input target view fuel cursor reference key.prior.readings priorReadings
  have rule5Readings := canonical.2
  rw [priorList] at rule5Readings
  obtain ⟨reading, readingList, meaning⟩ := singleton_rule5_reading
    input target view fuel cursor prior key.rule5Readings rule5Readings
  have commonRComputed := (input.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
    (aromaticCanonicalRule5StageFor prior.reference? RS.R)
    target view fuel cursor reading.commonR).mpr meaning.2.1
  have commonSComputed := (input.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
    (aromaticCanonicalRule5StageFor prior.reference? RS.S)
    target view fuel cursor reading.commonS).mpr meaning.2.2
  rw [priorReference] at commonRComputed commonSComputed
  refine ⟨references, reading, readingList, ?_, ?_, ?_⟩
  · rw [meaning.1]
    exact priorReference
  · exact buildAromaticCanonicalCumulativeRule45Key?_descriptor_head_of_label input
      (.rule5 reference RS.R) target view commonRComputed label
  · exact buildAromaticCanonicalCumulativeRule45Key?_descriptor_head_of_label input
      (.rule5 reference RS.S) target view commonSComputed label

/-- Actual left key references are derived from compiled ranked labels and the scheduled `S`. -/
theorem central_left_prior_references :
    (centralKeyFrame.keyAt centralSlotTwo).rule45.prior.references = [RS.S] :=
  (actual_compound_rule5_reading_of_chiral_label source centralTarget centralView 4
    (centralRootAt centralSlotTwo) (centralKeyFrame.keyAt centralSlotTwo).rule45 RS.S
    (central_rule45_keyAt_computed centralSlotTwo) central_slot_two_label).1

/-- Actual right key references are derived from compiled ranked labels and the scheduled `R`. -/
theorem central_right_prior_references :
    (centralKeyFrame.keyAt centralSlotThree).rule45.prior.references = [RS.R] :=
  (actual_compound_rule5_reading_of_chiral_label source centralTarget centralView 4
    (centralRootAt centralSlotThree) (centralKeyFrame.keyAt centralSlotThree).rule45 RS.R
    (central_rule45_keyAt_computed centralSlotThree) central_slot_three_label).1

theorem central_left_rule5_reading_exists : ∃ reading : source.AromaticCanonicalRerootRule5Reading,
    (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = [reading] ∧
    reading.prior.reference? = some RS.S ∧
    reading.commonR.descriptor.head? = some [([], [2, 1, 0, 0])] ∧
    reading.commonS.descriptor.head? = some [([], [2, 1, 0, 1])] := by
  obtain ⟨reading, readings, reference, commonR, commonS⟩ :=
    (actual_compound_rule5_reading_of_chiral_label source centralTarget centralView 4
      (centralRootAt centralSlotTwo) (centralKeyFrame.keyAt centralSlotTwo).rule45 RS.S
      (central_rule45_keyAt_computed centralSlotTwo) central_slot_two_label).2
  exact ⟨reading, readings, reference,
    by simpa only [localizedCumulativeRule45Priority_commonR_S] using commonR,
    by simpa only [localizedCumulativeRule45Priority_commonS_S] using commonS⟩

theorem central_right_rule5_reading_exists : ∃ reading : source.AromaticCanonicalRerootRule5Reading,
    (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = [reading] ∧
    reading.prior.reference? = some RS.R ∧
    reading.commonR.descriptor.head? = some [([], [2, 1, 0, 1])] ∧
    reading.commonS.descriptor.head? = some [([], [2, 1, 0, 0])] := by
  obtain ⟨reading, readings, reference, commonR, commonS⟩ :=
    (actual_compound_rule5_reading_of_chiral_label source centralTarget centralView 4
      (centralRootAt centralSlotThree) (centralKeyFrame.keyAt centralSlotThree).rule45 RS.R
      (central_rule45_keyAt_computed centralSlotThree) central_slot_three_label).2
  exact ⟨reading, readings, reference,
    by simpa only [localizedCumulativeRule45Priority_commonR_R] using commonR,
    by simpa only [localizedCumulativeRule45Priority_commonS_R] using commonS⟩

noncomputable def centralLeftRule5Reading := Classical.choose central_left_rule5_reading_exists
noncomputable def centralRightRule5Reading := Classical.choose central_right_rule5_reading_exists

theorem centralLeftRule5Reading_spec :
    (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = [centralLeftRule5Reading] ∧
    centralLeftRule5Reading.prior.reference? = some RS.S ∧
    centralLeftRule5Reading.commonR.descriptor.head? = some [([], [2, 1, 0, 0])] ∧
    centralLeftRule5Reading.commonS.descriptor.head? = some [([], [2, 1, 0, 1])] :=
  Classical.choose_spec central_left_rule5_reading_exists

theorem centralRightRule5Reading_spec :
    (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = [centralRightRule5Reading] ∧
    centralRightRule5Reading.prior.reference? = some RS.R ∧
    centralRightRule5Reading.commonR.descriptor.head? = some [([], [2, 1, 0, 1])] ∧
    centralRightRule5Reading.commonS.descriptor.head? = some [([], [2, 1, 0, 0])] :=
  Classical.choose_spec central_right_rule5_reading_exists

private theorem compare_sparse_heads_gt
    (left right : List (List (OfficialSparseEntry (List Nat)))) (leftValue rightValue : List Nat)
    (leftHead : left.head? = some [([], leftValue)])
    (rightHead : right.head? = some [([], rightValue)])
    (strict : compareLocalizedCumulativeRule45Priority leftValue rightValue = Ordering.gt) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority left right =
      Ordering.gt := by
  cases left with
  | nil => simp at leftHead
  | cons first leftTail =>
      have firstEq : first = [([], leftValue)] := Option.some.inj leftHead
      subst first
      cases right with
      | nil => simp at rightHead
      | cons second rightTail =>
          have secondEq : second = [([], rightValue)] := Option.some.inj rightHead
          subst second
          exact compareSparseLayers_cons_gt compareLocalizedCumulativeRule45Priority
            leftValue rightValue leftTail rightTail strict

private theorem compare_sparse_heads_lt
    (left right : List (List (OfficialSparseEntry (List Nat)))) (leftValue rightValue : List Nat)
    (leftHead : left.head? = some [([], leftValue)])
    (rightHead : right.head? = some [([], rightValue)])
    (strict : compareLocalizedCumulativeRule45Priority leftValue rightValue = Ordering.lt) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority left right =
      Ordering.lt := by
  cases left with
  | nil => simp at leftHead
  | cons first leftTail =>
      have firstEq : first = [([], leftValue)] := Option.some.inj leftHead
      subst first
      cases right with
      | nil => simp at rightHead
      | cons second rightTail =>
          have secondEq : second = [([], rightValue)] := Option.some.inj rightHead
          subst second
          exact compareSparseLayers_cons_lt compareLocalizedCumulativeRule45Priority
            leftValue rightValue leftTail rightTail strict

/-- The actual common-`R` decision on the compiled central reading lists is `lt`: the slot-2
`S` reading is headed `[2, 1, 0, 0]`, the slot-3 `R` reading `[2, 1, 0, 1]`. -/
theorem central_actual_commonR_lt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.R
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = Ordering.lt := by
  rw [centralLeftRule5Reading_spec.1, centralRightRule5Reading_spec.1,
    compareAromaticCanonicalRerootCompoundRule5Readings_R_singleton source centralLeftRule5Reading centralRightRule5Reading]
  exact compare_sparse_heads_lt _ _ [2, 1, 0, 0] [2, 1, 0, 1]
    centralLeftRule5Reading_spec.2.2.1 centralRightRule5Reading_spec.2.2.1
    compareLocalizedCumulativeRule45Priority_commonR_reversed

/-- Historical kernel-certificate key.  Under the corrected calibration the actual common-`R`
decision is `lt`, not `gt`; the accurately named declaration is `central_actual_commonR_lt`. -/
theorem central_actual_commonR_gt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.R
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = Ordering.lt :=
  central_actual_commonR_lt

/-- The actual common-`S` decision on the compiled central reading lists is `gt`: the slot-2
`S` reading is headed `[2, 1, 0, 1]`, the slot-3 `R` reading `[2, 1, 0, 0]`. -/
theorem central_actual_commonS_gt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.S
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = Ordering.gt := by
  rw [centralLeftRule5Reading_spec.1, centralRightRule5Reading_spec.1,
    compareAromaticCanonicalRerootCompoundRule5Readings_S_singleton source centralLeftRule5Reading centralRightRule5Reading]
  exact compare_sparse_heads_gt _ _ [2, 1, 0, 1] [2, 1, 0, 0]
    centralLeftRule5Reading_spec.2.2.2 centralRightRule5Reading_spec.2.2.2
    compareLocalizedCumulativeRule45Priority_commonS_reversed

/-- Historical kernel-certificate key.  Under the corrected calibration the actual common-`S`
decision is `gt`, not `lt`; the accurately named declaration is `central_actual_commonS_gt`. -/
theorem central_actual_commonS_lt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.S
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = Ordering.gt :=
  central_actual_commonS_gt

/-- Reversed slot order: the actual common-`R` decision is `gt`. -/
theorem central_actual_commonR_reversed_gt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.R
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = Ordering.gt := by
  rw [centralRightRule5Reading_spec.1, centralLeftRule5Reading_spec.1,
    compareAromaticCanonicalRerootCompoundRule5Readings_R_singleton source centralRightRule5Reading centralLeftRule5Reading]
  exact compare_sparse_heads_gt _ _ [2, 1, 0, 1] [2, 1, 0, 0]
    centralRightRule5Reading_spec.2.2.1 centralLeftRule5Reading_spec.2.2.1
    compareLocalizedCumulativeRule45Priority_commonR_decisive

/-- Historical kernel-certificate key.  Under the corrected calibration the reversed common-`R`
decision is `gt`, not `lt`; the accurately named declaration is
`central_actual_commonR_reversed_gt`. -/
theorem central_actual_commonR_reversed_lt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.R
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = Ordering.gt :=
  central_actual_commonR_reversed_gt

/-- Reversed slot order: the actual common-`S` decision is `lt`. -/
theorem central_actual_commonS_reversed_lt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.S
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = Ordering.lt := by
  rw [centralRightRule5Reading_spec.1, centralLeftRule5Reading_spec.1,
    compareAromaticCanonicalRerootCompoundRule5Readings_S_singleton source centralRightRule5Reading centralLeftRule5Reading]
  exact compare_sparse_heads_lt _ _ [2, 1, 0, 0] [2, 1, 0, 1]
    centralRightRule5Reading_spec.2.2.2 centralLeftRule5Reading_spec.2.2.2
    compareLocalizedCumulativeRule45Priority_commonS_decisive

/-- Historical kernel-certificate key.  Under the corrected calibration the reversed common-`S`
decision is `lt`, not `gt`; the accurately named declaration is
`central_actual_commonS_reversed_lt`. -/
theorem central_actual_commonS_reversed_gt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.S
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = Ordering.lt :=
  central_actual_commonS_reversed_lt

/-- Only the two earlier comparator ties remain; reading witnesses and heads are discharged.
Under the corrected calibration the actual slot-2/slot-3 comparison is `lt` with the
enantiomorphic signal. -/
theorem central_drawing_rule45_forward_of_actual_prior_ties
    (rule3Tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule3
      (centralKeyFrame.keyAt centralSlotThree).rule3 = Ordering.eq)
    (priorTie : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior = Ordering.eq) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
      centralKeyFrame centralSlotTwo centralSlotThree = { ordering := Ordering.lt, pseudo := true } := by
  rw [source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    centralKeyFrame centralSlotTwo centralSlotThree rule3Tie]
  exact compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_lt_gt source _ _
    priorTie central_actual_commonR_lt central_actual_commonS_gt

/-- The reversed actual comparison is `gt` with the enantiomorphic signal. -/
theorem central_drawing_rule45_reversed_of_actual_prior_ties
    (rule3Tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotThree).rule3
      (centralKeyFrame.keyAt centralSlotTwo).rule3 = Ordering.eq)
    (priorTie : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior = Ordering.eq) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
      centralKeyFrame centralSlotThree centralSlotTwo = { ordering := Ordering.gt, pseudo := true } := by
  rw [source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    centralKeyFrame centralSlotThree centralSlotTwo rule3Tie]
  exact compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_gt_lt source _ _
    priorTie central_actual_commonR_reversed_gt central_actual_commonS_reversed_lt

end TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
