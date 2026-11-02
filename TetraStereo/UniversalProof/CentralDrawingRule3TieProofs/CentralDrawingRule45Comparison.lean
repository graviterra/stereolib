import TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingOccurrenceModel

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

/-!
# The decisive central Rule-4/5 comparator over the committed three-center drawing source

This module works on the actual drawing-only successor of `ThreeCenterDrawingSourceProofs`.  The central final
occurrence `centralTarget` carries the actual returned four-ligand frame `centralRoots`, and the
internally scheduled drawing model supplies its restricted view `centralView`.  Under the
corrected geometry calibration (negative exact oriented volume is `R`, positive is `S`) the two
genuine drawing dependency values at the equal-carbon ligands are `S` at slot `2` (the historical
key `central_left_dependency_label_R`, whose statement is corrected upstream) and `R` at slot `3`
(the historical key `central_right_dependency_label_S`).  Nothing from the old spatial or
auxiliary model is transported.

The comparator chain reconstructed here is the normative order
`Rule 3 → Rule 4a → Rule 4b → Rule 4c → Rule 5`.  Two families of facts are proved in full:

* the decisive Rule-5 reading arithmetic on the cumulative node vectors `[2, 1, 0, 1]`
  (common `R`) and `[2, 1, 0, 0]` (common `S`), and the head-of-first-layer decision of
  `OfficialRuleMajorKey.compareSparseLayers`; and
* the whole `compareAromaticCanonicalRerootCompoundThroughRule5` reduction once the prior
  Rule-4b/4c key has tied.

The **actual** fixture now instantiates the mirrored vector pattern: at the actual labels the
slot-2 (`S`) common-`R`/common-`S` heads are `[2, 1, 0, 0]` / `[2, 1, 0, 1]`, while the slot-3
(`R`) heads are `[2, 1, 0, 1]` / `[2, 1, 0, 0]`.  Consequently the actual forward comparison is
`lt` with the enantiomorphic (`pseudo`) signal, and the reversed comparison is `gt` with the same
signal.  The historical lemmas `central_drawing_rule45_decisive_forward` / `_reversed` are retained
with their original, still-true conditional statements (the opposite-vector mirror); the
declarations `central_drawing_rule45_decisive_actual` / `_actual_reversed` below state the
directions actually realised by the corrected drawing model.

These are *reductions*: the two genuinely deep obligations — the Rule-3 automorphism tie at the
two identical-carbon ligand occurrences and the Rule-4b/4c uppercase reflection of the actual
compiled keys — are the retained hypotheses `rule3Tie`/`priorTie`, and the actual
descriptor-head equations are the retained `leftCommon{R,S}`/`rightCommon{R,S}` hypotheses.
They are not restated as a `Complete`-style contract, and no caller comparator, expected label or
key-success value is assumed by the closed lemmas of sections 1--5.
-/

/-! ## 1. Decisive Rule-5 cumulative node vectors

The common-`R` reading of an `R` ligand and the common-`S` reading of an `R` ligand are the
vectors `[2, 1, 0, 1]` / `[2, 1, 0, 0]`; the mirrored `S` ligand reverses the pair.  These are
pure computations on the cumulative Rules-4a--5 stage and are unchanged by the calibration repair
(the symbolic `RS` values are not reinterpreted). -/

theorem localizedCumulativeRule45Priority_commonR_R :
    localizedCumulativeRule45Priority (.rule5 RS.R RS.R) (some (.chiral RS.R)) =
      [2, 1, 0, 1] := by decide

theorem localizedCumulativeRule45Priority_commonR_S :
    localizedCumulativeRule45Priority (.rule5 RS.S RS.R) (some (.chiral RS.S)) =
      [2, 1, 0, 0] := by decide

theorem localizedCumulativeRule45Priority_commonS_R :
    localizedCumulativeRule45Priority (.rule5 RS.R RS.S) (some (.chiral RS.R)) =
      [2, 1, 0, 0] := by decide

theorem localizedCumulativeRule45Priority_commonS_S :
    localizedCumulativeRule45Priority (.rule5 RS.S RS.S) (some (.chiral RS.S)) =
      [2, 1, 0, 1] := by decide

theorem compareLocalizedCumulativeRule45Priority_commonR_decisive :
    compareLocalizedCumulativeRule45Priority [2, 1, 0, 1] [2, 1, 0, 0] =
      Ordering.gt := by decide

theorem compareLocalizedCumulativeRule45Priority_commonR_reversed :
    compareLocalizedCumulativeRule45Priority [2, 1, 0, 0] [2, 1, 0, 1] =
      Ordering.lt := by decide

theorem compareLocalizedCumulativeRule45Priority_commonS_decisive :
    compareLocalizedCumulativeRule45Priority [2, 1, 0, 0] [2, 1, 0, 1] =
      Ordering.lt := by decide

theorem compareLocalizedCumulativeRule45Priority_commonS_reversed :
    compareLocalizedCumulativeRule45Priority [2, 1, 0, 1] [2, 1, 0, 0] =
      Ordering.gt := by decide

/-! ## 2. The first descriptor layer decides the sparse-layers comparison

The cumulative descriptor of every compiled cumulative key is headed by the singleton layer
`[[([], priority)]]`.  Two descriptors whose first layers carry different cumulative vectors are
therefore decided at that first layer, independently of every deeper merged sphere. -/

private theorem compareLex_singleton {α : Type*} (compare : α → α → Ordering) (a b : α) :
    List.compareLex compare [a] [b] = compare a b := by
  rw [List.compareLex_cons_cons]
  cases h : compare a b <;> rfl

/-- A strictly greater first-layer cumulative vector decides the whole sparse-layers comparison
as `gt`, whatever the remaining merged spheres are. -/
theorem compareSparseLayers_cons_gt {α : Type*}
    (compare : α → α → Ordering) (a b : α)
    (leftRest rightRest : List (List (OfficialSparseEntry α)))
    (compared : compare a b = Ordering.gt) :
    OfficialRuleMajorKey.compareSparseLayers compare
      ([([], a)] :: leftRest) ([([], b)] :: rightRest) = Ordering.gt := by
  simp [OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry, List.compareLex, compareLex, Ordering.byKey,
    flip, compared]

/-- The mirrored strict case decides the whole sparse-layers comparison as `lt`. -/
theorem compareSparseLayers_cons_lt {α : Type*}
    (compare : α → α → Ordering) (a b : α)
    (leftRest rightRest : List (List (OfficialSparseEntry α)))
    (compared : compare a b = Ordering.lt) :
    OfficialRuleMajorKey.compareSparseLayers compare
      ([([], a)] :: leftRest) ([([], b)] :: rightRest) = Ordering.lt := by
  simp [OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
    OfficialRuleMajorKey.compareSparseEntry, List.compareLex, compareLex, Ordering.byKey,
    flip, compared]

/-! ## 3. Singleton common-reference reading lists

Each ligand carries exactly one Rule-4b reference, so its compound Rule-5 reading list is a
singleton.  Comparing two singleton lists under a common reference is precisely the sparse-layers
comparison of the selected common-`R` or common-`S` projection. -/

theorem compareAromaticCanonicalRerootCompoundRule5Readings_R_singleton
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootRule5Reading) :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.R [left] [right] =
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.commonR.descriptor right.commonR.descriptor := by
  have unfolded :
      source.compareAromaticCanonicalRerootCompoundRule5Readings RS.R [left] [right] =
        List.compareLex
          (Ordering.byKey (fun reading : source.AromaticCanonicalRerootRule5Reading =>
              reading.commonR.descriptor)
            (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
          [left] [right] := rfl
  rw [unfolded, compareLex_singleton]
  rfl

theorem compareAromaticCanonicalRerootCompoundRule5Readings_S_singleton
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootRule5Reading) :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.S [left] [right] =
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.commonS.descriptor right.commonS.descriptor := by
  have unfolded :
      source.compareAromaticCanonicalRerootCompoundRule5Readings RS.S [left] [right] =
        List.compareLex
          (Ordering.byKey (fun reading : source.AromaticCanonicalRerootRule5Reading =>
              reading.commonS.descriptor)
            (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
          [left] [right] := rfl
  rw [unfolded, compareLex_singleton]
  rfl

/-! ## 4. The decisive Rule-5 comparator

Once the complete compound Rules-4b/4c prior key has tied, Rule 5 reads the hierarchy under a
common `R` and a common `S` reference.  Opposite decisions under the two common references are
exactly the `±2` enantiomorphic comparison that stamps the lowercase pseudoasymmetric signal. -/

theorem compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_gt_lt
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (priorTie : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq)
    (commonR : source.compareAromaticCanonicalRerootCompoundRule5Readings
      RS.R left.rule5Readings right.rule5Readings = Ordering.gt)
    (commonS : source.compareAromaticCanonicalRerootCompoundRule5Readings
      RS.S left.rule5Readings right.rule5Readings = Ordering.lt) :
    source.compareAromaticCanonicalRerootCompoundThroughRule5 left right =
      { ordering := Ordering.gt, pseudo := true } := by
  simp only [compareAromaticCanonicalRerootCompoundThroughRule5, priorTie, commonR, commonS]
  decide

theorem compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_lt_gt
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRerootCompoundRule45Key)
    (priorTie : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq)
    (commonR : source.compareAromaticCanonicalRerootCompoundRule5Readings
      RS.R left.rule5Readings right.rule5Readings = Ordering.lt)
    (commonS : source.compareAromaticCanonicalRerootCompoundRule5Readings
      RS.S left.rule5Readings right.rule5Readings = Ordering.gt) :
    source.compareAromaticCanonicalRerootCompoundThroughRule5 left right =
      { ordering := Ordering.lt, pseudo := true } := by
  simp only [compareAromaticCanonicalRerootCompoundThroughRule5, priorTie, commonR, commonS]
  decide

/-! ## 5. The compiled cumulative key is headed by its own dependency vector

Both the terminal and the branching clause of `buildAromaticCanonicalCumulativeRule45Key?` emit
`[[([], priority)]]` as the first descriptor sphere and `[[([], label)]]` as the first ranked-label
sphere, where `priority`/`label` are read from `aromaticCanonicalDependencyLabel` at the compiled
cursor.  These two heads are therefore the actual compiled values, not a caller-supplied
expectation. -/

theorem buildAromaticCanonicalCumulativeRule45Key?_descriptor_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor = some key →
      key.descriptor.head? =
        some [([], localizedCumulativeRule45Priority stage
          (source.aromaticCanonicalDependencyLabel target view cursor))]
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45Key? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        rfl
      · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45Key? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        rfl
      · cases childKeysComputed : children.mapM
            (source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel) with
        | none => simp [children, terminal, childKeysComputed] at computed
        | some childKeys =>
            simp [children, terminal, childKeysComputed] at computed
            subst key
            rfl

theorem buildAromaticCanonicalCumulativeRule45Key?_rankedLabels_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor = some key →
      key.rankedLabels.head? =
        some [([], source.aromaticCanonicalDependencyLabel target view cursor)]
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45Key? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        rfl
      · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45Key? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        rfl
      · cases childKeysComputed : children.mapM
            (source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel) with
        | none => simp [children, terminal, childKeysComputed] at computed
        | some childKeys =>
            simp [children, terminal, childKeysComputed] at computed
            subst key
            rfl

/-- Label-parameterized form: the compiled descriptor head is the cumulative vector of the actual
dependency label. -/
theorem buildAromaticCanonicalCumulativeRule45Key?_descriptor_head_of_label
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    {fuel : Nat} {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalCumulativeRule45Key}
    {label : Option AromaticCanonicalAuxiliaryLabel}
    (computed : source.buildAromaticCanonicalCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (read : source.aromaticCanonicalDependencyLabel target view cursor = label) :
    key.descriptor.head? =
      some [([], localizedCumulativeRule45Priority stage label)] := by
  rw [buildAromaticCanonicalCumulativeRule45Key?_descriptor_head
    source stage target view fuel cursor key computed, read]

/-- A first ranked-label sphere headed by an uppercase `R` chiral descriptor fixes the Rule-4b
reference population to the unique reference `[R]` (P-92.5.2.1(a)). -/
theorem localizedRule4bReferencesFromRankedLabels_cons_chiral_R
    (tail : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    localizedRule4bReferencesFromRankedLabels
      ([([], some (.chiral RS.R))] :: tail) = [RS.R] := by
  simp [localizedRule4bReferencesFromRankedLabels, localizedFirstChiralRankPopulation,
    localizedFirstChiralRankPopulationInLayer, localizedChiralDescriptorsAtRank,
    localizedRule4bReferencesFromPopulation]

/-- The mirrored case: a first ranked-label sphere headed by an uppercase `S` chiral descriptor
fixes the Rule-4b reference population to `[S]`. -/
theorem localizedRule4bReferencesFromRankedLabels_cons_chiral_S
    (tail : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    localizedRule4bReferencesFromRankedLabels
      ([([], some (.chiral RS.S))] :: tail) = [RS.S] := by
  simp [localizedRule4bReferencesFromRankedLabels, localizedFirstChiralRankPopulation,
    localizedFirstChiralRankPopulationInLayer, localizedChiralDescriptorsAtRank,
    localizedRule4bReferencesFromPopulation]

/-! ## 6. The actual central key frame and the decisive comparison over it

`centralKeyFrame` is the genuine compiled frame of the central final occurrence with its actual
returned four-ligand frame, obtained by ordinary classical choice from the generic no-double
existence theorem.  Under the corrected calibration the actual drawn labels at slots `2` and `3`
are `S` and `R` (the historical upstream keys keep their names; their statements are corrected).
The decisive reductions below are stated on that actual frame. -/

/-- The actual returned central four-ligand frame is a valid reroot frame. -/
theorem central_roots_valid :
    ∀ cursor ∈ centralRoots, source.AromaticCanonicalRerootCursorValid cursor :=
  source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid centralTarget centralRoots
    actual_ligand_frames.1

/-- The actual left ligand slot `2` (the corrected `S` daughter occurrence). -/
def centralSlotTwo : Fin 4 := ⟨2, by decide +kernel⟩

/-- The actual right ligand slot `3` (the corrected `R` daughter occurrence). -/
def centralSlotThree : Fin 4 := ⟨3, by decide +kernel⟩

/-- The actual drawing dependency label at the left ligand slot is `S` under the corrected
calibration.  The upstream declaration keeps its historical name
`central_left_dependency_label_R`; that is a stable API key, not a label claim. -/
theorem central_slot_two_label :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
        (centralRootAt centralSlotTwo) = some (.chiral RS.S) :=
  central_left_dependency_label_R

/-- The actual drawing dependency label at the right ligand slot is `R` under the corrected
calibration.  The upstream declaration keeps its historical name
`central_right_dependency_label_S`. -/
theorem central_slot_three_label :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
        (centralRootAt centralSlotThree) = some (.chiral RS.R) :=
  central_right_dependency_label_S

/-- The genuine compiled Rules-3--5 key frame of the central final occurrence. -/
noncomputable def centralKeyFrame :
    source.AromaticCanonicalOccurrenceRule3Through5KeyFrame branchCarrierFuel :=
  Classical.choose
    (SingleWedgeSource.exists_occurrence_production_keyFrame_of_valid_noDouble
      source centralTarget centralView centralRoots central_roots_length central_roots_valid
      source_no_ordinary_double_bond)

theorem centralKeyFrame_computed :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? centralTarget centralView
        (2 * (branchCarrierFuel + 1)) centralRoots = some centralKeyFrame :=
  Classical.choose_spec
    (SingleWedgeSource.exists_occurrence_production_keyFrame_of_valid_noDouble
      source centralTarget centralView centralRoots central_roots_length central_roots_valid
      source_no_ordinary_double_bond)

/-- **Historical mirror reduction.**  When the two identical-carbon ligand occurrences tie under
the complete Rule-3 keys and the compound Rules-4b/4c prior keys, and the compiled common
readings carry the vectors `[2, 1, 0, 1]` / `[2, 1, 0, 0]`, Rule 5 decides the comparison to
`gt` with the enantiomorphic (`pseudo`) signal set.  This statement is the algebraic mirror of
the vector pattern actually realised after the calibration repair; it is retained because it is
a true generic conditional.  The realised pattern is
`central_drawing_rule45_decisive_actual`. -/
theorem central_drawing_rule45_decisive_forward
    (rule3Tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule3
      (centralKeyFrame.keyAt centralSlotThree).rule3 = Ordering.eq)
    (priorTie : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior = Ordering.eq)
    (left right : source.AromaticCanonicalRerootRule5Reading)
    (leftReadings : (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = [left])
    (rightReadings : (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = [right])
    (leftCommonR : ∃ tail, left.commonR.descriptor = [[([], [2, 1, 0, 1])]] ++ tail)
    (rightCommonR : ∃ tail, right.commonR.descriptor = [[([], [2, 1, 0, 0])]] ++ tail)
    (leftCommonS : ∃ tail, left.commonS.descriptor = [[([], [2, 1, 0, 0])]] ++ tail)
    (rightCommonS : ∃ tail, right.commonS.descriptor = [[([], [2, 1, 0, 1])]] ++ tail) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
        centralKeyFrame centralSlotTwo centralSlotThree =
      { ordering := Ordering.gt, pseudo := true } := by
  rw [source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    centralKeyFrame centralSlotTwo centralSlotThree rule3Tie]
  apply compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_gt_lt source
  · exact priorTie
  · rw [leftReadings, rightReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_R_singleton source left right]
    obtain ⟨leftRest, leftEq⟩ := leftCommonR
    obtain ⟨rightRest, rightEq⟩ := rightCommonR
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_gt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 1] [2, 1, 0, 0] leftRest rightRest
      compareLocalizedCumulativeRule45Priority_commonR_decisive
  · rw [leftReadings, rightReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_S_singleton source left right]
    obtain ⟨leftRest, leftEq⟩ := leftCommonS
    obtain ⟨rightRest, rightEq⟩ := rightCommonS
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_lt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 0] [2, 1, 0, 1] leftRest rightRest
      compareLocalizedCumulativeRule45Priority_commonS_decisive

/-- **Historical mirror reduction, reversed slot order.**  The same opposite-vector pattern in
the slot-3/slot-2 order gives `lt` with the enantiomorphic signal. -/
theorem central_drawing_rule45_decisive_reversed
    (rule3TieRev : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotThree).rule3
      (centralKeyFrame.keyAt centralSlotTwo).rule3 = Ordering.eq)
    (priorTieRev : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior = Ordering.eq)
    (left right : source.AromaticCanonicalRerootRule5Reading)
    (leftReadings : (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = [left])
    (rightReadings : (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = [right])
    (leftCommonR : ∃ tail, left.commonR.descriptor = [[([], [2, 1, 0, 1])]] ++ tail)
    (rightCommonR : ∃ tail, right.commonR.descriptor = [[([], [2, 1, 0, 0])]] ++ tail)
    (leftCommonS : ∃ tail, left.commonS.descriptor = [[([], [2, 1, 0, 0])]] ++ tail)
    (rightCommonS : ∃ tail, right.commonS.descriptor = [[([], [2, 1, 0, 1])]] ++ tail) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
        centralKeyFrame centralSlotThree centralSlotTwo =
      { ordering := Ordering.lt, pseudo := true } := by
  rw [source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    centralKeyFrame centralSlotThree centralSlotTwo rule3TieRev]
  apply compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_lt_gt source
  · exact priorTieRev
  · rw [rightReadings, leftReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_R_singleton source right left]
    obtain ⟨leftRest, leftEq⟩ := leftCommonR
    obtain ⟨rightRest, rightEq⟩ := rightCommonR
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_lt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 0] [2, 1, 0, 1] rightRest leftRest
      compareLocalizedCumulativeRule45Priority_commonS_decisive
  · rw [rightReadings, leftReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_S_singleton source right left]
    obtain ⟨leftRest, leftEq⟩ := leftCommonS
    obtain ⟨rightRest, rightEq⟩ := rightCommonS
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_gt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 1] [2, 1, 0, 0] rightRest leftRest
      compareLocalizedCumulativeRule45Priority_commonS_reversed

/-- **Decisive actual forward comparison.**  Under the corrected calibration the slot-2 (`S`)
reading has common vectors `[2, 1, 0, 0]` / `[2, 1, 0, 1]` and the slot-3 (`R`) reading has
`[2, 1, 0, 1]` / `[2, 1, 0, 0]`.  Once the Rule-3 keys and the compound Rules-4b/4c prior keys
tie, Rule 5 decides the slot-2/slot-3 comparison to `lt` with the enantiomorphic signal. -/
theorem central_drawing_rule45_decisive_actual
    (rule3Tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule3
      (centralKeyFrame.keyAt centralSlotThree).rule3 = Ordering.eq)
    (priorTie : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior = Ordering.eq)
    (left right : source.AromaticCanonicalRerootRule5Reading)
    (leftReadings : (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = [left])
    (rightReadings : (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = [right])
    (leftCommonR : ∃ tail, left.commonR.descriptor = [[([], [2, 1, 0, 0])]] ++ tail)
    (rightCommonR : ∃ tail, right.commonR.descriptor = [[([], [2, 1, 0, 1])]] ++ tail)
    (leftCommonS : ∃ tail, left.commonS.descriptor = [[([], [2, 1, 0, 1])]] ++ tail)
    (rightCommonS : ∃ tail, right.commonS.descriptor = [[([], [2, 1, 0, 0])]] ++ tail) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
        centralKeyFrame centralSlotTwo centralSlotThree =
      { ordering := Ordering.lt, pseudo := true } := by
  rw [source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    centralKeyFrame centralSlotTwo centralSlotThree rule3Tie]
  apply compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_lt_gt source
  · exact priorTie
  · rw [leftReadings, rightReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_R_singleton source left right]
    obtain ⟨leftRest, leftEq⟩ := leftCommonR
    obtain ⟨rightRest, rightEq⟩ := rightCommonR
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_lt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 0] [2, 1, 0, 1] leftRest rightRest
      compareLocalizedCumulativeRule45Priority_commonR_reversed
  · rw [leftReadings, rightReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_S_singleton source left right]
    obtain ⟨leftRest, leftEq⟩ := leftCommonS
    obtain ⟨rightRest, rightEq⟩ := rightCommonS
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_gt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 1] [2, 1, 0, 0] leftRest rightRest
      compareLocalizedCumulativeRule45Priority_commonS_reversed

/-- **Decisive actual reversed comparison.**  The same corrected vectors in the slot-3/slot-2
order give `gt` with the enantiomorphic signal. -/
theorem central_drawing_rule45_decisive_actual_reversed
    (rule3TieRev : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotThree).rule3
      (centralKeyFrame.keyAt centralSlotTwo).rule3 = Ordering.eq)
    (priorTieRev : source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior = Ordering.eq)
    (left right : source.AromaticCanonicalRerootRule5Reading)
    (leftReadings : (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings = [left])
    (rightReadings : (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = [right])
    (leftCommonR : ∃ tail, left.commonR.descriptor = [[([], [2, 1, 0, 0])]] ++ tail)
    (rightCommonR : ∃ tail, right.commonR.descriptor = [[([], [2, 1, 0, 1])]] ++ tail)
    (leftCommonS : ∃ tail, left.commonS.descriptor = [[([], [2, 1, 0, 1])]] ++ tail)
    (rightCommonS : ∃ tail, right.commonS.descriptor = [[([], [2, 1, 0, 0])]] ++ tail) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
        centralKeyFrame centralSlotThree centralSlotTwo =
      { ordering := Ordering.gt, pseudo := true } := by
  rw [source.compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    centralKeyFrame centralSlotThree centralSlotTwo rule3TieRev]
  apply compareAromaticCanonicalRerootCompoundThroughRule5_of_priorTie_of_gt_lt source
  · exact priorTieRev
  · rw [rightReadings, leftReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_R_singleton source right left]
    obtain ⟨leftRest, leftEq⟩ := leftCommonR
    obtain ⟨rightRest, rightEq⟩ := rightCommonR
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_gt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 1] [2, 1, 0, 0] rightRest leftRest
      compareLocalizedCumulativeRule45Priority_commonR_decisive
  · rw [rightReadings, leftReadings,
      compareAromaticCanonicalRerootCompoundRule5Readings_S_singleton source right left]
    obtain ⟨leftRest, leftEq⟩ := leftCommonS
    obtain ⟨rightRest, rightEq⟩ := rightCommonS
    rw [leftEq, rightEq]
    exact compareSparseLayers_cons_lt compareLocalizedCumulativeRule45Priority
      [2, 1, 0, 0] [2, 1, 0, 1] rightRest leftRest
      compareLocalizedCumulativeRule45Priority_commonS_decisive

end TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
