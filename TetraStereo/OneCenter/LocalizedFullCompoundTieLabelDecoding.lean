import TetraStereo.OneCenter.LocalizedParametricCompoundRule45Key
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedSparseAddressReconstruction
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree









/-- Every nonempty list is a cons. -/
theorem fullTie_list_exists_cons_of_ne_nil {α : Type*} {list : List α}
    (nonempty : list ≠ []) : ∃ head tail, list = head :: tail := by
  cases list with
  | nil => exact absurd rfl nonempty
  | cons head tail => exact ⟨head, tail, rfl⟩

/-- A successful compound Rules-4b/4c key build exposes its actual Rule-4a build and its actual
reading-list build at the same fuel. -/
theorem fullTie_compoundRule4bcKey_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        .rule4a read fuel cursor = some key.rule4aKey ∧
      input.buildLocalizedRerootRule4bcReadingsWithRead? read fuel cursor
        (localizedRule4bcReferenceAlternatives key.references) = some key.readings := by
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
          read fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [rule4aComputed, readingsComputed] at computed
      | some readings =>
          have keyEq : key =
              { rule4aKey := rule4aKey
                references :=
                  localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
                referenceCountPriority :=
                  constitutionalRule4bReferenceCountPriority
                    (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)
                readings := readings } := by
            simpa [rule4aComputed, readingsComputed] using computed.symm
          rw [keyEq]
          exact ⟨rfl, readingsComputed⟩

/-- A successful Rule-5 reading build exposes the prior alternative and both actual
common-reference builds, at the same fuel. -/
theorem fullTie_rule5Reading_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    reading.prior = prior ∧
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (localizedRule5StageFor prior.reference? .R) read fuel cursor = some reading.commonR ∧
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (localizedRule5StageFor prior.reference? .S) read fuel cursor = some reading.commonS := by
  unfold buildLocalizedRerootRule5ReadingWithRead? at computed
  cases commonRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor prior.reference? .R) read fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      cases commonSComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (localizedRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonRComputed, commonSComputed] at computed
      | some commonS =>
          have readingEq : reading =
              { prior := prior, commonR := commonR, commonS := commonS } := by
            simpa [commonRComputed, commonSComputed] using computed.symm
          rw [readingEq]
          exact ⟨rfl, rfl, rfl⟩

/-- A successful compound through-Rule-5 key build exposes its actual compound Rules-4b/4c build
and its actual Rule-5 reading-list build, at the same fuel. -/
theorem fullTie_compoundRule45Key_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
        read fuel cursor = some key.prior ∧
      input.buildLocalizedRerootRule5ReadingsWithRead? read fuel cursor
        key.prior.readings = some key.rule5Readings := by
  unfold buildLocalizedRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      cases readingsComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          have keyEq : key = { prior := prior, rule5Readings := readings } := by
            simpa [priorComputed, readingsComputed] using computed.symm
          rw [keyEq]
          exact ⟨rfl, readingsComputed⟩

/-- A full actual compound through-Rule-5 comparator tie is exactly the compound Rules-4b/4c tie
and the common-`R` Rule-5 reading-list tie.  No stage, reference or label is assumed. -/
theorem fullTie_rule45Tie_prior_and_readings
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (tie : input.compareLocalizedRerootCompoundRule45Keys left right = Ordering.eq) :
    input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = Ordering.eq ∧
      input.compareLocalizedRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings = Ordering.eq := by
  have decomposed := tie
  simp only [compareLocalizedRerootCompoundRule45Keys, compareLex, Ordering.byKey,
    Ordering.then_eq_eq] at decomposed
  exact ⟨decomposed.1, decomposed.2⟩

/-- **Four-case injectivity of the actual cumulative priority vector.**  For a fixed common Rule-5
reference and any pair of own Rule-4b references (`none` or `some`), equality of the actual
Rule-4a--5 priority vectors forces equality of the sparse labels.  The mixed cases are impossible
because the `rule5NoRule4bReference` vector has length three while the `rule5` vector has length
four.  No sparsity hypothesis is used. -/
theorem fullTie_priority_injective
    (ownLeft ownRight : Option RS) (commonReference : RS)
    (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority
        (localizedRule5StageFor ownLeft commonReference) left =
      localizedCumulativeRule45Priority
        (localizedRule5StageFor ownRight commonReference) right) :
    left = right := by
  cases ownLeft with
  | none =>
      cases ownRight with
      | none =>
          exact localizedCumulativeRule45Priority_rule5NoRule4bReference_injective
            commonReference left right same
      | some _ =>
          exact absurd same (by
            intro hypothesis
            have lengthEq := congrArg List.length hypothesis
            simp [localizedRule5StageFor, localizedCumulativeRule45Priority] at lengthEq)
  | some leftReference =>
      cases ownRight with
      | none =>
          exact absurd same (by
            intro hypothesis
            have lengthEq := congrArg List.length hypothesis
            simp [localizedRule5StageFor, localizedCumulativeRule45Priority] at lengthEq)
      | some rightReference =>
          exact localizedCumulativeRule45Priority_rule5_commonReference_injective
            leftReference rightReference commonReference left right same

/-- The paired head readings of a tied nonempty common-reference reading list carry equal
common-reference descriptors. -/
theorem fullTie_compareRule5Readings_cons_cons_eq
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (headLeft headRight : input.LocalizedRerootRule5Reading)
    (tailLeft tailRight : List input.LocalizedRerootRule5Reading)
    (same : input.compareLocalizedRerootCompoundRule5Readings commonReference
      (headLeft :: tailLeft) (headRight :: tailRight) = Ordering.eq) :
    input.localizedRerootRule5Descriptor commonReference headLeft =
      input.localizedRerootRule5Descriptor commonReference headRight :=
  (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp
    (by
      have headTie := same
      simp only [compareLocalizedRerootCompoundRule5Readings, List.compareLex_cons_cons,
        Ordering.byKey, Ordering.then_eq_eq] at headTie
      exact headTie.1)

















































































/-! ## Length preservation of the actual sequential reading builders -/

/-- Every successful actual per-reference Rule-4b/4c reading-list compilation preserves the length
of the normative alternative list.  The builder emits exactly one reading per alternative. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_length_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (alternatives : List (Option RS))
      (readings : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule4bcReadingsWithRead?
        read fuel cursor alternatives = some readings →
      readings.length = alternatives.length := by
  intro alternatives
  induction alternatives with
  | nil =>
      intro readings computed
      simp [buildLocalizedRerootRule4bcReadingsWithRead?] at computed
      subst readings
      rfl
  | cons alternative rest inductionHypothesis =>
      intro readings computed
      unfold buildLocalizedRerootRule4bcReadingsWithRead? at computed
      cases headComputed : input.buildLocalizedRerootRule4bcReadingWithRead?
          read fuel cursor alternative with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
              read fuel cursor rest with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              simp [inductionHypothesis tail tailComputed]

/-- Every successful actual Rule-5 reading-list compilation preserves the length of the prior
reading list.  The builder emits exactly one reading per prior alternative. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_length_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (priors : List input.LocalizedRerootRule4bcReading)
      (readings : List input.LocalizedRerootRule5Reading),
      input.buildLocalizedRerootRule5ReadingsWithRead?
        read fuel cursor priors = some readings →
      readings.length = priors.length := by
  intro priors
  induction priors with
  | nil =>
      intro readings computed
      simp [buildLocalizedRerootRule5ReadingsWithRead?] at computed
      subst readings
      rfl
  | cons prior rest inductionHypothesis =>
      intro readings computed
      unfold buildLocalizedRerootRule5ReadingsWithRead? at computed
      cases headComputed : input.buildLocalizedRerootRule5ReadingWithRead?
          read fuel cursor prior with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
              read fuel cursor rest with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              simp [inductionHypothesis tail tailComputed]

/-! ## Nonemptiness of the actual Rule-4b/4c and Rule-5 reading lists -/

/-- Every successful actual compound Rules-4b/4c build has a nonempty prior reading list.  The
normative alternative list is `[none]` when no uppercase reference exists and the `some` image of a
nonempty list otherwise, and the sequential builder emits one reading per alternative. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_readings_ne_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    key.readings ≠ [] := by
  obtain ⟨-, readingsComputed⟩ :=
    fullTie_compoundRule4bcKey_components input read fuel cursor key computed
  have lengthEq :=
    buildLocalizedRerootRule4bcReadingsWithRead?_length_eq input read fuel cursor
      (localizedRule4bcReferenceAlternatives key.references) key.readings readingsComputed
  have positive : 0 < (localizedRule4bcReferenceAlternatives key.references).length :=
    referenceAlternatives_length_pos key.references
  intro empty
  have zeroLength : key.readings.length = 0 := by simp [empty]
  rw [lengthEq] at zeroLength
  omega

/-- Every successful actual compound through-Rule-5 build has a nonempty Rule-5 reading list.  The
prior reading list is nonempty, and the Rule-5 builder emits one reading per prior alternative, so
no nonemptiness hypothesis is needed anywhere downstream. -/
theorem buildLocalizedRerootCompoundRule45KeyWithRead?_rule5Readings_ne_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule45Key)
    (computed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    key.rule5Readings ≠ [] := by
  obtain ⟨priorComputed, readingsComputed⟩ :=
    fullTie_compoundRule45Key_components input read fuel cursor key computed
  have priorNonempty : key.prior.readings ≠ [] :=
    buildLocalizedRerootCompoundRule4bcKeyWithRead?_readings_ne_nil input read fuel cursor
      key.prior priorComputed
  have lengthEq :=
    buildLocalizedRerootRule5ReadingsWithRead?_length_eq input read fuel cursor
      key.prior.readings key.rule5Readings readingsComputed
  have positive : 0 < key.prior.readings.length := List.length_pos_iff.mpr priorNonempty
  intro empty
  have zeroLength : key.rule5Readings.length = 0 := by simp [empty]
  rw [lengthEq] at zeroLength
  omega

/-! ## Exposing the head reading and its common-`R` build -/

/-- A successful actual Rule-5 reading-list build over a nonempty prior list exposes its head
reading, the actual per-reading build, the recorded prior alternative, and the actual common-`R`
cumulative build at the stage selected by that prior alternative's own Rule-4b reference.  This
generalises the existing singleton extraction to arbitrary nonempty prior lists; nothing about the
desired head, its common-`R` key or the reference selection is assumed. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_cons_exposes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (priors : List input.LocalizedRerootRule4bcReading)
    (readings : List input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5ReadingsWithRead?
      read fuel cursor (prior :: priors) = some readings) :
    ∃ head tail,
      readings = head :: tail ∧
        input.buildLocalizedRerootRule5ReadingWithRead? read fuel cursor prior = some head ∧
          head.prior = prior ∧
            input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                (localizedRule5StageFor prior.reference? .R) read fuel cursor =
              some head.commonR := by
  unfold buildLocalizedRerootRule5ReadingsWithRead? at computed
  cases headComputed : input.buildLocalizedRerootRule5ReadingWithRead?
      read fuel cursor prior with
  | none => simp [headComputed] at computed
  | some head =>
      cases tailComputed : input.buildLocalizedRerootRule5ReadingsWithRead?
          read fuel cursor priors with
      | none => simp [headComputed, tailComputed] at computed
      | some tail =>
          have readingsEq : readings = head :: tail := by
            simpa [headComputed, tailComputed] using computed.symm
          obtain ⟨priorEq, commonRBuilt, -⟩ :=
            fullTie_rule5Reading_components input read fuel cursor
              prior head headComputed
          exact ⟨head, tail, readingsEq, rfl, priorEq, commonRBuilt⟩

/-! ## Same-cursor constitutional coherence of arbitrary actual `WithRead` builds -/

/-- Two successful actual cumulative builds at one cursor have equal constitutional observables,
whatever their descriptor stages, label readers or recursion budgets.  The constitutional component
is exactly the label-independent rule-major derivation of the cursor, so it cannot depend on the
Rule-4a--5 stage or on the reader. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_observable_equal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    {leftStage rightStage : LocalizedCumulativeRule45Stage}
    {leftRead rightRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      leftStage leftRead leftFuel cursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      rightStage rightRead rightFuel cursor = some rightKey) :
    constitutionalObservable leftKey.constitutional =
      constitutionalObservable rightKey.constitutional :=
  input.declarative_constitutional_observable_unique leftFuel rightFuel cursor
    leftKey.constitutional rightKey.constitutional
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      leftStage leftRead leftFuel cursor leftKey leftComputed)
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      rightStage rightRead rightFuel cursor rightKey rightComputed)

/-- **Transport of the Rule-4a constitutional columns to the actual common-`R` pair.**  On each
side, the actual common-`R` key and the actual Rule-4a key are successful cumulative builds at the
same cursor; same-cursor coherence identifies their constitutional observables.  An equality of the
three constitutional columns of the two Rule-4a keys therefore transports to the two common-`R`
keys.  The two cursors, readers, budgets and own Rule-4b references are all independent. -/
theorem actual_commonR_pair_constitutional_columns
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftRead rightRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    (ownLeft ownRight : Option RS)
    (leftCommon rightCommon : input.LocalizedRerootCumulativeRule45Key)
    (leftRule4a rightRule4a : input.LocalizedRerootCumulativeRule45Key)
    (leftCommonBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor ownLeft .R) leftRead leftFuel leftCursor = some leftCommon)
    (leftRule4aBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a leftRead leftFuel leftCursor = some leftRule4a)
    (rightCommonBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (localizedRule5StageFor ownRight .R) rightRead rightFuel rightCursor = some rightCommon)
    (rightRule4aBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a rightRead rightFuel rightCursor = some rightRule4a)
    (rule4aColumns :
      leftRule4a.constitutional.rule1a = rightRule4a.constitutional.rule1a ∧
        leftRule4a.constitutional.rule1b = rightRule4a.constitutional.rule1b ∧
          leftRule4a.constitutional.rule2 = rightRule4a.constitutional.rule2) :
    leftCommon.constitutional.rule1a = rightCommon.constitutional.rule1a ∧
      leftCommon.constitutional.rule1b = rightCommon.constitutional.rule1b ∧
        leftCommon.constitutional.rule2 = rightCommon.constitutional.rule2 := by
  have leftObservable :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_observable_equal
      input leftCursor leftCommonBuilt leftRule4aBuilt
  have rightObservable :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_observable_equal
      input rightCursor rightCommonBuilt rightRule4aBuilt
  have rule4aObservable : constitutionalObservable leftRule4a.constitutional =
      constitutionalObservable rightRule4a.constitutional := by
    obtain ⟨rule1aEq, rule1bEq, rule2Eq⟩ := rule4aColumns
    simp only [constitutionalObservable, rule1aEq, rule1bEq, rule2Eq]
  have commonObservable : constitutionalObservable leftCommon.constitutional =
      constitutionalObservable rightCommon.constitutional :=
    leftObservable.trans (rule4aObservable.trans rightObservable.symm)
  exact ⟨congrArg LocalizedConstitutionalObservable.rule1a commonObservable,
    congrArg LocalizedConstitutionalObservable.rule1b commonObservable,
    congrArg LocalizedConstitutionalObservable.rule2 commonObservable⟩

/-! ## Observation equality determines the exact-label table -/

/-- **Equal decorated observations determine the exact optional-label table.**  The observation
retains the reader label at every node and the sorted child list; descending the common child
structure by index therefore reconstructs the whole addressed label table.  No shape hypothesis
and no source-cursor equality is used. -/
theorem labelTable_eq_of_observation_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (same : observation t1 = observation t2) :
    t1.labelTable = t2.labelTable := by
  have main : ∀ n : Nat, ∀ candidate1 : LocalizedCumulativeDecoratedTree input carrierFuel,
      height candidate1 ≤ n →
        ∀ candidate2 : LocalizedCumulativeDecoratedTree input carrierFuel,
          observation candidate1 = observation candidate2 →
            candidate1.labelTable = candidate2.labelTable := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate1 bound candidate2 same
    cases candidate1 with
    | mk source1 atomic1 dist1 mass1 label1 children1 =>
      cases candidate2 with
      | mk source2 atomic2 dist2 mass2 label2 children2 =>
        have labelEq : label1 = label2 := by
          have labelSame := congrArg (fun obs => obs.decoration.label) same
          simpa only [table_observation_mk] using labelSame
        have childrenSameMap : children1.map observation = children2.map observation := by
          have childrenSame := congrArg (fun obs => obs.children) same
          simpa only [table_observation_mk, table_observationList_eq_map] using childrenSame
        have childCount : children1.length = children2.length := by
          simpa using congrArg List.length childrenSameMap
        have childTable : ∀ (index : Nat) (firstBound : index < children1.length)
            (secondBound : index < children2.length),
            table (fun node => node.label) (children1[index]'firstBound) =
              table (fun node => node.label) (children2[index]'secondBound) := by
          intro index firstBound secondBound
          have observationAt : observation (children1[index]'firstBound) =
              observation (children2[index]'secondBound) := by
            have atIndex : (children1.map observation)[index]? =
                (children2.map observation)[index]? :=
              congrArg (fun list => list[index]?) childrenSameMap
            rw [List.getElem?_map, List.getElem?_map,
              List.getElem?_eq_getElem firstBound,
              List.getElem?_eq_getElem secondBound] at atIndex
            simpa using atIndex
          have smaller : height (children1[index]'firstBound) <
              height ⟨source1, atomic1, dist1, mass1, label1, children1⟩ :=
            height_lt_height_of_mem ⟨source1, atomic1, dist1, mass1, label1, children1⟩
              (List.mem_of_getElem? (List.getElem?_eq_getElem firstBound))
          have bounded : height (children1[index]'firstBound) < k := by omega
          have applied := inductionHypothesis (height (children1[index]'firstBound)) bounded
            (children1[index]'firstBound) (le_refl _) (children2[index]'secondBound) observationAt
          simpa only [labelTable_eq_table] using applied
        have childTables : children1.map (table (fun node => node.label)) =
            children2.map (table (fun node => node.label)) := by
          apply List.ext_getElem (by simpa using childCount)
          intro index inFirst inSecond
          rw [List.getElem_map, List.getElem_map]
          exact childTable index (by simpa using inFirst) (by simpa using inSecond)
        have rootTable : ∀ (source : input.LocalizedRerootCursor carrierFuel)
            (atomicNumber rule1bDistance isotopeMass : Nat)
            (label : Option LocalizedAuxiliaryLabel)
            (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)),
            table (fun node => node.label)
                ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =
              [[([], label)]] ++ mergeLocalizedTreeChildTables
                (children.map (table (fun node => node.label))) := by
          intro source atomicNumber rule1bDistance isotopeMass label children
          rw [table_eq_root_merge]
        simp only [labelTable_eq_table, rootTable, labelEq, childTables]
  exact main (height t1) t1 (le_refl _) t2 same

/-! ## The central full-tie same-reader-label theorem -/

/-- **Full actual compound Rule-5 tie: the two common-`R` readings carry the same labels at every
shared actual position.**

From two actual successful parametric compound through-Rule-5 builds at actual cursors and a full
actual comparator tie, the paired head Rule-5 reading exists with its actual common-`R` cumulative
build on each side.  Those builds yield actually realised decorated trees whose sources are the
original cursors, whose erased shapes agree, whose exact-label tables and decorated observations
are equal, and whose reader values agree at every position paired by the equal-shape position
equivalence.

No nonemptiness, singleton, unique-nearest-reference, supplied-reference, sparse-reader,
desired-alignment, coverage, physical-isomorphism or label-covariance premise is used.  The only
label fact consumed is the unconditional scalar injectivity
`fullTie_priority_injective`, so arbitrary optional labels (including
pseudoasymmetric ones) and arbitrary pairs of own Rule-4b references are covered. -/
theorem actual_full_compoundRule45_tie_same_reader_labels
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftRead rightRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      leftRead leftFuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      rightRead rightFuel rightCursor = some rightKey)
    (tie : input.compareLocalizedRerootCompoundRule45Keys leftKey rightKey = Ordering.eq) :
    ∃ (tL tR : LocalizedCumulativeDecoratedTree input carrierFuel)
      (hshape : shape tL = shape tR),
      tL.source = leftCursor ∧
        tR.source = rightCursor ∧
          LocalizedCumulativeTreeRealizes input leftRead tL ∧
            LocalizedCumulativeTreeRealizes input rightRead tR ∧
              tL.labelTable = tR.labelTable ∧
                observation tL = observation tR ∧
                  ∀ p : Position tL,
                    leftRead (positionSource p) =
                      rightRead (positionSource (shapePositionEquiv hshape p)) := by
  -- The full tie splits into the compound Rule-4b/4c tie and the common-`R` reading-list tie.
  obtain ⟨priorTie, readingsTie⟩ :=
    fullTie_rule45Tie_prior_and_readings input leftKey rightKey tie
  have rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey = Ordering.eq :=
    ((input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mp priorTie).1
  obtain ⟨rule4aRule1a, rule4aRule1b, rule4aRule2⟩ :=
    cumulativeRule45Tie_constitutional_columns input
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey rule4aTie
  -- Expose the actual sub-builds of both compound keys.
  obtain ⟨leftPriorComputed, leftRule5ReadingsComputed⟩ :=
    fullTie_compoundRule45Key_components input leftRead leftFuel
      leftCursor leftKey leftComputed
  obtain ⟨rightPriorComputed, rightRule5ReadingsComputed⟩ :=
    fullTie_compoundRule45Key_components input rightRead rightFuel
      rightCursor rightKey rightComputed
  obtain ⟨leftRule4aComputed, -⟩ :=
    fullTie_compoundRule4bcKey_components input leftRead leftFuel
      leftCursor leftKey.prior leftPriorComputed
  obtain ⟨rightRule4aComputed, -⟩ :=
    fullTie_compoundRule4bcKey_components input rightRead rightFuel
      rightCursor rightKey.prior rightPriorComputed
  -- The prior reading lists are nonempty; expose their heads.
  have leftPriorNonempty : leftKey.prior.readings ≠ [] :=
    buildLocalizedRerootCompoundRule4bcKeyWithRead?_readings_ne_nil input leftRead leftFuel
      leftCursor leftKey.prior leftPriorComputed
  have rightPriorNonempty : rightKey.prior.readings ≠ [] :=
    buildLocalizedRerootCompoundRule4bcKeyWithRead?_readings_ne_nil input rightRead rightFuel
      rightCursor rightKey.prior rightPriorComputed
  obtain ⟨priorLeft, priorsLeft, leftPriorsEq⟩ :=
    fullTie_list_exists_cons_of_ne_nil leftPriorNonempty
  obtain ⟨priorRight, priorsRight, rightPriorsEq⟩ :=
    fullTie_list_exists_cons_of_ne_nil rightPriorNonempty
  rw [leftPriorsEq] at leftRule5ReadingsComputed
  rw [rightPriorsEq] at rightRule5ReadingsComputed
  -- Expose the paired head readings and their actual common-`R` builds.
  obtain ⟨headLeft, tailLeft, leftReadingsEq, -, -, leftCommonRBuilt⟩ :=
    buildLocalizedRerootRule5ReadingsWithRead?_cons_exposes input leftRead leftFuel leftCursor
      priorLeft priorsLeft leftKey.rule5Readings leftRule5ReadingsComputed
  obtain ⟨headRight, tailRight, rightReadingsEq, -, -, rightCommonRBuilt⟩ :=
    buildLocalizedRerootRule5ReadingsWithRead?_cons_exposes input rightRead rightFuel rightCursor
      priorRight priorsRight rightKey.rule5Readings rightRule5ReadingsComputed

  have readingsTieCons : input.compareLocalizedRerootCompoundRule5Readings .R
      (headLeft :: tailLeft) (headRight :: tailRight) = Ordering.eq := by
    simpa only [leftReadingsEq, rightReadingsEq] using readingsTie
  have descriptorTie :=
    fullTie_compareRule5Readings_cons_cons_eq input .R
      headLeft headRight tailLeft tailRight readingsTieCons
  have descriptorEq : headLeft.commonR.descriptor = headRight.commonR.descriptor := by
    simpa only [localizedRerootRule5Descriptor] using descriptorTie

  obtain ⟨tL, tLSource, fullMatchL, realizesL, -⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input
      (localizedRule5StageFor priorLeft.reference? .R) leftRead leftFuel leftCursor
      headLeft.commonR leftCommonRBuilt
  obtain ⟨tR, tRSource, fullMatchR, realizesR, -⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input
      (localizedRule5StageFor priorRight.reference? .R) rightRead rightFuel rightCursor
      headRight.commonR rightCommonRBuilt
  -- Transport the Rule-4a columns to the actual common-`R` pair.
  obtain ⟨commonRule1a, commonRule1b, commonRule2⟩ :=
    actual_commonR_pair_constitutional_columns input leftRead rightRead
      leftCursor rightCursor priorLeft.reference? priorRight.reference?
      headLeft.commonR headRight.commonR
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey
      leftCommonRBuilt leftRule4aComputed rightCommonRBuilt rightRule4aComputed
      ⟨rule4aRule1a, rule4aRule1b, rule4aRule2⟩
  -- The three constitutional columns of the two realised trees agree.
  have hRule1a : (tables (localizedRule5StageFor priorLeft.reference? .R) tL).rule1a =
      (tables (localizedRule5StageFor priorRight.reference? .R) tR).rule1a :=
    fullMatchL.tableMatch.1.trans (commonRule1a.trans fullMatchR.tableMatch.1.symm)
  have hRule1b : (tables (localizedRule5StageFor priorLeft.reference? .R) tL).rule1b =
      (tables (localizedRule5StageFor priorRight.reference? .R) tR).rule1b :=
    fullMatchL.tableMatch.2.1.trans (commonRule1b.trans fullMatchR.tableMatch.2.1.symm)
  have hRule2 : (tables (localizedRule5StageFor priorLeft.reference? .R) tL).rule2 =
      (tables (localizedRule5StageFor priorRight.reference? .R) tR).rule2 :=
    fullMatchL.tableMatch.2.2.1.trans (commonRule2.trans fullMatchR.tableMatch.2.2.1.symm)
  have hDescriptor :
      (tables (localizedRule5StageFor priorLeft.reference? .R) tL).descriptor =
        (tables (localizedRule5StageFor priorRight.reference? .R) tR).descriptor :=
    fullMatchL.tableMatch.2.2.2.trans (descriptorEq.trans fullMatchR.tableMatch.2.2.2.symm)

  have hshape : shape tL = shape tR :=
    table_shape_eq_of_columns_eq (localizedRule5StageFor priorLeft.reference? .R)
      (localizedRule5StageFor priorRight.reference? .R) tL tR hRule1a hRule1b hRule2

  have observationEq : observation tL = observation tR :=
    table_observation_eq_of_tables_eq
      (fun label => localizedCumulativeRule45Priority
        (localizedRule5StageFor priorLeft.reference? .R) label)
      (fun label => localizedCumulativeRule45Priority
        (localizedRule5StageFor priorRight.reference? .R) label)
      (fun left right same =>
        fullTie_priority_injective priorLeft.reference?
          priorRight.reference? .R left right same)
      tL tR
      (by simpa only [tables_rule1a] using hRule1a)
      (by simpa only [tables_rule1b] using hRule1b)
      (by simpa only [tables_rule2] using hRule2)
      (by simpa only [tables_descriptor] using hDescriptor)
  -- Exact-label tables agree, because the observation retains every reader label.
  have labelTableEq : tL.labelTable = tR.labelTable :=
    labelTable_eq_of_observation_eq tL tR observationEq
  refine ⟨tL, tR, hshape, tLSource, tRSource, realizesL, realizesR, labelTableEq,
    observationEq, ?_⟩
  intro p
  -- Observation equality gives label equality at every shared raw slot address.
  have nodeLabelEq : (positionNode (shapePositionEquiv hshape p)).label =
      (positionNode p).label := by
    have leftLookup : subtreeAt? tL p.val = some (positionNode p) := positionNode_spec p
    have rightLookup : subtreeAt? tR (shapePositionEquiv hshape p).val =
        some (positionNode (shapePositionEquiv hshape p)) :=
      positionNode_spec (shapePositionEquiv hshape p)
    rw [shapePositionEquiv_val hshape p] at rightLookup
    exact subtreeAt?_label_eq_of_observation_eq p.val tL tR observationEq
      (positionNode p) (positionNode (shapePositionEquiv hshape p)) leftLookup rightLookup
  -- Node labels are the reader values at the node sources.
  calc leftRead (positionSource p)
      = (positionNode p).label := (positionNode_label_eq_read realizesL p).symm
    _ = (positionNode (shapePositionEquiv hshape p)).label := nodeLabelEq.symm
    _ = rightRead (positionSource (shapePositionEquiv hshape p)) :=
        positionNode_label_eq_read realizesR (shapePositionEquiv hshape p)

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.fullTie_list_exists_cons_of_ne_nil
assert_kernel_only TetraStereo.OneCenter.fullTie_compoundRule4bcKey_components
assert_kernel_only TetraStereo.OneCenter.fullTie_rule5Reading_components
assert_kernel_only TetraStereo.OneCenter.fullTie_compoundRule45Key_components
assert_kernel_only TetraStereo.OneCenter.fullTie_rule45Tie_prior_and_readings
assert_kernel_only TetraStereo.OneCenter.fullTie_priority_injective
assert_kernel_only TetraStereo.OneCenter.fullTie_compareRule5Readings_cons_cons_eq
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule4bcReadingsWithRead?_length_eq
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule5ReadingsWithRead?_length_eq
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKeyWithRead?_readings_ne_nil
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule45KeyWithRead?_rule5Readings_ne_nil
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootRule5ReadingsWithRead?_cons_exposes
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_observable_equal
assert_kernel_only TetraStereo.OneCenter.actual_commonR_pair_constitutional_columns
assert_kernel_only TetraStereo.OneCenter.labelTable_eq_of_observation_eq
assert_kernel_only TetraStereo.OneCenter.actual_full_compoundRule45_tie_same_reader_labels
