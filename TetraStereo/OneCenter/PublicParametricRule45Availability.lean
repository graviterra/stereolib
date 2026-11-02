import TetraStereo.OneCenter.PublicParametricCompoundRule45Key
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceFuelCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput






















































/-! ## Generic executable child lists -/

/-- A list of cursors whose members all compile successfully has a successful `List.mapM` of
actual keys.  This is the executable child-list induction used by the totality proofs; it assumes
nothing about any already-computed key list. -/
private theorem exists_mapM_buildWithRead?_of_forall
    (source : AuthoritativeChemicalInput) {carrierFuel evaluationFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          stage read evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          stage read evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_buildWithRead?_of_forall stage read cursors
          (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-! ## Cumulative Rules-4a--5 keys under an arbitrary reader -/

/-- Evaluation of the actual arbitrary-reader cumulative builder succeeds whenever its structural
fuel covers the strictly decreasing cursor budget.  The reader is total and may return `none` at
any cursor: structural truncation is impossible under the bound, and no label availability
hypothesis is used. -/
theorem exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_of_budget_le
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ evaluationFuel (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.AromaticCanonicalRerootCursorValid cursor →
      source.aromaticCanonicalRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenComputed : source.aromaticCanonicalRerootChildren? cursor =
          some children := rfl
      have childrenDerived := source.aromaticCanonicalRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := read cursor
        refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildAromaticCanonicalCumulativeRule45KeyWithRead?,
          childrenComputed, empty, label]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := source.aromaticCanonicalRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenComputed : source.aromaticCanonicalRerootChildren? cursor =
          some children := rfl
      have childrenDerived := source.aromaticCanonicalRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := read cursor
        refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildAromaticCanonicalCumulativeRule45KeyWithRead?,
          childrenComputed, empty, label]
      · have childComplete : ∀ child ∈ children, ∃ key,
            source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              stage read evaluationFuel child = some key := by
          intro child present
          have childValid := source.aromaticCanonicalRerootChild_valid
            cursor child children childrenDerived present
          have decreases := source.aromaticCanonicalRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_of_budget_le
            stage read evaluationFuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          source.exists_mapM_buildWithRead?_of_forall
            stage read children childComplete
        let label := read cursor
        let compare := source.compareAromaticCanonicalCumulativeRule45Keys
        let sorted := sortAromaticCanonicalCumulativeRule45Keys compare childKeys
        refine ⟨
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
              mergeAromaticCanonicalDescriptorChildren sorted
            labels := [[([], label)]] ++ mergeAromaticCanonicalLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              mergeAromaticCanonicalRankedLabelChildren compare sorted }, ?_⟩
        simp [buildAromaticCanonicalCumulativeRule45KeyWithRead?,
          childrenComputed, empty, childKeysComputed, label, compare, sorted]

/-- The actual arbitrary-reader cumulative builder is total at the structural bound
`2 * (carrierFuel + 1)` for every path-valid cursor.  This is the exact bound used by the
restricted production evaluator, proved here for the parametric recursion. -/
theorem exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage read (2 * (carrierFuel + 1)) cursor = some key := by
  apply source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_of_budget_le
    stage read (2 * (carrierFuel + 1)) cursor valid
  exact source.aromaticCanonicalRerootCursorBudget_le_twice cursor

/-! ## Compound Rules-4b/4c layers under the same arbitrary reader -/

/-- Every one-reference Rule-4b/4c reading of the actual parametric compound compiler succeeds at
the same structural bound, for either the no-reference alternative or any `some reference`
alternative.  Both cumulative stages are the actual arbitrary-reader builders. -/
theorem exists_buildAromaticCanonicalRerootRule4bcReadingWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (reference : Option RS) :
    ∃ reading, source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read (2 * (carrierFuel + 1)) cursor reference = some reading := by
  cases reference with
  | none =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
          .rule4a read cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
          .rule4cNoReference read cursor valid
      exact ⟨
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
          rule4bComputed, rule4cComputed]⟩
  | some reference =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
          (.rule4b reference) read cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
          (.rule4c reference) read cursor valid
      exact ⟨
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
          rule4bComputed, rule4cComputed]⟩

/-- Every finite normative Rule-4b/4c alternative list succeeds at the same bound under the
arbitrary reader, in the production order (`none` or one reading per selected reference). -/
theorem exists_buildAromaticCanonicalRerootRule4bcReadingsWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∀ references : List (Option RS),
      ∃ readings, source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read (2 * (carrierFuel + 1)) cursor references = some readings
  | [] => ⟨[], rfl⟩
  | reference :: references => by
      obtain ⟨reading, readingComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule4bcReadingWithRead?_at_twice
          read cursor valid reference
      obtain ⟨readings, readingsComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule4bcReadingsWithRead?_at_twice
          read cursor valid references
      exact ⟨reading :: readings,
        by simp [buildAromaticCanonicalRerootRule4bcReadingsWithRead?,
          readingComputed, readingsComputed]⟩

/-- The complete no/one/two-reference parametric compound Rules-4b/4c key is total at the same
bound: the Rule-4a key is compiled by the actual arbitrary-reader cumulative builder, the reference
selection is derived from its real ranked labels, and the sequential readings are compiled under
that selection. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨rule4aKey, rule4aComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      .rule4a read cursor valid
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := aromaticCanonicalRule4bcReferenceAlternatives references
  obtain ⟨readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule4bcReadingsWithRead?_at_twice
      read cursor valid alternatives
  exact ⟨
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings },
    by simp [buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?,
      rule4aComputed, references, alternatives, readingsComputed]⟩

/-! ## Compound Rule-5 layers under the same arbitrary reader -/

/-- Both common-reference Rule-5 readings (`commonR` and `commonS`) of the actual parametric
compiler succeed at the same bound, at the stages actually selected by
`aromaticCanonicalRule5StageFor` for the prior alternative. -/
theorem exists_buildAromaticCanonicalRerootRule5ReadingWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (prior : source.AromaticCanonicalRerootRule4bcReading) :
    ∃ reading, source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read (2 * (carrierFuel + 1)) cursor prior = some reading := by
  obtain ⟨commonR, commonRComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      (aromaticCanonicalRule5StageFor prior.reference? .R) read cursor valid
  obtain ⟨commonS, commonSComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      (aromaticCanonicalRule5StageFor prior.reference? .S) read cursor valid
  exact ⟨{ prior := prior, commonR := commonR, commonS := commonS },
    by simp [buildAromaticCanonicalRerootRule5ReadingWithRead?,
      commonRComputed, commonSComputed]⟩

/-- Every finite normative Rule-5 reading list succeeds at the same bound under the arbitrary
reader, preserving the sequential production order. -/
theorem exists_buildAromaticCanonicalRerootRule5ReadingsWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∀ priors : List source.AromaticCanonicalRerootRule4bcReading,
      ∃ readings, source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        read (2 * (carrierFuel + 1)) cursor priors = some readings
  | [] => ⟨[], rfl⟩
  | prior :: priors => by
      obtain ⟨reading, readingComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule5ReadingWithRead?_at_twice
          read cursor valid prior
      obtain ⟨readings, readingsComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule5ReadingsWithRead?_at_twice
          read cursor valid priors
      exact ⟨reading :: readings,
        by simp [buildAromaticCanonicalRerootRule5ReadingsWithRead?,
          readingComputed, readingsComputed]⟩

/-- **Complete parametric compound key availability.**  The actual through-Rule-5 compound
builder under an arbitrary total reader succeeds at the structural bound
`2 * (carrierFuel + 1)` for every path-valid cursor.  Both the complete Rules-4b/4c key (with its
no/one/two-reference alternatives) and every common-R/common-S Rule-5 reading are retained
exactly. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨prior, priorComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      read cursor valid
  obtain ⟨readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule5ReadingsWithRead?_at_twice
      read cursor valid prior.readings
  exact ⟨{ prior := prior, rule5Readings := readings }, by
    simp [buildAromaticCanonicalRerootCompoundRule45KeyWithRead?,
      priorComputed, readingsComputed]⟩

/-! ## Exact full-key fuel stability for the arbitrary reader -/

/-- A pointwise success refinement of `Option`-valued functions lifts through `List.mapM` with the
*same* result list. -/
private theorem list_mapM_of_pointwise_successor {α β : Type*}
    {first second : α → Option β}
    (step : ∀ value result, first value = some result → second value = some result) :
    ∀ values : List α, ∀ results : List β,
      values.mapM first = some results → values.mapM second = some results
  | [], results, computed => by
      simp at computed
      subst results
      rfl
  | value :: values, results, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : first value with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : values.mapM first with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst results
              simp [List.mapM_cons, step value head headComputed,
                list_mapM_of_pointwise_successor step values tail tailComputed]

/-- The definitional one-step unfolding of the cumulative builder at a successor fuel, with the
recursive child calls explicitly kept at the predecessor fuel.  This is a `rfl` equation; it is
used to rewrite the goal without letting the simplifier unfold the recursive call under the child
`List.mapM`. -/
private theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_step
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read (fuel + 1) cursor =
      (do
        let children ← source.aromaticCanonicalRerootChildren? cursor
        let label := read cursor
        if children = [] then
          some
            { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node true
              descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
              labels := [[([], label)]]
              rankedLabels := [[([], label)]] }
        else
          let childKeys ← children.mapM
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              stage read fuel)
          let compare := source.compareAromaticCanonicalCumulativeRule45Keys
          let sorted := sortAromaticCanonicalCumulativeRule45Keys compare childKeys
          some
            { constitutional := ExactOfficialRuleMajorKey.assemble
                (MoleculeGraph.exactOfficialRuleMajorRootKey
                  cursor.occurrence.1.node false)
                (sorted.map fun child => child.constitutional)
              descriptor :=
                [[([], localizedCumulativeRule45Priority stage label)]] ++
                  mergeAromaticCanonicalDescriptorChildren sorted
              labels := [[([], label)]] ++ mergeAromaticCanonicalLabelChildren sorted
              rankedLabels := [[([], label)]] ++
                mergeAromaticCanonicalRankedLabelChildren compare sorted }) := rfl

/-- **One-step exact stability of the cumulative builder.**  A successful arbitrary-reader
cumulative key at a structural fuel is produced, with the *identical* key, one fuel step later.
The proof is the actual structural recursion on fuel and the actual child `List.mapM`; no label
hypothesis and no assumed key equality is used. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalCumulativeRule45Key),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel cursor = some key →
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read (fuel + 1) cursor = some key
  | 0, cursor, key, computed => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenComputed : source.aromaticCanonicalRerootChildren? cursor =
          some children := rfl
      by_cases terminal : children = []
      · simp [buildAromaticCanonicalCumulativeRule45KeyWithRead?,
          childrenComputed, terminal] at computed ⊢
        exact computed
      · simp [buildAromaticCanonicalCumulativeRule45KeyWithRead?,
          childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenComputed : source.aromaticCanonicalRerootChildren? cursor =
          some children := rfl
      by_cases terminal : children = []
      · simp [buildAromaticCanonicalCumulativeRule45KeyWithRead?,
          childrenComputed, terminal] at computed ⊢
        exact computed
      · nth_rewrite 1 [
          buildAromaticCanonicalCumulativeRule45KeyWithRead?_step (fuel := fuel)
        ] at computed
        rw [childrenComputed] at computed
        simp [terminal, Option.bind_some] at computed
        cases childKeysComputed : children.mapM
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              stage read fuel) with
        | none => simp [childKeysComputed] at computed
        | some childKeys =>
            simp [childKeysComputed] at computed
            have childKeysNext : children.mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  stage read (fuel + 1)) = some childKeys :=
              list_mapM_of_pointwise_successor
                (fun child result success =>
                  buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
                    source stage read fuel child result success)
                children childKeys childKeysComputed
            nth_rewrite 1 [
              buildAromaticCanonicalCumulativeRule45KeyWithRead?_step (fuel := fuel + 1)
            ]
            rw [childrenComputed]
            simp [terminal, childKeysNext, Option.bind_some]
            exact computed

/-- Every successful arbitrary-reader cumulative key at a structural fuel is produced with the
same key at every larger fuel. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_success_monotone_of_le
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel)
    (key : source.AromaticCanonicalCumulativeRule45Key)
    (computed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage read lowFuel cursor = some key) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage read highFuel cursor = some key := by
  obtain ⟨difference, rfl⟩ := Nat.le.dest le
  clear le
  induction difference with
  | zero => simpa using computed
  | succ difference inductionHypothesis =>
      exact buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
        source stage read (lowFuel + difference) cursor key inductionHypothesis

/-! ### Stability of the compound layers -/

/-- One-step exact stability of one Rule-4b/4c reading. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_successor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (computed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read (fuel + 1) cursor reference = some reading := by
  cases reference with
  | none =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              have rule4bNext :=
                buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
                  source .rule4a read fuel cursor rule4bKey rule4bComputed
              have rule4cNext :=
                buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
                  source .rule4cNoReference read fuel cursor rule4cKey rule4cComputed
              simp [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
                rule4bNext, rule4cNext]
  | some reference =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              have rule4bNext :=
                buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
                  source (.rule4b reference) read fuel cursor rule4bKey rule4bComputed
              have rule4cNext :=
                buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
                  source (.rule4c reference) read fuel cursor rule4cKey rule4cComputed
              simp [buildAromaticCanonicalRerootRule4bcReadingWithRead?,
                rule4bNext, rule4cNext]

/-- One-step exact stability of the Rule-4b/4c reading list. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_successor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (references : List (Option RS))
      (readings : List source.AromaticCanonicalRerootRule4bcReading),
      source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read fuel cursor references = some readings →
      source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read (fuel + 1) cursor references = some readings
  | [], readings, computed => by
      simp [buildAromaticCanonicalRerootRule4bcReadingsWithRead?] at computed ⊢
      exact computed
  | reference :: references, readings, computed => by
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read fuel cursor reference with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
              read fuel cursor references with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              have headNext :=
                buildAromaticCanonicalRerootRule4bcReadingWithRead?_successor
                  source read fuel cursor reference head headComputed
              have tailNext :=
                buildAromaticCanonicalRerootRule4bcReadingsWithRead?_successor
                  source read fuel cursor references tail tailComputed
              simp [buildAromaticCanonicalRerootRule4bcReadingsWithRead?,
                headNext, tailNext]

/-- One-step exact stability of the complete compound Rules-4b/4c key. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_successor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read (fuel + 1) cursor = some key := by
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      simp [rule4aComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          read fuel cursor
          (aromaticCanonicalRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [rule4aComputed, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, readingsComputed] at computed
          subst key
          have rule4aNext :=
            buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
              source .rule4a read fuel cursor rule4aKey rule4aComputed
          have readingsNext :=
            buildAromaticCanonicalRerootRule4bcReadingsWithRead?_successor
              source read fuel cursor
              (aromaticCanonicalRule4bcReferenceAlternatives
                (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))
              readings readingsComputed
          simp [buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?,
            rule4aNext, readingsNext]

/-- One-step exact stability of one Rule-5 reading (both common-reference hierarchies). -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_successor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (computed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read (fuel + 1) cursor prior = some reading := by
  unfold buildAromaticCanonicalRerootRule5ReadingWithRead? at computed
  cases commonRComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      simp [commonRComputed] at computed
      cases commonSComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonRComputed, commonSComputed] at computed
      | some commonS =>
          simp [commonRComputed, commonSComputed] at computed
          subst reading
          have commonRNext :=
            buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
              source (aromaticCanonicalRule5StageFor prior.reference? .R)
              read fuel cursor commonR commonRComputed
          have commonSNext :=
            buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
              source (aromaticCanonicalRule5StageFor prior.reference? .S)
              read fuel cursor commonS commonSComputed
          simp [buildAromaticCanonicalRerootRule5ReadingWithRead?,
            commonRNext, commonSNext]

/-- One-step exact stability of the Rule-5 reading list. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_successor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (priors : List source.AromaticCanonicalRerootRule4bcReading)
      (readings : List source.AromaticCanonicalRerootRule5Reading),
      source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        read fuel cursor priors = some readings →
      source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        read (fuel + 1) cursor priors = some readings
  | [], readings, computed => by
      simp [buildAromaticCanonicalRerootRule5ReadingsWithRead?] at computed ⊢
      exact computed
  | prior :: priors, readings, computed => by
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          read fuel cursor prior with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
              read fuel cursor priors with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              have headNext :=
                buildAromaticCanonicalRerootRule5ReadingWithRead?_successor
                  source read fuel cursor prior head headComputed
              have tailNext :=
                buildAromaticCanonicalRerootRule5ReadingsWithRead?_successor
                  source read fuel cursor priors tail tailComputed
              simp [buildAromaticCanonicalRerootRule5ReadingsWithRead?,
                headNext, tailNext]

/-- **One-step exact stability of the complete through-Rule-5 compound key.**  A successful
arbitrary-reader compound key is reproduced with the identical value one fuel step later. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_successor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read (fuel + 1) cursor = some key := by
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      simp [priorComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [priorComputed, readingsComputed] at computed
      | some readings =>
          simp [priorComputed, readingsComputed] at computed
          subst key
          have priorNext :=
            buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_successor
              source read fuel cursor prior priorComputed
          have readingsNext :=
            buildAromaticCanonicalRerootRule5ReadingsWithRead?_successor
              source read fuel cursor prior.readings readings readingsComputed
          simp [buildAromaticCanonicalRerootCompoundRule45KeyWithRead?,
            priorNext, readingsNext]

/-- Every successful arbitrary-reader through-Rule-5 compound key at a structural fuel is produced
with the same key at every larger fuel. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_success_monotone_of_le
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read lowFuel cursor = some key) :
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read highFuel cursor = some key := by
  obtain ⟨difference, rfl⟩ := Nat.le.dest le
  clear le
  induction difference with
  | zero => simpa using computed
  | succ difference inductionHypothesis =>
      exact buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_successor
        source read (lowFuel + difference) cursor key inductionHypothesis

/-! ## Recovery of the shipped restricted API -/

/-- Specializing the reader to the existing source-canonical dependency label recovers the
shipped cumulative totality statement at the same bound. -/
theorem exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice_recovered
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalCumulativeRule45Key?
      stage target view (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨key, computed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      stage (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      cursor valid
  exact ⟨key, by
    rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
      stage target view (2 * (carrierFuel + 1)) cursor]
    exact computed⟩

/-- The complete restricted compound Rules-4b/4c key builder is recovered from the parametric
totality statement by the unconditional specialization of its arbitrary reader. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule4bcKey?_at_twice_recovered
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRerootCompoundRule4bcKey?
      target view (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨key, computed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      cursor valid
  exact ⟨key, by
    rw [← source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_eq_aromaticCanonicalDependencyLabel
      target view (2 * (carrierFuel + 1)) cursor]
    exact computed⟩

/-- The complete restricted through-Rule-5 compound key builder is recovered from the parametric
totality statement by the unconditional specialization of its arbitrary reader.  This is exactly
the shipped `exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice` statement. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice_recovered
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRerootCompoundRule45Key?
      target view (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨key, computed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      cursor valid
  exact ⟨key, by
    rw [← source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
      target view (2 * (carrierFuel + 1)) cursor]
    exact computed⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_of_budget_le
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootRule4bcReadingWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootRule4bcReadingsWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootRule5ReadingWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootRule5ReadingsWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_success_monotone_of_le
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_successor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_successor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_successor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_successor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_successor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_successor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_success_monotone_of_le
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice_recovered
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule4bcKey?_at_twice_recovered
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice_recovered
