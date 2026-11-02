import TetraStereo.OneCenter.LocalizedUniqueNearestRule4bReference
import TetraStereo.OneCenter.LocalizedRule4bSparseLabelDecoding
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput
















































/-! ## Layer predicates -/

/-- Every recorded observation in every sphere is absent (`none`). -/
def LocalizedLabelLayersAllNone
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) : Prop :=
  ∀ layer, layer ∈ layers → ∀ entry, entry ∈ layer → entry.2 = none

/-- No recorded observation in any sphere is an uppercase chiral label. -/
def LocalizedLabelLayersChiralFree
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) : Prop :=
  ∀ layer, layer ∈ layers → ∀ entry, entry ∈ layer →
    ∀ descriptor : RS, entry.2 ≠ some (.chiral descriptor)

/-- All-`none` layers are chiral-free.  (The converse needs the sparse domain.) -/
theorem localizedLabelLayersChiralFree_of_allNone
    {layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (allNone : LocalizedLabelLayersAllNone layers) :
    LocalizedLabelLayersChiralFree layers := by
  intro layer layerPresent entry entryPresent descriptor chiral
  rw [allNone layer layerPresent entry entryPresent] at chiral
  cases chiral

/-- On the `none`/uppercase-chiral sparse domain, chiral-freeness is exactly all-`none`. -/
theorem localizedLabelLayersChiralFree_iff_allNone_of_sparse
    {layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (sparse : LocalizedLabelLayersSparse layers) :
    LocalizedLabelLayersChiralFree layers ↔ LocalizedLabelLayersAllNone layers := by
  constructor
  · intro free layer layerPresent entry entryPresent
    rcases sparse layer layerPresent entry entryPresent with absent | ⟨descriptor, chiral⟩
    · exact absent
    · exact absurd chiral (free layer layerPresent entry entryPresent descriptor)
  · exact localizedLabelLayersChiralFree_of_allNone

/-! ## Inversion of the executable selector on arbitrary ranked label tables -/

/-- The population selector returns `[]` exactly for the empty population. -/
theorem localizedRule4bReferencesFromPopulation_eq_nil_iff (descriptors : List RS) :
    localizedRule4bReferencesFromPopulation descriptors = [] ↔ descriptors = [] := by
  by_cases empty : descriptors = []
  · subst descriptors
    simp [localizedRule4bReferencesFromPopulation]
  · have notEmpty : descriptors.isEmpty = false := by
      simpa [List.isEmpty_iff] using empty
    rw [localizedRule4bReferencesFromPopulation, notEmpty]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases rMajor :
        (descriptors.filter fun descriptor => descriptor == RS.S).length <
          (descriptors.filter fun descriptor => descriptor == RS.R).length
    · rw [if_pos rMajor]
      constructor
      · intro equal
        cases equal
      · intro equal
        exact (empty equal).elim
    · rw [if_neg rMajor]
      by_cases sMajor :
          (descriptors.filter fun descriptor => descriptor == RS.R).length <
            (descriptors.filter fun descriptor => descriptor == RS.S).length
      · rw [if_pos sMajor]
        constructor
        · intro equal
          cases equal
        · intro equal
          exact (empty equal).elim
      · rw [if_neg sMajor]
        constructor
        · intro equal
          cases equal
        · intro equal
          exact (empty equal).elim

/-- `localizedFirstChiralRankPopulationInLayer` returns `none` exactly when the sphere contains
no uppercase chiral observation. -/
theorem localizedFirstChiralRankPopulationInLayer_eq_none_iff
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    localizedFirstChiralRankPopulationInLayer layer = none ↔
      ∀ entry, entry ∈ layer →
        ∀ descriptor : RS, entry.2 ≠ some (.chiral descriptor) := by
  induction layer with
  | nil =>
      simp [localizedFirstChiralRankPopulationInLayer]
  | cons head rest inductionHypothesis =>
      rcases head with ⟨rank, label⟩
      cases label with
      | none =>
          simp only [localizedFirstChiralRankPopulationInLayer]
          rw [inductionHypothesis]
          constructor
          · intro tailFree entry present descriptor chiral
            rcases List.mem_cons.mp present with same | later
            · subst entry
              cases chiral
            · exact tailFree entry later descriptor chiral
          · intro all entry present descriptor chiral
            exact all entry (List.mem_cons_of_mem _ present) descriptor chiral
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              simp only [localizedFirstChiralRankPopulationInLayer]
              rw [inductionHypothesis]
              constructor
              · intro tailFree entry present observedDescriptor chiral
                rcases List.mem_cons.mp present with same | later
                · subst entry
                  cases chiral
                · exact tailFree entry later observedDescriptor chiral
              · intro all entry present observedDescriptor chiral
                exact all entry (List.mem_cons_of_mem _ present) observedDescriptor chiral
          | chiral descriptor =>
              simp only [localizedFirstChiralRankPopulationInLayer]
              constructor
              · intro equal
                cases equal
              · intro all
                exact (all (rank, some (.chiral descriptor)) (by simp) descriptor rfl).elim

/-- A sphere containing an uppercase chiral observation never has the empty population. -/
theorem localizedFirstChiralRankPopulationInLayer_ne_some_nil :
    ∀ layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)),
      localizedFirstChiralRankPopulationInLayer layer ≠ some [] := by
  intro layer
  induction layer with
  | nil =>
      simp [localizedFirstChiralRankPopulationInLayer]
  | cons head rest inductionHypothesis =>
      rcases head with ⟨rank, label⟩
      cases label with
      | none =>
          simpa [localizedFirstChiralRankPopulationInLayer] using inductionHypothesis
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              simpa [localizedFirstChiralRankPopulationInLayer] using inductionHypothesis
          | chiral descriptor =>
              simp [localizedFirstChiralRankPopulationInLayer]

/-- The first-chiral-rank traversal over a stack returns `[]` exactly when no sphere contains an
uppercase chiral observation.  No hierarchy ordering of the spheres is assumed. -/
theorem localizedFirstChiralRankPopulation_eq_nil_iff
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    localizedFirstChiralRankPopulation layers = [] ↔
      ∀ layer, layer ∈ layers → ∀ entry, entry ∈ layer →
        ∀ descriptor : RS, entry.2 ≠ some (.chiral descriptor) := by
  induction layers with
  | nil =>
      simp [localizedFirstChiralRankPopulation]
  | cons layer layers inductionHypothesis =>
      unfold localizedFirstChiralRankPopulation
      cases observed : localizedFirstChiralRankPopulationInLayer layer with
      | none =>
          rw [inductionHypothesis]
          constructor
          · intro tailFree targetLayer targetPresent entry entryPresent descriptor chiral
            rcases List.mem_cons.mp targetPresent with same | later
            · subst targetLayer
              exact (localizedFirstChiralRankPopulationInLayer_eq_none_iff layer).mp observed
                entry entryPresent descriptor chiral
            · exact tailFree targetLayer later entry entryPresent descriptor chiral
          · intro all targetLayer targetPresent entry entryPresent descriptor chiral
            exact all targetLayer (List.mem_cons_of_mem layer targetPresent)
              entry entryPresent descriptor chiral
      | some population =>
          have nonempty : population ≠ [] := by
            intro populationNil
            have emptyObserved : localizedFirstChiralRankPopulationInLayer layer = some [] := by
              rw [observed, populationNil]
            exact localizedFirstChiralRankPopulationInLayer_ne_some_nil layer emptyObserved
          constructor
          · intro equal
            exact (nonempty equal).elim
          · intro all
            have layerFree : ∀ entry, entry ∈ layer →
                ∀ descriptor : RS, entry.2 ≠ some (.chiral descriptor) :=
              fun entry present descriptor chiral =>
                all layer (by simp) entry present descriptor chiral
            have noneObserved :=
              (localizedFirstChiralRankPopulationInLayer_eq_none_iff layer).mpr layerFree
            rw [noneObserved] at observed
            cases observed

/-- **Selector inversion on arbitrary ranked label tables.**  The actual executable Rule-4b
selector returns `[]` exactly when no observation in any sphere is an uppercase chiral label.
No hierarchy-order or sortedness assumption is used. -/
theorem localizedRule4bReferencesFromRankedLabels_eq_nil_iff
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    localizedRule4bReferencesFromRankedLabels layers = [] ↔
      ∀ layer, layer ∈ layers → ∀ entry, entry ∈ layer →
        ∀ descriptor : RS, entry.2 ≠ some (.chiral descriptor) := by
  unfold localizedRule4bReferencesFromRankedLabels
  rw [localizedRule4bReferencesFromPopulation_eq_nil_iff,
    localizedFirstChiralRankPopulation_eq_nil_iff]

/-- Sparse-domain form: an empty selection is equivalent to every recorded observation being
`none`. -/
theorem localizedRule4bReferencesFromRankedLabels_eq_nil_iff_allNone
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (sparse : LocalizedLabelLayersSparse layers) :
    localizedRule4bReferencesFromRankedLabels layers = [] ↔
      LocalizedLabelLayersAllNone layers := by
  rw [localizedRule4bReferencesFromRankedLabels_eq_nil_iff]
  exact localizedLabelLayersChiralFree_iff_allNone_of_sparse sparse

/-! ## Address-forgetting transport between actual tables -/

/-- An address-forgetting sequence equality transfers any label predicate from the first sphere to
the second. -/
theorem localizedSparseLayer_forall_of_map_snd_eq
    {first second : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))}
    (equal : first.map Prod.snd = second.map Prod.snd)
    (predicate : Option LocalizedAuxiliaryLabel → Prop)
    (holds : ∀ entry, entry ∈ first → predicate entry.2) :
    ∀ entry, entry ∈ second → predicate entry.2 := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil =>
          intro entry present
          simp at present
      | cons head tail =>
          simp at equal
  | cons head tail inductionHypothesis =>
      cases second with
      | nil => simp at equal
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at equal
          obtain ⟨headEqual, tailEqual⟩ := equal
          intro entry present
          rcases List.mem_cons.mp present with same | later
          · subst entry
            rw [← headEqual]
            exact holds head (by simp)
          · exact inductionHypothesis (second := rest) tailEqual
              (fun inner innerPresent => holds inner (by simp [innerPresent])) entry later

/-- Spherewise address-forgetting equality transfers a label predicate between whole label
stacks. -/
theorem localizedLabelLayers_forall_of_map_snd_eq
    {first second : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (equal : first.map (List.map Prod.snd) = second.map (List.map Prod.snd))
    (predicate : Option LocalizedAuxiliaryLabel → Prop)
    (holds : ∀ layer, layer ∈ first → ∀ entry, entry ∈ layer → predicate entry.2) :
    ∀ layer, layer ∈ second → ∀ entry, entry ∈ layer → predicate entry.2 := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil =>
          intro layer present
          simp at present
      | cons head tail =>
          simp at equal
  | cons head tail inductionHypothesis =>
      cases second with
      | nil => simp at equal
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at equal
          obtain ⟨headEqual, tailEqual⟩ := equal
          intro layer present entry entryPresent
          rcases List.mem_cons.mp present with same | later
          · subst layer
            exact localizedSparseLayer_forall_of_map_snd_eq headEqual predicate
              (fun inner innerPresent => holds head (by simp) inner innerPresent)
              entry entryPresent
          · exact inductionHypothesis (second := rest) tailEqual
              (fun inner innerPresent innerEntry innerEntryPresent =>
                holds inner (by simp [innerPresent]) innerEntry innerEntryPresent)
              layer later entry entryPresent

/-! ## Actual cumulative builder -/





theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [] ↔
      LocalizedLabelLayersChiralFree key.labels := by
  have invariant :=
    input.buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_forgetAddresses
      stage target view fuel cursor key computed
  constructor
  · intro selection
    have rankedFree : LocalizedLabelLayersChiralFree key.rankedLabels :=
      (localizedRule4bReferencesFromRankedLabels_eq_nil_iff key.rankedLabels).mp selection
    exact localizedLabelLayers_forall_of_map_snd_eq invariant.2.symm
      (fun label => ∀ descriptor : RS, label ≠ some (.chiral descriptor)) rankedFree
  · intro free
    have rankedFree : LocalizedLabelLayersChiralFree key.rankedLabels :=
      localizedLabelLayers_forall_of_map_snd_eq invariant.2
        (fun label => ∀ descriptor : RS, label ≠ some (.chiral descriptor)) free
    exact (localizedRule4bReferencesFromRankedLabels_eq_nil_iff key.rankedLabels).mpr rankedFree

/-- The sparse production wrapper.  From an actual successful build and an actual sparse
dependency reader (no supplied label absence and no supplied selector equation), an empty
selection is equivalent to every recorded label in `key.labels` being `none`. -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_allNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (readerSparse : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      LocalizedRule4bSparseLabel (input.localizedDependencyLabel target view cursor)) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [] ↔
      LocalizedLabelLayersAllNone key.labels := by
  have withRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
        some key := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel]
    exact computed
  have labelSparse : LocalizedLabelLayersSparse key.labels :=
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse stage
      (fun cursor => input.localizedDependencyLabel target view cursor)
      readerSparse fuel cursor key withRead
  rw [input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
    stage target view fuel cursor key computed]
  exact localizedLabelLayersChiralFree_iff_allNone_of_sparse labelSparse

/-- Forward direction in production form: an empty selector yields all-`none` actual labels. -/
theorem buildLocalizedRerootCumulativeRule45Key?_labels_allNone_of_referenceSelection_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (readerSparse : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      LocalizedRule4bSparseLabel (input.localizedDependencyLabel target view cursor))
    (selection : localizedRule4bReferencesFromRankedLabels key.rankedLabels = []) :
    LocalizedLabelLayersAllNone key.labels :=
  (input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_allNone
    stage target view fuel cursor key computed readerSparse).mp selection

/-- **Converse in production form**: all-`none` actual labels force the empty selector.  This
needs no sparse-reader hypothesis. -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_of_labels_allNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (allNone : LocalizedLabelLayersAllNone key.labels) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [] :=
  (input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
    stage target view fuel cursor key computed).mpr
    (localizedLabelLayersChiralFree_of_allNone allNone)

/-! ## Actual compound builder -/

/-- The no-reference alternative list is exactly `[none]`, so an empty selection compiles the
single actual no-reference reading. -/
@[simp] theorem localizedRule4bcReferenceAlternatives_nil :
    localizedRule4bcReferenceAlternatives ([] : List RS) = [none] := rfl

/-- A successful single-alternative reading list exposes its one actual reading and that
reading's actual successful compilation. -/
private theorem buildLocalizedRerootRule4bcReadings?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (readings : List input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadings?
      target view fuel cursor [reference] = some readings) :
    ∃ single : input.LocalizedRerootRule4bcReading,
      readings = [single] ∧
        input.buildLocalizedRerootRule4bcReading?
          target view fuel cursor reference = some single := by
  unfold buildLocalizedRerootRule4bcReadings? at computed
  cases headComputed : input.buildLocalizedRerootRule4bcReading?
      target view fuel cursor reference with
  | none => simp [headComputed] at computed
  | some reading =>
      have computed' :
          some (reading :: ([] : List input.LocalizedRerootRule4bcReading)) =
            some readings := by
        simpa only [buildLocalizedRerootRule4bcReadings?, headComputed,
          Option.bind_some] using computed
      have readingsEq : readings = [reading] := by
        simpa only [Option.some.injEq] using computed'.symm
      rw [readingsEq]
      exact ⟨reading, rfl, rfl⟩

/-- A successful actual no-reference reading carries `reference? = none`. -/
private theorem buildLocalizedRerootRule4bcReading?_reference?_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReading?
      target view fuel cursor none = some reading) :
    reading.reference? = none := by
  unfold buildLocalizedRerootRule4bcReading? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4bKey =>
      cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4cNoReference target view fuel cursor with
      | none => simp [rule4aComputed, rule4cComputed] at computed
      | some rule4cKey =>
          simp [rule4aComputed, rule4cComputed] at computed
          subst reading
          rfl

/-- **Actual compound empty-reference reading.**  If a successful compound build selects no
reference, it produces exactly one actual reading, that reading's `reference?` is `none`, and it
is the actual output of the no-reference single-reading builder. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_references_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (references : key.references = []) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = none ∧
        input.buildLocalizedRerootRule4bcReading?
          target view fuel cursor none = some reading := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references' :=
        localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references'
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references', alternatives, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references', alternatives, readingsComputed] at computed
          subst key
          have referencesEq : references' = [] := references
          have alternativesEq : alternatives = [none] := by
            simp [alternatives, referencesEq]
          rw [alternativesEq] at readingsComputed
          obtain ⟨reading, readingsEq, readingComputed⟩ :=
            buildLocalizedRerootRule4bcReadings?_singleton input target view fuel cursor
              none readings readingsComputed
          exact ⟨reading, readingsEq,
            buildLocalizedRerootRule4bcReading?_reference?_eq_none input target view fuel cursor
              reading readingComputed,
            readingComputed⟩

/-- **Actual compound inversion.**  A successful compound Rule-4b/4c build selects no reference
exactly when the retained actual Rule-4a key's `labels` table is chiral-free.  This uses the
existing `references_eq` identification of `key.references` with the executable selector on
`key.rule4aKey.rankedLabels`, and the existing `rule4aKey` extraction theorem. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_iff_rule4aKey_labels_chiralFree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    key.references = [] ↔ LocalizedLabelLayersChiralFree key.rule4aKey.labels := by
  have rule4aComputed :=
    buildLocalizedRerootCompoundRule4bcKey?_rule4aKey
      input target view fuel cursor key computed
  have referencesEqual :=
    buildLocalizedRerootCompoundRule4bcKey?_references_eq
      input target view fuel cursor key computed
  rw [referencesEqual]
  exact
    input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
      .rule4a target view fuel cursor key.rule4aKey rule4aComputed

/-- Sparse form of the compound inversion. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_iff_rule4aKey_labels_allNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (readerSparse : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      LocalizedRule4bSparseLabel (input.localizedDependencyLabel target view cursor)) :
    key.references = [] ↔ LocalizedLabelLayersAllNone key.rule4aKey.labels := by
  have rule4aComputed :=
    buildLocalizedRerootCompoundRule4bcKey?_rule4aKey
      input target view fuel cursor key computed
  have referencesEqual :=
    buildLocalizedRerootCompoundRule4bcKey?_references_eq
      input target view fuel cursor key computed
  rw [referencesEqual]
  exact
    input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_allNone
      .rule4a target view fuel cursor key.rule4aKey rule4aComputed readerSparse

/-- A compound build with an empty reference list has all-`none` actual Rule-4a labels. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (readerSparse : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      LocalizedRule4bSparseLabel (input.localizedDependencyLabel target view cursor))
    (references : key.references = []) :
    LocalizedLabelLayersAllNone key.rule4aKey.labels :=
  (input.buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_iff_rule4aKey_labels_allNone
    target view fuel cursor key computed readerSparse).mp references

/-- All-`none` actual Rule-4a labels force an empty compound reference list. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_of_rule4aKey_labels_allNone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (allNone : LocalizedLabelLayersAllNone key.rule4aKey.labels) :
    key.references = [] :=
  (input.buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_iff_rule4aKey_labels_chiralFree
    target view fuel cursor key computed).mpr
    (localizedLabelLayersChiralFree_of_allNone allNone)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedLabelLayersAllNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedLabelLayersChiralFree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLabelLayersChiralFree_of_allNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLabelLayersChiralFree_iff_allNone_of_sparse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bReferencesFromPopulation_eq_nil_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedFirstChiralRankPopulationInLayer_eq_none_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedFirstChiralRankPopulationInLayer_ne_some_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedFirstChiralRankPopulation_eq_nil_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bReferencesFromRankedLabels_eq_nil_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bReferencesFromRankedLabels_eq_nil_iff_allNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSparseLayer_forall_of_map_snd_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLabelLayers_forall_of_map_snd_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_allNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_labels_allNone_of_referenceSelection_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_of_labels_allNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bcReferenceAlternatives_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_references_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_iff_rule4aKey_labels_chiralFree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_iff_rule4aKey_labels_allNone
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_references_eq_nil_of_rule4aKey_labels_allNone
