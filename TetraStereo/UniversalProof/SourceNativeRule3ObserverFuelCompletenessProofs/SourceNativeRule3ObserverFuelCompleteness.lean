import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SourceNativeRule3ObserverFuelCompletenessProofs.SourceNativeRule3ObserverFuelCompleteness

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame

/-!
Fuel completeness for the actual callback-parameterized Rule-3 compiler. The premise that the
observer resolves every optional node outcome is a library domain condition, not a proved fact
about every chemical source. Negative outcomes remain permitted. Source-specific observer
resolution, topology readiness and scientific validation must be established separately.

The existing structural cursor budget bounds both passes by `2 * (carrierFuel + 1)`. A common
exclusion policy observes before cancelling, so it preserves unresolved refusal outside the total
domain. Returned keys and frames satisfy the checked observer's independent canonical judgment;
no expected key, successful sorter, spatial point or caller-supplied chemical label is required.
-/

def ObserverTotal {source : AuthoritativeChemicalInput}
    (observer : Rule3Observer source) : Prop :=
  ∀ node, ∃ outcome, observer.observe node = some outcome

variable {source : AuthoritativeChemicalInput} (observer : Rule3Observer source)

theorem exists_mapM_observer_keys_of_forall {carrierFuel evaluationFuel : Nat} :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        source.buildAromaticCanonicalRule3SpatialKeyWith?
          observer.observe evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe evaluationFuel) =
          some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ := exists_mapM_observer_keys_of_forall
        cursors (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- A valid cursor's decreasing structural budget suffices for the actual generic compiler. -/
theorem exists_observer_key_of_budget_le {carrierFuel : Nat}
    (total : ObserverTotal observer) :
    ∀ evaluationFuel (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.AromaticCanonicalRerootCursorValid cursor →
      source.aromaticCanonicalRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, source.buildAromaticCanonicalRule3SpatialKeyWith?
        observer.observe evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenDerived := source.aromaticCanonicalRerootChildren_sound cursor
      obtain ⟨observation, observationComputed⟩ := total cursor.occurrence.1.node
      by_cases empty : children = []
      · refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }, ?_⟩
        simp [buildAromaticCanonicalRule3SpatialKeyWith?, children,
          observationComputed, empty]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := source.aromaticCanonicalRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenDerived := source.aromaticCanonicalRerootChildren_sound cursor
      obtain ⟨observation, observationComputed⟩ := total cursor.occurrence.1.node
      by_cases empty : children = []
      · refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }, ?_⟩
        simp [buildAromaticCanonicalRule3SpatialKeyWith?, children,
          observationComputed, empty]
      · have childComplete : ∀ child ∈ children, ∃ key,
            source.buildAromaticCanonicalRule3SpatialKeyWith?
              observer.observe evaluationFuel child = some key := by
          intro child present
          have childValid := source.aromaticCanonicalRerootChild_valid
            cursor child children childrenDerived present
          have decreases := source.aromaticCanonicalRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply exists_observer_key_of_budget_le total
            evaluationFuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          exists_mapM_observer_keys_of_forall observer children childComplete
        let compare := source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        let sorted := sortAromaticCanonicalUncancelledRule3SpatialKeys compare childKeys
        refine ⟨
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := source.aromaticCanonicalRule3RootObservations observation ++
              mergeAromaticCanonicalRule3ObservationChildren sorted
            rule3 := source.aromaticCanonicalRule3RootPriorities observation ++
              mergeAromaticCanonicalRule3PriorityChildren sorted }, ?_⟩
        simp [buildAromaticCanonicalRule3SpatialKeyWith?, children,
          observationComputed, empty, childKeysComputed, compare, sorted]

theorem exists_observer_key_at_twice {carrierFuel : Nat}
    (total : ObserverTotal observer)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRule3SpatialKeyWith?
      observer.observe (2 * (carrierFuel + 1)) cursor = some key := by
  exact exists_observer_key_of_budget_le observer total _ cursor valid
    (source.aromaticCanonicalRerootCursorBudget_le_twice cursor)

theorem exists_observer_key_at_or_above_twice {carrierFuel evaluationFuel : Nat}
    (total : ObserverTotal observer)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (enough : 2 * (carrierFuel + 1) ≤ evaluationFuel) :
    ∃ key, source.buildAromaticCanonicalRule3SpatialKeyWith?
      observer.observe evaluationFuel cursor = some key := by
  exact exists_observer_key_of_budget_le observer total evaluationFuel cursor valid
    (Nat.le_trans (source.aromaticCanonicalRerootCursorBudget_le_twice cursor) enough)

/-- Cancellation retains total optional observations without requiring positive outcomes. -/
theorem excludedObserver_total (total : ObserverTotal observer)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    ObserverTotal (excludedObserver observer excluded) := by
  classical
  intro node
  obtain ⟨outcome, computed⟩ := total node
  cases outcome with
  | none => exact ⟨none, by simp [excludedObserver, observeExcept, computed]⟩
  | some result =>
      by_cases cancelled : result.physicalUnitId ∈ excluded
      · exact ⟨none, by simp [excludedObserver, observeExcept, computed, cancelled]⟩
      · exact ⟨some result, by simp [excludedObserver, observeExcept, computed, cancelled]⟩

theorem exists_excluded_observer_key_of_budget_le {carrierFuel evaluationFuel : Nat}
    (total : ObserverTotal observer)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (covered : source.aromaticCanonicalRerootCursorBudget cursor ≤ evaluationFuel) :
    ∃ key, source.buildAromaticCanonicalRule3SpatialKeyWith?
      (observeExcept observer excluded) evaluationFuel cursor = some key :=
  exists_observer_key_of_budget_le (excludedObserver observer excluded)
    (excludedObserver_total observer total excluded) evaluationFuel cursor valid covered

theorem exists_excluded_observer_key_at_twice {carrierFuel : Nat}
    (total : ObserverTotal observer)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRule3SpatialKeyWith?
      (observeExcept observer excluded) (2 * (carrierFuel + 1)) cursor = some key :=
  exists_excluded_observer_key_of_budget_le observer total excluded cursor valid
    (source.aromaticCanonicalRerootCursorBudget_le_twice cursor)

/-- Actual list success and the observer's exact independent recursive judgment. -/
theorem exists_observer_key_list_at_or_above_twice {carrierFuel evaluationFuel : Nat}
    (total : ObserverTotal observer)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor)
    (enough : 2 * (carrierFuel + 1) ≤ evaluationFuel) :
    ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe evaluationFuel) =
          some keys ∧
      source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
        observer.NodeOutcome evaluationFuel cursors keys := by
  obtain ⟨keys, computed⟩ := exists_mapM_observer_keys_of_forall observer cursors
    (fun cursor present => exists_observer_key_at_or_above_twice observer total
      cursor (valid cursor present) enough)
  exact ⟨keys, computed,
    (buildObserverKeyList_eq_some_iff observer evaluationFuel cursors keys).mp computed⟩

/-- Topology unambiguity remains an independent frame-level chemical obligation. -/
theorem exists_observer_frame_at_or_above_twice {carrierFuel evaluationFuel : Nat}
    (total : ObserverTotal observer)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor)
    (enough : 2 * (carrierFuel + 1) ≤ evaluationFuel)
    (topology : ∀ rawKeys,
      source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
        observer.NodeOutcome evaluationFuel cursors rawKeys →
      source.DeclarativeAromaticCanonicalRule3TopologyUnambiguous rawKeys) :
    ∃ frame, buildRule3ObserverFrame? observer evaluationFuel cursors = some frame ∧
      CanonicalRule3ObserverFrame observer evaluationFuel cursors frame := by
  obtain ⟨rawKeys, rawComputed, rawMeaning⟩ :=
    exists_observer_key_list_at_or_above_twice observer total cursors valid enough
  obtain ⟨resolution, resolutionComputed⟩ :=
    (source.aromaticCanonicalRule3TopologyUnambiguous_iff_declarative rawKeys).mpr
      (topology rawKeys rawMeaning)
  let excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
  obtain ⟨keys, keysComputed, _⟩ := exists_observer_key_list_at_or_above_twice
    (excludedObserver observer excluded) (excludedObserver_total observer total excluded)
    cursors valid enough
  change cursors.mapM
    (source.buildAromaticCanonicalRule3SpatialKeyWith?
      (observeExcept observer excluded) evaluationFuel) = some keys at keysComputed
  let frame : source.AromaticCanonicalRule3CanonicalKeyFrame :=
    { rawKeys, resolution, excluded, keys }
  have computed : buildRule3ObserverFrame? observer evaluationFuel cursors = some frame := by
    dsimp only [excluded] at keysComputed
    simp [buildRule3ObserverFrame?, frame, rawComputed, resolutionComputed,
      excluded, keysComputed]
  exact ⟨frame, computed,
    buildRule3ObserverFrame?_sound observer evaluationFuel cursors frame computed⟩

/-- Outside the total domain a failed base observation is still a failed excluded observation. -/
theorem excludedObserver_preserves_refusal
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (unresolved : observer.observe node = none) :
    (excludedObserver observer excluded).observe node = none :=
  observeExcept_preserves_unresolved observer excluded node unresolved

end TetraStereo.UniversalProof.SourceNativeRule3ObserverFuelCompletenessProofs.SourceNativeRule3ObserverFuelCompleteness
