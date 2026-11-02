import TetraStereo.OneCenter.LocalizedRerootRecursiveRule3SpatialKey
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Fuel completeness for recursively ranked localized Rule 3

Structural traversal and chemical evidence are separate obligations.  The reroot budget already
proves that twice the carrier depth covers every path-valid cursor.  Rule 3 adds one honest
chemical precondition: every carrier occurrence that is a genuine order-two edge must have enough
spatial evidence for the strict Rule-3 reader to resolve it.  Structural nonunits resolve as
`some none`; unresolved genuine units remain `none` and are never silently treated as absence.
-/

namespace CertifiedLocalizedCIPInput

/-- Every node in this finite carrier has a resolved Rule-3 tri-state reading. -/
def LocalizedRule3SpatiallyResolved
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) : Prop :=
  ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
    ∃ outcome, input.localizedRule3SpatialNode? occurrence.1.node = some outcome

private theorem exists_mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_of_forall
    (input : CertifiedLocalizedCIPInput) {carrierFuel evaluationFuel : Nat} :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        input.buildLocalizedRerootRecursiveRule3SpatialKey?
          evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (input.buildLocalizedRerootRecursiveRule3SpatialKey? evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        input.exists_mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_of_forall
          cursors (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- Evaluation succeeds when the structural fuel covers the decreasing cursor budget and every
genuine Rule-3 unit in the carrier has resolved spatial evidence. -/
theorem exists_buildLocalizedRerootRecursiveRule3SpatialKey?_of_budget_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (resolved : input.LocalizedRule3SpatiallyResolved carrierFuel) :
    ∀ evaluationFuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, input.buildLocalizedRerootRecursiveRule3SpatialKey?
        evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      obtain ⟨observation, observationComputed⟩ := resolved cursor.occurrence
      by_cases empty : children = []
      · refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }, ?_⟩
        simp [buildLocalizedRerootRecursiveRule3SpatialKey?, childrenComputed,
          observationComputed, empty]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := input.localizedRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      obtain ⟨observation, observationComputed⟩ := resolved cursor.occurrence
      by_cases empty : children = []
      · refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }, ?_⟩
        simp [buildLocalizedRerootRecursiveRule3SpatialKey?, childrenComputed,
          observationComputed, empty]
      · have childComplete : ∀ child ∈ children, ∃ key,
            input.buildLocalizedRerootRecursiveRule3SpatialKey?
              evaluationFuel child = some key := by
          intro child present
          have childValid := input.localizedRerootChild_valid
            cursor child children childrenDerived present
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply input.exists_buildLocalizedRerootRecursiveRule3SpatialKey?_of_budget_le
            resolved evaluationFuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          input.exists_mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_of_forall
            children childComplete
        let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
        refine ⟨
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations observation ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities observation ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }, ?_⟩
        simp [buildLocalizedRerootRecursiveRule3SpatialKey?, childrenComputed,
          observationComputed, empty, childKeysComputed, sorted]

/-- Twice the carrier depth suffices for every path-valid cursor once Rule-3 evidence resolves. -/
theorem exists_buildLocalizedRerootRecursiveRule3SpatialKey?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (resolved : input.LocalizedRule3SpatiallyResolved carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootRecursiveRule3SpatialKey?
      (2 * (carrierFuel + 1)) cursor = some key := by
  apply input.exists_buildLocalizedRerootRecursiveRule3SpatialKey?_of_budget_le
    resolved (2 * (carrierFuel + 1)) cursor valid
  exact input.localizedRerootCursorBudget_le_twice cursor

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
