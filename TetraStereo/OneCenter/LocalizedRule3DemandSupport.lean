import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3FuelCompleteness
import TetraStereo.OneCenter.LocalizedRule3CoupledTopologyApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter



















































namespace CertifiedLocalizedCIPInput

/-- Demand-sensitive recursive support for one descriptor-bearing Rule-3 key.

The predicate is structural in the shared fuel index, matching the structure of
`buildLocalizedRerootDescriptorBearingRule3Key?`: the node layer at `fuel + 1` delegates to the
predecessor frame via `LocalizedDescriptorBearingRule3NodeSupport`, and every declarative reroot
child is charged only the predecessor index.  This is the quantifier structure that the former
chemical-applicability premise could not express uniformly. -/
def LocalizedRule3KeyDemandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → input.LocalizedRerootCursor carrierFuel → Prop
  | 0, cursor =>
      input.LocalizedRerootCursorValid cursor ∧
      input.localizedRerootCursorBudget cursor ≤ 0 ∧
      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence
  | fuel + 1, cursor =>
      input.LocalizedRerootCursorValid cursor ∧
      input.localizedRerootCursorBudget cursor ≤ fuel + 1 ∧
      input.LocalizedDescriptorBearingRule3NodeSupport
        target cursor.occurrence view (fuel + 1) ∧
      ∀ children,
        input.DeclarativeLocalizedRerootChildren cursor children →
        ∀ child ∈ children,
          input.LocalizedRule3KeyDemandSupport target view fuel child

/-- Demand-sensitive recursive support for one descriptor-bearing Rule-3 frame.  At a successor
the two-pass builder only ever calls the predecessor key index, so exactly predecessor key demand
support is required; topology refusal is then ruled out by the pre-existing declarative
unambiguity condition. -/
def LocalizedRule3FrameDemandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List (input.LocalizedRerootCursor carrierFuel) → Prop
  | 0, _cursors => False
  | fuel + 1, cursors =>
      (∀ cursor ∈ cursors,
        input.LocalizedRule3KeyDemandSupport target view fuel cursor) ∧
      input.LocalizedDescriptorBearingRule3FrameDeclarativelyUnambiguous
        target view (fuel + 1) cursors

private theorem exists_mapM_buildKey_of_forall
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        input.buildLocalizedRerootDescriptorBearingRule3Key?
          target view fuel excluded cursor = some key) →
      ∃ keys, cursors.mapM
        (input.buildLocalizedRerootDescriptorBearingRule3Key?
          target view fuel excluded) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        input.exists_mapM_buildKey_of_forall target view fuel excluded cursors
          (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- Demand-sensitive key support makes the real descriptor-bearing key builder total for every
exclusion list.  The proof is ordinary induction on the shared fuel index: the node observation
comes from the existing executable node-support theorem
`exists_localizedDescriptorBearingRule3NodeWith?_of_support`, and the child keys come from the
actual fail-closed child enumeration plus the induction hypothesis. -/
theorem exists_buildLocalizedRerootDescriptorBearingRule3Key?_of_demandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRule3KeyDemandSupport target view fuel cursor →
      ∃ key, input.buildLocalizedRerootDescriptorBearingRule3Key?
        target view fuel excluded cursor = some key := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor support
      change (input.LocalizedRerootCursorValid cursor ∧
          input.localizedRerootCursorBudget cursor ≤ 0 ∧
          ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence) at support
      rcases support with ⟨valid, covered, notEdge⟩
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      have structuralResolved : ∃ observation,
          input.localizedDescriptorBearingRule3StructuralNode?
            cursor.occurrence = some observation := by
        classical
        exact ⟨none, by simp [localizedDescriptorBearingRule3StructuralNode?, notEdge]⟩
      obtain ⟨observation, observationComputed⟩ := structuralResolved
      by_cases empty : children = []
      · refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }, ?_⟩
        simp [buildLocalizedRerootDescriptorBearingRule3Key?, childrenComputed,
          observationComputed, empty]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := input.localizedRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | succ fuel ih =>
      intro excluded cursor support
      change (input.LocalizedRerootCursorValid cursor ∧
          input.localizedRerootCursorBudget cursor ≤ fuel + 1 ∧
          input.LocalizedDescriptorBearingRule3NodeSupport
            target cursor.occurrence view (fuel + 1) ∧
          (∀ children,
            input.DeclarativeLocalizedRerootChildren cursor children →
            ∀ child ∈ children,
              input.LocalizedRule3KeyDemandSupport target view fuel child)) at support
      rcases support with ⟨valid, covered, nodeSupport, childSupport⟩
      change input.LocalizedDescriptorBearingRule3NodeWithSupport target view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
        cursor.occurrence at nodeSupport
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      obtain ⟨observation, observationComputed⟩ :=
        input.exists_localizedDescriptorBearingRule3NodeWith?_of_support
          target cursor.occurrence view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel)
          excluded nodeSupport
      by_cases empty : children = []
      · refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }, ?_⟩
        simp [buildLocalizedRerootDescriptorBearingRule3Key?, childrenComputed,
          observationComputed, empty]
      · have childComplete : ∀ child ∈ children, ∃ key,
            input.buildLocalizedRerootDescriptorBearingRule3Key?
              target view fuel excluded child = some key := by
          intro child present
          have childDemand := childSupport children childrenDerived child present
          exact ih excluded child childDemand
        obtain ⟨childKeys, childKeysComputed⟩ :=
          input.exists_mapM_buildKey_of_forall
            target view fuel excluded children childComplete
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
        simp [buildLocalizedRerootDescriptorBearingRule3Key?, childrenComputed,
          observationComputed, empty, childKeysComputed, sorted]

/-- Demand-sensitive frame support makes the real two-pass descriptor-bearing frame builder total.
Both the raw (`[]`) and the rebuilt (computed exclusion) key passes succeed from the same
predecessor key demand support; the resolved topology comes from the pre-existing declarative
unambiguity condition. -/
theorem exists_buildLocalizedDescriptorBearingRule3Frame?_of_demandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel (cursors : List (input.LocalizedRerootCursor carrierFuel)),
      input.LocalizedRule3FrameDemandSupport target view fuel cursors →
      ∃ frame, input.buildLocalizedDescriptorBearingRule3Frame?
        target view fuel cursors = some frame := by
  intro fuel cursors support
  cases fuel with
  | zero =>
      change False at support
      exact support.elim
  | succ keyFuel =>
      change ((∀ cursor ∈ cursors,
          input.LocalizedRule3KeyDemandSupport target view keyFuel cursor) ∧
        (∀ rawKeys,
          cursors.mapM
            (input.buildLocalizedRerootDescriptorBearingRule3Key?
              target view keyFuel []) = some rawKeys →
          input.DeclarativeLocalizedRule3CoupledTopologyUnambiguous rawKeys)) at support
      rcases support with ⟨keysSupported, unambiguous⟩
      have keyComplete : ∀ excluded cursor, cursor ∈ cursors → ∃ key,
          input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view keyFuel excluded cursor = some key := by
        intro excluded cursor present
        exact input.exists_buildLocalizedRerootDescriptorBearingRule3Key?_of_demandSupport
          target view keyFuel excluded cursor (keysSupported cursor present)
      obtain ⟨rawKeys, rawComputed⟩ :=
        input.exists_mapM_buildKey_of_forall target view keyFuel [] cursors
          (keyComplete [])
      have topologyPresent :
          (input.localizedRule3CoupledTopologyResolution? rawKeys).isSome = true :=
        (input.localizedRule3CoupledTopologyResolution?_isSome_iff_unambiguous rawKeys).mpr
          (unambiguous rawKeys rawComputed)
      obtain ⟨topology, topologyComputed⟩ :=
        Option.isSome_iff_exists.mp topologyPresent
      let coupled := topology.isCoupled
      let excluded :=
        input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
      obtain ⟨keys, keysComputed⟩ :=
        input.exists_mapM_buildKey_of_forall target view keyFuel excluded cursors
          (keyComplete excluded)
      refine ⟨
        { rawKeys
          coupled
          excluded
          keys }, ?_⟩
      simp [buildLocalizedDescriptorBearingRule3Frame?, rawComputed,
        topologyComputed, coupled, excluded, keysComputed]

/-- Compatibility with the older reachable-support premise: if every valid, budget-covered query
has executable node support through a finite bound, then every valid, budget-covered cursor has
the new demand-sensitive key support at that bound.  The child recursion is discharged by the
strictly decreasing reroot budget, which is exactly why the reachable-support premise is strong
enough at each demanded index. -/
theorem LocalizedDescriptorBearingRule3ReachableSupportThrough.keyDemandSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (support : input.LocalizedDescriptorBearingRule3ReachableSupportThrough
      target view maximumFuel) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      fuel ≤ maximumFuel →
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ fuel →
      input.LocalizedRule3KeyDemandSupport target view fuel cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor bounded valid covered
      have nodeSupport := support 0 bounded cursor valid covered
      change ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge
        cursor.occurrence at nodeSupport
      exact ⟨valid, covered, nodeSupport⟩
  | succ fuel ih =>
      intro cursor bounded valid covered
      have nodeSupport := support (fuel + 1) bounded cursor valid covered
      have childDemand : ∀ children,
          input.DeclarativeLocalizedRerootChildren cursor children →
          ∀ child ∈ children,
            input.LocalizedRule3KeyDemandSupport target view fuel child := by
        intro children childrenDerived child present
        have childValid := input.localizedRerootChild_valid
          cursor child children childrenDerived present
        have childBounded : input.localizedRerootCursorBudget child ≤ fuel := by
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid childrenDerived present
          omega
        exact ih child (by omega) childValid childBounded
      exact ⟨valid, covered, nodeSupport, childDemand⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
