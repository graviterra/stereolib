import TetraStereo.OneCenter.AuthoritativeSemanticMancudePerceptionBoundary
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceFuelCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6InitialPartitionTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical Rule-3 fuel completeness

The finite reroot carrier already supplies a strictly decreasing cursor budget.  This file proves
that the same explicit `2 * (carrierFuel + 1)` bound is sufficient for both passes of the
source-canonical Rule-3 compiler whenever every genuine Rule-3 node has a resolved tri-state
spatial observation.  The only remaining frame-level refusal is then the chemically meaningful
one: an ambiguous coupled physical-unit topology.
-/

/-- Every node in the finite source-canonical carrier has a resolved Rule-3 tri-state reading. -/
def AromaticCanonicalRule3SpatiallyResolved
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) : Prop :=
  ∀ occurrence : source.AromaticCanonicalOccurrence carrierFuel,
    ∃ outcome, source.aromaticCanonicalRule3SpatialNode? occurrence.1.node = some outcome

/-- Structural nonunits compute to the resolved negative Rule-3 outcome.  Thus `none` is reserved
for a genuine ordinary double-bond unit whose required spatial evidence is missing. -/
theorem aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (notEdge : ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node) :
    source.aromaticCanonicalRule3SpatialNode? node = some none := by
  classical
  unfold aromaticCanonicalRule3SpatialNode?
  by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real]
    cases currentComputed : node.current? with
    | none => simp
    | some current =>
        cases parentComputed : node.parent? with
        | none => simp
        | some parent =>
            have notOrdinary :
                ¬ source.AromaticCanonicalOrdinaryDoubleBond parent current := by
              intro ordinary
              exact notEdge ⟨real, current, parent,
                currentComputed, parentComputed, ordinary⟩
            simp [notOrdinary]
  · simp [real]

/-- Chemical Rule-3 evidence is complete on the carrier exactly when every genuine ordinary
double-bond node has a positive resolved spatial reading. -/
def AromaticCanonicalRule3GeometryResolved
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) : Prop :=
  ∀ occurrence : source.AromaticCanonicalOccurrence carrierFuel,
    source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge occurrence.1.node →
      ∃ result, source.aromaticCanonicalRule3SpatialNode? occurrence.1.node =
        some (some result)

/-- The positive-evidence formulation is exactly the tri-state resolvedness used by recursion. -/
theorem aromaticCanonicalRule3GeometryResolved_iff_spatiallyResolved
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) :
    source.AromaticCanonicalRule3GeometryResolved carrierFuel ↔
      source.AromaticCanonicalRule3SpatiallyResolved carrierFuel := by
  constructor
  · intro geometry occurrence
    by_cases edge : source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge
        occurrence.1.node
    · obtain ⟨result, computed⟩ := geometry occurrence edge
      exact ⟨some result, computed⟩
    · exact ⟨none,
        source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge
          occurrence.1.node edge⟩
  · intro resolved occurrence edge
    obtain ⟨outcome, computed⟩ := resolved occurrence
    cases outcome with
    | none =>
        exact (source.aromaticCanonicalRule3SpatialNode?_eq_some_none_implies_not_edge
          occurrence.1.node computed edge).elim
    | some result => exact ⟨result, computed⟩

/-- Every cursor in the first ligand frame is path-valid: it was reached from the valid
no-incoming-edge cursor at the final occurrence. -/
theorem aromaticCanonicalOccurrenceLigandFrame_cursor_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (computed : source.aromaticCanonicalOccurrenceLigandFrame? target = some roots) :
    ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor := by
  have derived := source.aromaticCanonicalOccurrenceLigandFrame?_sound
    target roots computed
  intro cursor present
  exact source.aromaticCanonicalRerootChild_valid
    { occurrence := target, previous? := none } cursor roots derived present

private theorem exists_mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_of_forall
    (source : AuthoritativeChemicalInput) {carrierFuel evaluationFuel : Nat} :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalUncancelledRule3SpatialKey? evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_of_forall
          cursors (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- The uncancelled Rule-3 recursion succeeds whenever the decreasing cursor budget is covered. -/
theorem exists_buildAromaticCanonicalUncancelledRule3SpatialKey?_of_budget_le
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel) :
    ∀ evaluationFuel (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.AromaticCanonicalRerootCursorValid cursor →
      source.aromaticCanonicalRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, source.buildAromaticCanonicalUncancelledRule3SpatialKey?
        evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenDerived := source.aromaticCanonicalRerootChildren_sound cursor
      obtain ⟨observation, observationComputed⟩ := resolved cursor.occurrence
      by_cases empty : children = []
      · refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }, ?_⟩
        simp [buildAromaticCanonicalUncancelledRule3SpatialKey?, children,
          observationComputed, empty]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := source.aromaticCanonicalRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenDerived := source.aromaticCanonicalRerootChildren_sound cursor
      obtain ⟨observation, observationComputed⟩ := resolved cursor.occurrence
      by_cases empty : children = []
      · refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }, ?_⟩
        simp [buildAromaticCanonicalUncancelledRule3SpatialKey?, children,
          observationComputed, empty]
      · have childComplete : ∀ child ∈ children, ∃ key,
            source.buildAromaticCanonicalUncancelledRule3SpatialKey?
              evaluationFuel child = some key := by
          intro child present
          have childValid := source.aromaticCanonicalRerootChild_valid
            cursor child children childrenDerived present
          have decreases := source.aromaticCanonicalRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply source.exists_buildAromaticCanonicalUncancelledRule3SpatialKey?_of_budget_le
            resolved evaluationFuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          source.exists_mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_of_forall
            children childComplete
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
        simp [buildAromaticCanonicalUncancelledRule3SpatialKey?, children,
          observationComputed, empty, childKeysComputed, compare, sorted]

/-- The uniform finite bound covers every path-valid uncancelled Rule-3 cursor. -/
theorem exists_buildAromaticCanonicalUncancelledRule3SpatialKey?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalUncancelledRule3SpatialKey?
      (2 * (carrierFuel + 1)) cursor = some key := by
  apply source.exists_buildAromaticCanonicalUncancelledRule3SpatialKey?_of_budget_le
    resolved (2 * (carrierFuel + 1)) cursor valid
  exact source.aromaticCanonicalRerootCursorBudget_le_twice cursor

/-- A resolved original node remains resolved after any fixed physical-unit exclusion policy. -/
theorem exists_aromaticCanonicalRule3SpatialNodeExcept_of_resolved
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (occurrence : source.AromaticCanonicalOccurrence carrierFuel) :
    ∃ outcome, source.aromaticCanonicalRule3SpatialNodeExcept?
      excluded occurrence.1.node = some outcome := by
  obtain ⟨outcome, computed⟩ := resolved occurrence
  unfold aromaticCanonicalRule3SpatialNodeExcept?
  rw [computed]
  cases outcome with
  | none => exact ⟨none, rfl⟩
  | some result =>
      by_cases omitted : result.physicalUnitId ∈ excluded
      · exact ⟨none, by simp [omitted]⟩
      · exact ⟨some result, by simp [omitted]⟩

private theorem exists_mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_of_forall
    (source : AuthoritativeChemicalInput) {carrierFuel evaluationFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        source.buildAromaticCanonicalRule3SpatialKeyExcept?
          excluded evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRule3SpatialKeyExcept?
          excluded evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_of_forall
          excluded cursors (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- The fixed-exclusion second Rule-3 pass has the same structural completeness bound. -/
theorem exists_buildAromaticCanonicalRule3SpatialKeyExcept?_of_budget_le
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    ∀ evaluationFuel (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.AromaticCanonicalRerootCursorValid cursor →
      source.aromaticCanonicalRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, source.buildAromaticCanonicalRule3SpatialKeyExcept?
        excluded evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenDerived := source.aromaticCanonicalRerootChildren_sound cursor
      obtain ⟨observation, observationComputed⟩ :=
        source.exists_aromaticCanonicalRule3SpatialNodeExcept_of_resolved
          resolved excluded cursor.occurrence
      by_cases empty : children = []
      · refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }, ?_⟩
        simp [buildAromaticCanonicalRule3SpatialKeyExcept?, children,
          observationComputed, empty]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := source.aromaticCanonicalRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenDerived := source.aromaticCanonicalRerootChildren_sound cursor
      obtain ⟨observation, observationComputed⟩ :=
        source.exists_aromaticCanonicalRule3SpatialNodeExcept_of_resolved
          resolved excluded cursor.occurrence
      by_cases empty : children = []
      · refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }, ?_⟩
        simp [buildAromaticCanonicalRule3SpatialKeyExcept?, children,
          observationComputed, empty]
      · have childComplete : ∀ child ∈ children, ∃ key,
            source.buildAromaticCanonicalRule3SpatialKeyExcept?
              excluded evaluationFuel child = some key := by
          intro child present
          have childValid := source.aromaticCanonicalRerootChild_valid
            cursor child children childrenDerived present
          have decreases := source.aromaticCanonicalRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply source.exists_buildAromaticCanonicalRule3SpatialKeyExcept?_of_budget_le
            resolved excluded evaluationFuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          source.exists_mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_of_forall
            excluded children childComplete
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
        simp [buildAromaticCanonicalRule3SpatialKeyExcept?, children,
          observationComputed, empty, childKeysComputed, compare, sorted]

/-- The uniform finite bound covers every path-valid fixed-exclusion Rule-3 cursor. -/
theorem exists_buildAromaticCanonicalRule3SpatialKeyExcept?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRule3SpatialKeyExcept?
      excluded (2 * (carrierFuel + 1)) cursor = some key := by
  apply source.exists_buildAromaticCanonicalRule3SpatialKeyExcept?_of_budget_le
    resolved excluded (2 * (carrierFuel + 1)) cursor valid
  exact source.aromaticCanonicalRerootCursorBudget_le_twice cursor

/-- The sole non-structural frame-level applicability condition: the exhaustive coupled-unit
search returns either the ordinary case or one unique coupled topology, rather than ambiguity. -/
def AromaticCanonicalRule3TopologyUnambiguous
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) : Prop :=
  ∃ resolution, source.aromaticCanonicalRule3PhysicalTopologyResolution? keys =
    some resolution

/-- Independent uniqueness of the physical coupled-unit relation. -/
def DeclarativeAromaticCanonicalRule3TopologyUnambiguous
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) : Prop :=
  ∀ left right,
    source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys left →
    source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys right →
    left = right

private theorem mem_eraseDups_iff_for_rule3TopologyTotality
    {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) : ∀ values : List α, a ∈ values.eraseDups ↔ a ∈ values
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons]
      by_cases same : a = head
      · subst head
        simp
      · have filtered := mem_eraseDups_iff_for_rule3TopologyTotality
          a (tail.filter fun b => !b == head)
        simpa [same] using filtered
termination_by values => values.length
decreasing_by
  have filtered := List.length_filter_le (fun b => !b == head) tail
  simpa using Nat.lt_succ_of_le filtered

private theorem eraseDups_nodup_for_rule3TopologyTotality
    {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ values : List α, values.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [mem_eraseDups_iff_for_rule3TopologyTotality]
        simp
      · exact eraseDups_nodup_for_rule3TopologyTotality
          (tail.filter fun value => !value == head)
termination_by values => values.length
decreasing_by
  have filtered := List.length_filter_le (fun value => !value == head) tail
  simpa using Nat.lt_succ_of_le filtered

/-- Exhaustive coupled-pair candidates contain no duplicate physical pair. -/
theorem aromaticCanonicalRule3CoupledUnitPairCandidates_nodup
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    (source.aromaticCanonicalRule3CoupledUnitPairCandidates keys).Nodup := by
  let units := source.aromaticCanonicalRule3FramePhysicalUnits keys
  have unitsNodup : units.Nodup := by
    unfold units aromaticCanonicalRule3FramePhysicalUnits
    exact eraseDups_nodup_for_rule3TopologyTotality _
  unfold aromaticCanonicalRule3CoupledUnitPairCandidates
  change (units.flatMap fun first => units.map fun second =>
    ({ firstUnit := first, secondUnit := second } :
      source.AromaticCanonicalRule3CoupledUnitPair)).Nodup
  rw [List.nodup_flatMap]
  constructor
  · intro first _present
    exact unitsNodup.map (by
      intro left right equal
      exact congrArg AromaticCanonicalRule3CoupledUnitPair.secondUnit equal)
  · rw [List.nodup_iff_pairwise_ne] at unitsNodup
    apply unitsNodup.imp
    intro first second different
    rw [Function.onFun, List.disjoint_left]
    intro pair firstPresent secondPresent
    rcases List.mem_map.mp firstPresent with ⟨firstTail, _firstTailPresent, rfl⟩
    rcases List.mem_map.mp secondPresent with ⟨secondTail, _secondTailPresent, equal⟩
    exact different
      (congrArg AromaticCanonicalRule3CoupledUnitPair.firstUnit equal).symm

/-- Filtering the exhaustive duplicate-free candidates preserves duplicate-freedom. -/
theorem aromaticCanonicalRule3CoupledUnitPairs_nodup
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    (source.aromaticCanonicalRule3CoupledUnitPairs keys).Nodup := by
  classical
  unfold aromaticCanonicalRule3CoupledUnitPairs
  exact (source.aromaticCanonicalRule3CoupledUnitPairCandidates_nodup keys).filter _

/-- Executable topology acceptance is exactly independent uniqueness of the exhaustive coupled
physical-unit relation. -/
theorem aromaticCanonicalRule3TopologyUnambiguous_iff_declarative
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.AromaticCanonicalRule3TopologyUnambiguous keys ↔
      source.DeclarativeAromaticCanonicalRule3TopologyUnambiguous keys := by
  constructor
  · rintro ⟨resolution, computed⟩
    have derived := source.aromaticCanonicalRule3PhysicalTopologyResolution?_sound
      keys resolution computed
    intro left right leftDerived rightDerived
    cases derived with
    | ordinary absent => exact (absent left leftDerived).elim
    | coupled selectedDerived unique =>
        exact (unique left leftDerived).trans (unique right rightDerived).symm
  · intro unique
    unfold AromaticCanonicalRule3TopologyUnambiguous
    unfold aromaticCanonicalRule3PhysicalTopologyResolution?
    generalize foundIdentity :
      source.aromaticCanonicalRule3CoupledUnitPairs keys = found
    cases found with
    | nil => exact ⟨.ordinary, by simp⟩
    | cons first tail =>
        cases tail with
        | nil => exact ⟨.coupled first, by simp⟩
        | cons second rest =>
            have firstDerived :
                source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys first :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys first).mp (by
                rw [foundIdentity]
                simp)
            have secondDerived :
                source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys second :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys second).mp (by
                rw [foundIdentity]
                simp)
            have same : first = second := unique first second firstDerived secondDerived
            have nodup := source.aromaticCanonicalRule3CoupledUnitPairs_nodup keys
            rw [foundIdentity] at nodup
            simp [same] at nodup

private theorem exists_mapM_uncancelled_at_twice_of_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalUncancelledRule3SpatialKey?_at_twice
          resolved cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_uncancelled_at_twice_of_valid resolved cursors
          (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

private theorem exists_mapM_except_at_twice_of_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRule3SpatialKeyExcept?
          excluded (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalRule3SpatialKeyExcept?_at_twice
          resolved excluded cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_except_at_twice_of_valid resolved excluded cursors
          (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- Both Rule-3 passes and the common physical-unit frame succeed at the proved finite bound. -/
theorem exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor)
    (topology : ∀ rawKeys,
      cursors.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
        (2 * (carrierFuel + 1))) = some rawKeys →
      source.AromaticCanonicalRule3TopologyUnambiguous rawKeys) :
    ∃ frame, source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      (2 * (carrierFuel + 1)) cursors = some frame := by
  obtain ⟨rawKeys, rawComputed⟩ :=
    source.exists_mapM_uncancelled_at_twice_of_valid resolved cursors valid
  obtain ⟨resolution, resolutionComputed⟩ := topology rawKeys rawComputed
  let excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
  obtain ⟨keys, keysComputed⟩ :=
    source.exists_mapM_except_at_twice_of_valid resolved excluded cursors valid
  exact ⟨{ rawKeys, resolution, excluded, keys }, by
    simp [buildAromaticCanonicalRule3CanonicalKeyFrame?, rawComputed,
      resolutionComputed, excluded, keysComputed]⟩

private theorem exists_mapM_rule45_at_twice_of_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key?
          target view (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_rule45_at_twice_of_valid target view cursors
          (fun child present => valid child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

private theorem exists_mapM_rule3Through5Except_at_twice_of_valid
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
          excluded target view (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨rule3, rule3Computed⟩ :=
        source.exists_buildAromaticCanonicalRule3SpatialKeyExcept?_at_twice
          resolved excluded cursor (valid cursor (by simp))
      obtain ⟨rule45, rule45Computed⟩ :=
        source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_rule3Through5Except_at_twice_of_valid
          resolved excluded target view cursors
          (fun child present => valid child (by simp [present]))
      refine ⟨{ rule3, rule45 } :: keys, ?_⟩
      simp [buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?,
        rule3Computed, rule45Computed, keysComputed]

/-- At the uniform finite bound, lower Rules-1a--5 root inputs follow from four valid cursors,
resolved Rule-3 observations, and unambiguous physical topology.  No recursive-builder success
premise remains. -/
theorem aromaticCanonicalRule3Through5RootInputsResolved_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor)
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (topology : ∀ rawKeys,
      roots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
        (2 * (carrierFuel + 1))) = some rawKeys →
      source.AromaticCanonicalRule3TopologyUnambiguous rawKeys) :
    source.AromaticCanonicalRule3Through5RootInputsResolved
      target view (2 * (carrierFuel + 1)) roots := by
  obtain ⟨rule3Frame, rule3Computed⟩ :=
    source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_at_twice
      resolved roots valid topology
  obtain ⟨keys, keysComputed⟩ :=
    source.exists_mapM_rule3Through5Except_at_twice_of_valid
      resolved rule3Frame.excluded target view roots valid
  exact ⟨rootsLength, rule3Frame, keys, rule3Computed, keysComputed⟩

/-! ## Sources without ordinary double bonds

For an all-single-bond source, Rule 3 has no geometric units to resolve or couple.  The following
theorems discharge both residual Rule-3 premises of the uniform partition-totality theorem in one
source-level step. -/

/-- A source with no ordinary double bond resolves every Rule-3 carrier node to the structural
nonunit outcome. -/
theorem aromaticCanonicalRule3SpatiallyResolved_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (carrierFuel : Nat) :
    source.AromaticCanonicalRule3SpatiallyResolved carrierFuel := by
  intro occurrence
  refine ⟨none,
    source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge
      occurrence.1.node ?_⟩
  rintro ⟨_real, current, parent, _currentComputed, _parentComputed, ordinary⟩
  exact noDouble parent current ordinary

private theorem declarativeRule3SpatialNodeOutcome_eq_none_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {outcome : Option source.AromaticCanonicalRule3SpatialNodeResult}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialNodeOutcome node outcome) :
    outcome = none := by
  cases derived with
  | structuralNonunit => rfl
  | @geometry result observed =>
      rcases observed with ⟨_real, _current, _parent, ordinary, _unit⟩
      exact (noDouble result.left result.right ordinary).elim

private theorem foldl_max_observation_lengths_eq_zero
    {source : AuthoritativeChemicalInput}
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (empty : ∀ key ∈ keys, key.observations = []) :
    keys.foldl (fun longest child => max longest child.observations.length) 0 = 0 := by
  induction keys with
  | nil => rfl
  | cons head tail ih =>
      have headEmpty := empty head (by simp)
      simp [headEmpty]
      exact ih (fun key present => empty key (by simp [present]))

private theorem mergeAromaticCanonicalRule3ObservationChildren_eq_nil
    {source : AuthoritativeChemicalInput}
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (empty : ∀ key ∈ keys, key.observations = []) :
    mergeAromaticCanonicalRule3ObservationChildren keys = [] := by
  unfold mergeAromaticCanonicalRule3ObservationChildren
  rw [show aromaticCanonicalRule3ObservationChildLayerCount keys = 0 by
    exact foldl_max_observation_lengths_eq_zero keys empty]
  rfl

private theorem declarativeUncancelledRule3SpatialKeyList_observations_eq_nil_of_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
      fuel cursors keys) :
    ∀ key ∈ keys, key.observations = [] := by
  refine DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList.rec
    (motive_1 := fun _fuel _cursor key _derived => key.observations = [])
    (motive_2 := fun _fuel _cursors keys _derived =>
      ∀ key ∈ keys, key.observations = [])
    ?_ ?_ ?_ ?_ ?_ derived
  · intro cursor children observation frame terminal observed
    have observationEmpty :=
      source.declarativeRule3SpatialNodeOutcome_eq_none_of_noDouble noDouble observed
    subst observation
    rfl
  · intro fuel cursor children observation frame terminal observed
    have observationEmpty :=
      source.declarativeRule3SpatialNodeOutcome_eq_none_of_noDouble noDouble observed
    subst observation
    rfl
  · intro fuel cursor children observation childKeys sorted frame nonterminal observed
      childrenDerived permutation descending childrenEmpty
    have observationEmpty :=
      source.declarativeRule3SpatialNodeOutcome_eq_none_of_noDouble noDouble observed
    subst observation
    simp only [aromaticCanonicalRule3RootObservations, List.nil_append]
    apply mergeAromaticCanonicalRule3ObservationChildren_eq_nil sorted
    intro child present
    exact childrenEmpty child (permutation.mem_iff.mp present)
  · intro fuel
    simp
  · intro fuel cursor cursors headKey tailKeys head tail headEmpty tailEmpty key present
    simp only [List.mem_cons] at present
    rcases present with rfl | present
    · exact headEmpty
    · exact tailEmpty key present

private theorem flatMap_eq_nil_of_forall_eq_nil
    {alpha beta : Type*} (f : alpha → List beta) :
    ∀ (values : List alpha), (∀ value ∈ values, f value = []) →
      values.flatMap f = []
  | [], _ => rfl
  | head :: tail, empty => by
      rw [List.flatMap_cons, empty head (by simp)]
      simp only [List.nil_append]
      exact flatMap_eq_nil_of_forall_eq_nil f tail
        (fun value present => empty value (by simp [present]))

/-- Successful uncancelled Rule-3 compilation on an all-single-bond source has no observations,
no physical units, and therefore a unique (empty) topology. -/
theorem mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_noDouble
    (source : AuthoritativeChemicalInput)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    {carrierFuel fuel : Nat}
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rawKeys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : cursors.mapM
      (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) = some rawKeys) :
    (∀ key ∈ rawKeys,
      key.observations = [] ∧
        source.aromaticCanonicalRule3PhysicalUnitIds key = []) ∧
      source.aromaticCanonicalRule3FramePhysicalUnits rawKeys = [] ∧
      source.AromaticCanonicalRule3TopologyUnambiguous rawKeys := by
  have observationsEmpty : ∀ key ∈ rawKeys, key.observations = [] :=
    source.declarativeUncancelledRule3SpatialKeyList_observations_eq_nil_of_noDouble
      noDouble
      (source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound_list
        cursors rawKeys computed)
  have unitsEmpty : ∀ key ∈ rawKeys,
      source.aromaticCanonicalRule3PhysicalUnitIds key = [] := by
    intro key present
    simp [aromaticCanonicalRule3PhysicalUnitIds, observationsEmpty key present]
  have flattenedUnitsEmpty :
      rawKeys.flatMap source.aromaticCanonicalRule3PhysicalUnitIds = [] := by
    exact flatMap_eq_nil_of_forall_eq_nil
      source.aromaticCanonicalRule3PhysicalUnitIds rawKeys unitsEmpty
  have frameUnitsEmpty :
      source.aromaticCanonicalRule3FramePhysicalUnits rawKeys = [] := by
    unfold aromaticCanonicalRule3FramePhysicalUnits
    rw [flattenedUnitsEmpty]
    rfl
  refine ⟨?_, frameUnitsEmpty, ?_⟩
  · intro key present
    exact ⟨observationsEmpty key present, unitsEmpty key present⟩
  · apply (source.aromaticCanonicalRule3TopologyUnambiguous_iff_declarative rawKeys).mpr
    intro left right leftDerived _rightDerived
    have impossible : False := by
      have firstPresent := leftDerived.1
      rw [frameUnitsEmpty] at firstPresent
      simp at firstPresent
    exact impossible.elim

/-- For a four-root, path-valid frame in an all-single-bond source, the entire canonical
Rules-1a--5 root input is total at the uniform fuel bound.  Callers no longer prove Rule-3
resolvedness and physical-topology uniqueness separately. -/
theorem aromaticCanonicalRule3Through5RootInputsResolved_at_twice_of_noDouble
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (valid : ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor) :
    source.AromaticCanonicalRule3Through5RootInputsResolved
      target view (2 * (carrierFuel + 1)) roots := by
  apply source.aromaticCanonicalRule3Through5RootInputsResolved_at_twice
    target view roots rootsLength valid
    (source.aromaticCanonicalRule3SpatiallyResolved_of_noDouble noDouble carrierFuel)
  intro rawKeys computed
  exact (source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_noDouble
    noDouble roots rawKeys computed).2.2

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
