import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Fuel completeness for descriptor-bearing Rule 3

Structural coverage, chemical evidence, and coupled-topology uniqueness remain separate.  The
former `ResolvedThrough` predicate quantified unrelated occurrences even at index zero and is
retained only as a documented superseded interface.  `ReachableSupportThrough` instead classifies
exactly the valid, budget-covered node queries made by the recursion into named supported chemical
cases, and is proved equivalent to reachable outer-option resolution.  A frame-specific
topology premise additionally rules out multiple independently valid coupled matchings.  Under
those premises, the already proved zipper budget supplies structural totality.  The conservative
square bound used by the replacement descriptor is then proved large enough for every path-valid
cursor in its four-ligand frame.
-/

namespace CertifiedLocalizedCIPInput

/-- Every descriptor-bearing Rule-3 node query through `maximumFuel` resolves. -/
def LocalizedDescriptorBearingRule3ResolvedThrough
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (maximumFuel : Nat) : Prop :=
  ∀ fuel, fuel ≤ maximumFuel →
    ∀ excluded occurrence,
      ∃ outcome, input.localizedDescriptorBearingRule3Node?
        target occurrence view fuel excluded = some outcome

/-- Every descriptor-bearing Rule-3 node query that can actually be reached by the valid reroot
recursion resolves.  Unlike `LocalizedDescriptorBearingRule3ResolvedThrough`, this does not ask
the zero-index structural reader to resolve an unrelated double-bond occurrence: the cursor's
proved structural budget must be covered by the queried index. -/
def LocalizedDescriptorBearingRule3ReachableResolvedThrough
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (maximumFuel : Nat) : Prop :=
  ∀ fuel, fuel ≤ maximumFuel →
    ∀ excluded cursor,
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ fuel →
      ∃ outcome, input.localizedDescriptorBearingRule3Node?
        target cursor.occurrence view fuel excluded = some outcome

/-- Explicit support for one fuel-indexed node query.  At zero, only a structural non-unit is
admissible.  At a successor, support is one of the chemically named cases exposed by
`LocalizedDescriptorBearingRule3NodeWithSupport`. -/
def LocalizedDescriptorBearingRule3NodeSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Nat → Prop
  | 0 => ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  | fuel + 1 =>
      input.LocalizedDescriptorBearingRule3NodeWithSupport target view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) occurrence

/-- Every structurally reachable node query through the bound belongs to an explicitly supported
chemical case.  The physical-unit exclusion list does not occur here because, once a unit has
been compiled, deciding whether it has already been observed is total. -/
def LocalizedDescriptorBearingRule3ReachableSupportThrough
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (maximumFuel : Nat) : Prop :=
  ∀ fuel, fuel ≤ maximumFuel →
    ∀ cursor,
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ fuel →
      input.LocalizedDescriptorBearingRule3NodeSupport
        target cursor.occurrence view fuel

/-- Explicit support of all reachable node queries implies executable outer-option resolution. -/
theorem LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (support : input.LocalizedDescriptorBearingRule3ReachableSupportThrough
      target view maximumFuel) :
    input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
      target view maximumFuel := by
  intro fuel bounded excluded cursor valid covered
  have supported := support fuel bounded cursor valid covered
  cases fuel with
  | zero =>
      change ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence at supported
      exact ⟨none, by
        simp [localizedDescriptorBearingRule3Node?,
          localizedDescriptorBearingRule3StructuralNode?, supported]⟩
  | succ keyFuel =>
      change input.LocalizedDescriptorBearingRule3NodeWithSupport target view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel)
        cursor.occurrence at supported
      exact input.exists_localizedDescriptorBearingRule3NodeWith?_of_support
        target cursor.occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel)
        excluded supported

/-- Reachable executable resolution and the explicit chemical support classification are
equivalent.  The reverse direction needs only the empty exclusion list because unit exclusion can
change the inner result but cannot make a supported node's outer option fail. -/
theorem localizedDescriptorBearingRule3ReachableResolvedThrough_iff_support
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
        target view maximumFuel ↔
      input.LocalizedDescriptorBearingRule3ReachableSupportThrough
        target view maximumFuel := by
  constructor
  · intro resolved fuel bounded cursor valid covered
    obtain ⟨outcome, computed⟩ := resolved fuel bounded [] cursor valid covered
    cases fuel with
    | zero =>
        change input.localizedDescriptorBearingRule3StructuralNode? cursor.occurrence =
          some outcome at computed
        exact (input.localizedDescriptorBearingRule3StructuralNode?_sound
          cursor.occurrence outcome computed).2
    | succ keyFuel =>
        change input.localizedDescriptorBearingRule3NodeWith?
          target cursor.occurrence view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel) [] =
            some outcome at computed
        exact (input.exists_localizedDescriptorBearingRule3NodeWith?_iff_support
          target cursor.occurrence view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel) []).mp
            ⟨outcome, computed⟩
  · exact fun support =>
      LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved
        input target view support

/-- At positive key fuel, reachable resolution of a ring-closing query supplies exactly one of
the two supported P-93 outcomes: a proved permanent omission, or a successfully compiled required
cyclic `E/Z` descriptor.  Fully cyclic cumulenes, policy gaps, and nonmonocyclic ring systems do
not satisfy this support premise and therefore cannot hide behind the outer-option existential. -/
theorem LocalizedDescriptorBearingRule3ReachableResolvedThrough.ringClosure_supported
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
      target view maximumFuel)
    (keyFuel : Nat) (bounded : keyFuel + 1 ≤ maximumFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (covered : input.localizedRerootCursorBudget cursor ≤ keyFuel + 1)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (entryComputed : input.localizedRule3CumulatedAxisEntry? cursor.occurrence =
      some (.ringClosure initial closure)) :
    (∃ routeInitial routeClosure policyResult,
        input.localizedRule3CyclicAuthorityRoute? cursor.occurrence =
          some (.ordinaryMonocyclicPolicy routeInitial routeClosure policyResult) ∧
        policyResult.policy = .permanentlyOmit) ∨
      ∃ result,
        input.localizedRule3RequiredMonocyclicEZWith?
          target cursor.occurrence view
            (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel) =
          some result := by
  have support :=
    (input.localizedDescriptorBearingRule3ReachableResolvedThrough_iff_support
      target view).mp resolved (keyFuel + 1) bounded cursor valid covered
  exact (input.localizedDescriptorBearingRule3NodeWithSupport_of_ringClosure_iff
    target cursor.occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel)
      initial closure entryComputed).mp support

/-- At positive key fuel, reachable resolution of a branched non-chain query supplies exactly the
individual-double-bond geometry required by the P-93 branch route.  The theorem does not assert
that every branched bond is stereogenic; it exposes that condition as the necessary support
certificate. -/
theorem LocalizedDescriptorBearingRule3ReachableResolvedThrough.branched_individual_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
      target view maximumFuel)
    (keyFuel : Nat) (bounded : keyFuel + 1 ≤ maximumFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (covered : input.localizedRerootCursorBudget cursor ≤ keyFuel + 1)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (first second : input.LocalizedRerootCursor carrierFuel)
    (rest : List (input.LocalizedRerootCursor carrierFuel))
    (entryComputed : input.localizedRule3CumulatedAxisEntry? cursor.occurrence =
      some (.branched initial first second rest)) :
    ∃ result,
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
        target cursor.occurrence view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel) =
        some result := by
  have support :=
    (input.localizedDescriptorBearingRule3ReachableResolvedThrough_iff_support
      target view).mp resolved (keyFuel + 1) bounded cursor valid covered
  exact (input.localizedDescriptorBearingRule3NodeWithSupport_of_branched_iff
    target cursor.occurrence view
    (input.buildLocalizedDescriptorBearingRule3Frame? target view keyFuel)
    initial first second rest entryComputed).mp support

/-- The former all-occurrence premise is sufficient for the exact reachable-query premise. -/
theorem LocalizedDescriptorBearingRule3ResolvedThrough.reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ResolvedThrough
      target view maximumFuel) :
    input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
      target view maximumFuel := by
  intro fuel bounded excluded cursor _valid _covered
  exact resolved fuel bounded excluded cursor.occurrence

/-- The old all-occurrence premise is inconsistent as soon as the carrier contains a real
order-two parent/current edge: its fuel-zero obligation asks the structural base reader to
resolve a geometrical node that it intentionally rejects. -/
theorem not_localizedDescriptorBearingRule3ResolvedThrough_of_doubleBondEdge
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :
    ¬ input.LocalizedDescriptorBearingRule3ResolvedThrough
      target view maximumFuel := by
  intro resolved
  obtain ⟨outcome, computed⟩ := resolved 0 (Nat.zero_le maximumFuel) [] occurrence
  change input.localizedDescriptorBearingRule3StructuralNode? occurrence =
    some outcome at computed
  simp [localizedDescriptorBearingRule3StructuralNode?, edge] at computed

/-- The raw pass at a frame index has no ambiguous exhaustive coupled topology.  This premise is
kept separate from node/geometry resolution because ambiguity is a chemically meaningful refusal,
not a lack of recursion fuel. -/
def LocalizedDescriptorBearingRule3FrameTopologyResolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List (input.LocalizedRerootCursor carrierFuel) → Prop
  | 0, _cursors => False
  | fuel + 1, cursors =>
      ∀ rawKeys,
        cursors.mapM
          (input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view fuel []) = some rawKeys →
        ∃ topology,
          input.localizedRule3CoupledTopologyResolution? rawKeys = some topology

private theorem exists_mapM_descriptorBearingRule3Key_of_forall
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
        input.exists_mapM_descriptorBearingRule3Key_of_forall
          target view fuel excluded cursors
          (fun child present => complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

private theorem length_eq_of_mapM_eq_some
    {Input Output : Type} (f : Input → Option Output) :
    ∀ (inputs : List Input) (outputs : List Output),
      inputs.mapM f = some outputs → outputs.length = inputs.length
  | [], outputs, computed => by
      simp at computed
      subst outputs
      rfl
  | input :: inputs, outputs, computed => by
      cases outputComputed : f input with
      | none => simp [outputComputed] at computed
      | some output =>
          cases outputsComputed : inputs.mapM f with
          | none => simp [outputComputed, outputsComputed] at computed
          | some tail =>
              simp [outputComputed, outputsComputed] at computed
              subst outputs
              simp [length_eq_of_mapM_eq_some f inputs tail outputsComputed]

/-- Exhaustive coupled matching is a four-ligand policy.  Therefore every successful raw key
pass over a non-four-cursor frame resolves automatically to ordinary topology; no separate
ambiguity premise is needed. -/
theorem localizedDescriptorBearingRule3FrameTopologyResolved_of_length_ne_four
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (length : cursors.length ≠ 4) :
    input.LocalizedDescriptorBearingRule3FrameTopologyResolved
      target view (fuel + 1) cursors := by
  intro rawKeys rawComputed
  have sameLength : rawKeys.length = cursors.length :=
    length_eq_of_mapM_eq_some
      (input.buildLocalizedRerootDescriptorBearingRule3Key?
        target view fuel []) cursors rawKeys rawComputed
  have rawLength : rawKeys.length ≠ 4 := by
    rw [sameLength]
    exact length
  exact ⟨.ordinary,
    input.localizedRule3CoupledTopologyResolution?_eq_ordinary_of_length_ne_four
      rawKeys rawLength⟩

/-- A descriptor-bearing key succeeds when its cursor budget and node-resolution index are both
covered. -/
theorem exists_buildLocalizedRerootDescriptorBearingRule3Key?_of_budget_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
      target view maximumFuel) :
    ∀ evaluationFuel (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor carrierFuel),
      evaluationFuel ≤ maximumFuel →
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, input.buildLocalizedRerootDescriptorBearingRule3Key?
        target view evaluationFuel excluded cursor = some key
  | 0, excluded, cursor, bounded, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      obtain ⟨observation, observationComputed⟩ :=
        resolved 0 bounded excluded cursor valid covered
      change input.localizedDescriptorBearingRule3StructuralNode?
        cursor.occurrence = some observation at observationComputed
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
  | evaluationFuel + 1, excluded, cursor, bounded, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      obtain ⟨observation, observationComputed⟩ :=
        resolved (evaluationFuel + 1) bounded excluded cursor valid covered
      change input.localizedDescriptorBearingRule3NodeWith?
        target cursor.occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame?
          target view evaluationFuel) excluded = some observation at observationComputed
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
              target view evaluationFuel excluded child = some key := by
          intro child present
          have childValid := input.localizedRerootChild_valid
            cursor child children childrenDerived present
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply input.exists_buildLocalizedRerootDescriptorBearingRule3Key?_of_budget_le
            target view resolved evaluationFuel excluded child
          · omega
          · exact childValid
          · omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          input.exists_mapM_descriptorBearingRule3Key_of_forall
            target view evaluationFuel excluded children childComplete
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

/-- A two-pass frame succeeds whenever its predecessor key index covers every cursor budget. -/
theorem exists_buildLocalizedDescriptorBearingRule3Frame?_of_twice_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough
      target view maximumFuel)
    (frameFuel : Nat) (bounded : frameFuel ≤ maximumFuel)
    (covers : 2 * (carrierFuel + 1) < frameFuel)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (topologyResolved : input.LocalizedDescriptorBearingRule3FrameTopologyResolved
      target view frameFuel cursors)
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) :
    ∃ frame, input.buildLocalizedDescriptorBearingRule3Frame?
      target view frameFuel cursors = some frame := by
  cases frameFuel with
  | zero => omega
  | succ keyFuel =>
      have keyFuelBounded : keyFuel ≤ maximumFuel := by omega
      have keyComplete : ∀ excluded cursor, cursor ∈ cursors → ∃ key,
          input.buildLocalizedRerootDescriptorBearingRule3Key?
            target view keyFuel excluded cursor = some key := by
        intro excluded cursor present
        apply input.exists_buildLocalizedRerootDescriptorBearingRule3Key?_of_budget_le
          target view resolved keyFuel excluded cursor keyFuelBounded
          (valid cursor present)
        have cursorBound := input.localizedRerootCursorBudget_le_twice cursor
        omega
      obtain ⟨rawKeys, rawComputed⟩ :=
        input.exists_mapM_descriptorBearingRule3Key_of_forall
          target view keyFuel [] cursors (keyComplete [] )
      obtain ⟨topology, topologyComputed⟩ := topologyResolved rawKeys rawComputed
      let coupled := topology.isCoupled
      let excluded :=
        input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
      obtain ⟨keys, keysComputed⟩ :=
        input.exists_mapM_descriptorBearingRule3Key_of_forall
          target view keyFuel excluded cursors (keyComplete excluded)
      refine ⟨
        { rawKeys
          coupled
          excluded
          keys }, ?_⟩
      simp [buildLocalizedDescriptorBearingRule3Frame?, rawComputed,
        topologyComputed, coupled, excluded, keysComputed]

/-- The square budget used by the replacement descriptor covers every valid cursor, once all node
queries through that finite index have the required chemical evidence. -/
theorem exists_buildLocalizedDescriptorBearingRule3Frame?_at_conservativeFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (topologyResolved : input.LocalizedDescriptorBearingRule3FrameTopologyResolved
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors)
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) :
    ∃ frame, input.buildLocalizedDescriptorBearingRule3Frame?
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) cursors =
        some frame := by
  apply input.exists_buildLocalizedDescriptorBearingRule3Frame?_of_twice_lt
    target view resolved
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) (by rfl) _
    cursors topologyResolved valid
  unfold localizedDescriptorBearingRule3EvaluationFuel
  nlinarith

/-- A two-reference endpoint frame can never trigger four-ligand coupled ambiguity.  Hence node
resolution and cursor validity alone make the conservative descriptor-bearing frame total. -/
theorem exists_buildLocalizedDescriptorBearingRule3Frame?_two_at_conservativeFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
    (first second : input.LocalizedRerootCursor carrierFuel)
    (firstValid : input.LocalizedRerootCursorValid first)
    (secondValid : input.LocalizedRerootCursorValid second) :
    ∃ frame, input.buildLocalizedDescriptorBearingRule3Frame?
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      [first, second] = some frame := by
  apply input.exists_buildLocalizedDescriptorBearingRule3Frame?_at_conservativeFuel
    target view resolved [first, second]
  · apply input.localizedDescriptorBearingRule3FrameTopologyResolved_of_length_ne_four
    simp
  · intro cursor present
    simp at present
    rcases present with rfl | rfl
    · exact firstValid
    · exact secondValid

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
