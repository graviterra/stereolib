import TetraStereo.OneCenter.LocalizedShortCircuitReadiness
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private theorem mapM_exists_of_total {α β : Type} (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, total => by
      obtain ⟨result, head⟩ := total value (by simp)
      obtain ⟨results, tail⟩ := mapM_exists_of_total f values
        (fun value present => total value (by simp [present]))
      exact ⟨result :: results, by simp [head, tail]⟩

/-- A carrier certificate checked from finite local topology, strict constitutional comparisons and
geometry removes recursive endpoint calls. Key construction then has the structural tree bound,
uniformly in the auxiliary view and the coupled-unit exclusion list. -/
theorem exists_shortCircuitRule3Key_of_budget_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor < fuel →
      ∃ key, input.buildLocalizedRerootShortCircuitRule3KeyExec?
        target view fuel excluded cursor = some key
  | 0, _, _, covered => by omega
  | fuel + 1, cursor, valid, covered => by
      let children := input.executableLocalizedRerootChildren cursor
      have childrenComputed : input.executableLocalizedRerootChildren? cursor = some children := rfl
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      obtain ⟨certificate, _⟩ := ready.ready cursor.occurrence
      let observation := certificate.observation excluded
      have nodeComputed := certificate.computed target view
        (input.buildLocalizedShortCircuitRule3FrameExec? target view fuel) excluded
      by_cases empty : children = []
      · refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }, ?_⟩
        simp [buildLocalizedRerootShortCircuitRule3KeyExec?, childrenComputed,
          nodeComputed, empty, observation]
      · have childComplete : ∀ child ∈ children, ∃ key,
            input.buildLocalizedRerootShortCircuitRule3KeyExec?
              target view fuel excluded child = some key := by
          intro child present
          have childValid := input.localizedRerootChild_valid
            cursor child children derived present
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid derived present
          apply input.exists_shortCircuitRule3Key_of_budget_lt
            ready target view excluded fuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ := mapM_exists_of_total
          (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view fuel excluded)
          children childComplete
        let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
        refine ⟨
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations observation ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities observation ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }, ?_⟩
        simp [buildLocalizedRerootShortCircuitRule3KeyExec?, childrenComputed,
          nodeComputed, empty, childKeysComputed, observation, sorted]

/-- The certified callback-free class needs only a linear key budget. -/
theorem exists_shortCircuitRule3Key_at_linear_bound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootShortCircuitRule3KeyExec?
      target view (2 * (carrierFuel + 1) + 1) excluded cursor = some key := by
  apply input.exists_shortCircuitRule3Key_of_budget_lt ready target view excluded _ cursor valid
  have bounded := input.localizedRerootCursorBudget_le_twice cursor
  omega

/-- At the linear frame budget both key passes are guaranteed. The only remaining frame failure
is the original coupled-topology ambiguity check; it is kept explicit, not silently waived. -/
theorem shortCircuitRule3Frame_at_linear_bound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedRule3CallbackFreeCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor) :
    ∃ rawKeys,
      cursors.mapM (input.buildLocalizedRerootShortCircuitRule3KeyExec?
        target view (2 * (carrierFuel + 1) + 1) []) = some rawKeys ∧
      ((∃ frame, input.buildLocalizedShortCircuitRule3FrameExec?
        target view (2 * (carrierFuel + 1) + 2) cursors = some frame) ↔
        ∃ topology, input.DeclarativeLocalizedRule3CoupledTopologyResolution rawKeys topology) := by
  obtain ⟨rawKeys, rawComputed⟩ := mapM_exists_of_total
    (input.buildLocalizedRerootShortCircuitRule3KeyExec?
      target view (2 * (carrierFuel + 1) + 1) []) cursors
    (fun cursor present => input.exists_shortCircuitRule3Key_at_linear_bound
      ready target view [] cursor (valid cursor present))
  refine ⟨rawKeys, rawComputed, ?_⟩
  constructor
  · rintro ⟨frame, computed⟩
    have step : 2 * (carrierFuel + 1) + 2 = (2 * (carrierFuel + 1) + 1) + 1 := by omega
    rw [step, buildLocalizedShortCircuitRule3FrameExec?, rawComputed] at computed
    cases topologyComputed : input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
    | none => simp [topologyComputed] at computed
    | some topology =>
        exact ⟨topology, (input.localizedRule3CoupledTopologyResolution?_eq_some_iff
          rawKeys topology).mp
          ((input.localizedRule3CoupledTopologyResolutionExec?_eq_original rawKeys).symm.trans
            topologyComputed)⟩
  · rintro ⟨topology, topologyDerived⟩
    have topologyComputed : input.localizedRule3CoupledTopologyResolutionExec? rawKeys =
        some topology := by
      rw [input.localizedRule3CoupledTopologyResolutionExec?_eq_original]
      exact (input.localizedRule3CoupledTopologyResolution?_eq_some_iff
        rawKeys topology).mpr topologyDerived
    let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
    obtain ⟨keys, keysComputed⟩ := mapM_exists_of_total
      (input.buildLocalizedRerootShortCircuitRule3KeyExec?
        target view (2 * (carrierFuel + 1) + 1) excluded) cursors
      (fun cursor present => input.exists_shortCircuitRule3Key_at_linear_bound
        ready target view excluded cursor (valid cursor present))
    refine ⟨{ rawKeys, coupled := topology.isCoupled, excluded, keys }, ?_⟩
    have step : 2 * (carrierFuel + 1) + 2 = (2 * (carrierFuel + 1) + 1) + 1 := by omega
    rw [step, buildLocalizedShortCircuitRule3FrameExec?, rawComputed]
    simp [topologyComputed, keysComputed, excluded]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
