import TetraStereo.Certificate.MandatoryDemand
import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery
import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedRule3MandatoryDemand

set_option autoImplicit false

/-!
# Mandatory-cycle refusal for the extended Rule-3 recursion

This module instantiates the generic refusal theory of
`TetraStereo.Certificate.MandatoryDemand` on the *actual* extended key / frame evaluator

* `buildLocalizedRerootExtendedShortCircuitRule3KeyExec?`
* `buildLocalizedExtendedShortCircuitRule3FrameExec?`

of `LocalizedRerootExtendedShortCircuitRule3Key`, against the actual preflight-pruned weighted
demand graph `preflightExtendedWeightedDemandGraph` of `LocalizedPreflightDemandDiscovery`.

The only semantic input discharged here is the local propagation obligation
`WeightedDemand.Propagates`: a successful key at budget `n` forces every mandatory dependency
(executable child or preflight-pruned callback request) to be successful at a strictly smaller
budget.  The proof follows the real evaluation order:

* a child of a successful budget-`n+1` key succeeds at budget `n`, because the key's
  `children.mapM` binds every child before the key can be assembled;
* a preflight callback request of a successful budget-`n+1` key is answered at budget `n`
  (`rule3PreflightExtendedNodeCallbackRequests_isSome_of_success`), and a successful frame at
  budget `n` forces every listed reference cursor through its *raw* pass at budget `n-1` with
  the empty exclusion list;
* at budget `0` the key only succeeds on a proved structural nonunit with no children, where the
  preflight request list is empty, so there are no mandatory successors at all.

No external propagation, acyclicity, rank table, desired descriptor or successful-callback
hypothesis enters any statement.  The molecular conclusions are exactly the generic theorems of
`MandatoryDemand` specialized to the evaluator:

* `extendedShortCircuitRule3Key_propagates` is the actual `WeightedDemand.Propagates` instance;
* a mandatory cycle makes the key refuse *every* budget;
* simultaneous key success of all requested roots forces the reachable graph to be acyclic;
* dually, a non-acyclic reachable graph forces the two-pass frame evaluator to return `none` at
  *every* budget (`extendedShortCircuitRule3Frame_none_of_not_acyclic`).
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand

/-! ## Generic mapM support -/

/-- If a `mapM` over an `Option`-valued function succeeds, every member maps to some value. -/
private theorem mapM_all_some {α β : Type} (f : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results → ∀ value ∈ values, ∃ output, f value = some output
  | [], _, _, value, present => by simp at present
  | a :: as, _, computed, value, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some b =>
        cases tailComputed : as.mapM f with
        | none => simp [headComputed, tailComputed] at computed
        | some tail =>
          rcases List.mem_cons.mp present with rfl | present
          · exact ⟨b, headComputed⟩
          · exact mapM_all_some f as tail tailComputed value present

/-- The total executable children expansion returns exactly the executable children list. -/
private theorem executableLocalizedRerootChildren?_some_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (computed : input.executableLocalizedRerootChildren? cursor = some children) :
    children = input.executableLocalizedRerootChildren cursor := by
  simpa [executableLocalizedRerootChildren?] using computed.symm

/-! ## The pruned request list is empty on structural nonunits -/

/-- A structural nonunit occurrence carries no preflight-pruned callback demand.  Both route
certificates require a real Rule-3 double-bond edge, and the original node fallback is empty
without one. -/
theorem rule3PreflightExtendedNodeCallbackRequests_eq_nil_of_not_edge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :
    input.rule3PreflightExtendedNodeCallbackRequests occurrence = [] := by
  simp [rule3PreflightExtendedNodeCallbackRequests, rule3NodeCallbackRequests,
    rule3OriginalNodeCallbackRequests, localizedRule3OddRouteCertificate?,
    localizedRule3OrdinaryRouteCertificate?, notEdge]

/-! ## Success at a budget -/

/-- A cursor is successful at a budget when some exclusion list and some recursive key are
produced by the actual extended key evaluator. -/
def successfulExtendedShortCircuitRule3Key
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (budget : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ (excluded : List input.LocalizedRule3PhysicalUnitId)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey),
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view budget excluded cursor = some key

/-! ## Propagation of success to smaller budgets -/

/-- At budget zero the evaluator is the structural base reader: it succeeds only on a terminal
structural nonunit, where the executable children and the preflight requests are both empty, so
there are no mandatory successors at all. -/
private theorem keyExec_zero_no_successors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view 0 excluded cursor = some key) :
    ∀ child : input.LocalizedRerootCursor carrierFuel,
      ¬ Edge (input.preflightExtendedWeightedDemandGraph carrierFuel) cursor child := by
  intro child edge
  change child ∈ input.executableLocalizedRerootChildren cursor ++
    (input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence).flatten at edge
  unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec? at computed
  cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
  | none => simp [childrenComputed] at computed
  | some children =>
    cases observationComputed : input.localizedRule3StructuralNodeExec cursor.occurrence with
    | none => simp [childrenComputed, observationComputed] at computed
    | some observation =>
      by_cases terminal : children = []
      · have children_eq : children = input.executableLocalizedRerootChildren cursor :=
          input.executableLocalizedRerootChildren?_some_eq cursor children childrenComputed
        have noDouble : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence := by
          intro doubleEdge
          have noneEq :=
            (input.localizedRule3StructuralNodeExec_eq_none_iff cursor.occurrence).mpr doubleEdge
          rw [noneEq] at observationComputed
          cases observationComputed
        have noRequests : input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence = [] :=
          input.rule3PreflightExtendedNodeCallbackRequests_eq_nil_of_not_edge
            cursor.occurrence noDouble
        rcases List.mem_append.mp edge with childEdge | requestEdge
        · have childInChildren : child ∈ children := children_eq.symm ▸ childEdge
          rw [terminal] at childInChildren
          simp at childInChildren
        · rw [noRequests] at requestEdge
          simp at requestEdge
      · simp [childrenComputed, observationComputed, terminal] at computed

/-- A child of a successful budget-`fuel+1` key succeeds at budget `fuel` with the same exclusion
list, because the key's `children.mapM` must bind every child before the key is assembled. -/
private theorem keyExec_succ_child_successful
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view (fuel + 1) excluded cursor = some key)
    (child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    input.successfulExtendedShortCircuitRule3Key target view fuel child := by
  unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec? at computed
  cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
  | none => simp [childrenComputed] at computed
  | some children =>
    cases observationComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target cursor.occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel) excluded with
    | none => simp [childrenComputed, observationComputed] at computed
    | some observation =>
      by_cases terminal : children = []
      · exfalso
        have childInChildren : child ∈ children :=
          (input.executableLocalizedRerootChildren?_some_eq cursor children childrenComputed).symm ▸ present
        rw [terminal] at childInChildren
        simp at childInChildren
      · cases childKeysComputed : children.mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel excluded) with
        | none => simp [childrenComputed, observationComputed, terminal, childKeysComputed] at computed
        | some childKeys =>
          have childInChildren : child ∈ children :=
            (input.executableLocalizedRerootChildren?_some_eq cursor children childrenComputed).symm ▸ present
          obtain ⟨childKey, childComputed⟩ := mapM_all_some
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel excluded)
            children childKeys childKeysComputed child childInChildren
          exact ⟨excluded, childKey, childComputed⟩

/-- A preflight request of a successful budget-`fuel+1` key is answered by the frame callback at
budget `fuel`, via the actual node success theorem of `LocalizedRule3MandatoryDemand`. -/
private theorem keyExec_succ_callback_frame_isSome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view (fuel + 1) excluded cursor = some key)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (requested : request ∈ input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence) :
    (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel request).isSome := by
  unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec? at computed
  cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
  | none => simp [childrenComputed] at computed
  | some children =>
    cases observationComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target cursor.occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel) excluded with
    | none => simp [childrenComputed, observationComputed] at computed
    | some observation =>
      exact input.rule3PreflightExtendedNodeCallbackRequests_isSome_of_success
        target cursor.occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
        excluded observation observationComputed request requested

/-- A successful two-pass frame at budget `fuel+1` succeeds on its raw pass, so every listed
cursor is a successful key at budget `fuel` with the empty exclusion list. -/
theorem extendedShortCircuitRule3Frame_some_rawKeys_successful
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view (fuel + 1) cursors = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ cursors) :
    input.successfulExtendedShortCircuitRule3Key target view fuel cursor := by
  unfold buildLocalizedExtendedShortCircuitRule3FrameExec? at computed
  cases rawComputed : cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel []) with
  | none => simp [rawComputed] at computed
  | some rawKeys =>
    obtain ⟨rawKey, rawComputed⟩ := mapM_all_some
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel [])
      cursors rawKeys rawComputed cursor present
    exact ⟨[], rawKey, rawComputed⟩

/-! ## The actual propagation instance -/

/-- The actual `WeightedDemand.Propagates` instance of the extended key evaluator against the
preflight-pruned weighted demand graph, for a fixed target and dependency view.  No external
propagation or acyclicity hypothesis is assumed. -/
theorem extendedShortCircuitRule3Key_propagates
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Propagates (input.preflightExtendedWeightedDemandGraph carrierFuel)
      (input.successfulExtendedShortCircuitRule3Key target view) := by
  intro n cursor hs child edge
  obtain ⟨excluded, key, computed⟩ := hs
  cases n with
  | zero =>
      exfalso
      exact input.keyExec_zero_no_successors target view excluded cursor key computed child edge
  | succ fuel =>
      change child ∈ input.executableLocalizedRerootChildren cursor ++
        (input.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence).flatten at edge
      rcases List.mem_append.mp edge with childEdge | requestEdge
      · exact ⟨fuel, Nat.lt_succ_self fuel,
          input.keyExec_succ_child_successful target view fuel excluded cursor key computed
            child childEdge⟩
      · obtain ⟨request, requested, present⟩ := List.mem_flatten.mp requestEdge
        have frameIsSome :
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
              target view fuel request).isSome :=
          input.keyExec_succ_callback_frame_isSome target view fuel excluded cursor key computed
            request requested
        obtain ⟨frame, frameComputed⟩ := Option.isSome_iff_exists.mp frameIsSome
        cases fuel with
        | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at frameComputed
        | succ fuel' =>
          have childSuccessful := input.extendedShortCircuitRule3Frame_some_rawKeys_successful
            target view fuel' request frame frameComputed child present
          exact ⟨fuel', by omega, childSuccessful⟩

/-! ## Key-level refusal and acyclicity corollaries -/

/-- A cursor on a nonempty mandatory cycle is refused by the key evaluator at every budget. -/
theorem extendedShortCircuitRule3Key_not_successful_of_cycle
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (cycle : Relation.TransGen
      (Edge (input.preflightExtendedWeightedDemandGraph carrierFuel)) cursor cursor) :
    ∀ budget, ¬ input.successfulExtendedShortCircuitRule3Key target view budget cursor :=
  not_successful_of_cycle (input.extendedShortCircuitRule3Key_propagates target view) cycle

/-- A root reaching a mandatory cycle is refused by the key evaluator at every budget. -/
theorem extendedShortCircuitRule3Key_not_successful_of_reachable_cycle
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {root cursor : input.LocalizedRerootCursor carrierFuel}
    (path : Relation.ReflTransGen
      (Edge (input.preflightExtendedWeightedDemandGraph carrierFuel)) root cursor)
    (cycle : Relation.TransGen
      (Edge (input.preflightExtendedWeightedDemandGraph carrierFuel)) cursor cursor) :
    ∀ budget, ¬ input.successfulExtendedShortCircuitRule3Key target view budget root :=
  not_successful_of_reachable_cycle
    (input.extendedShortCircuitRule3Key_propagates target view) path cycle

/-- Simultaneous success of every requested root forces the reachable preflight-pruned graph to be
acyclic. -/
theorem extendedShortCircuitRule3Key_acyclic_of_all_successful
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {roots : List (input.LocalizedRerootCursor carrierFuel)}
    (success : ∀ root ∈ roots, ∃ budget,
      input.successfulExtendedShortCircuitRule3Key target view budget root) :
    Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) roots :=
  acyclic_of_all_successful (input.extendedShortCircuitRule3Key_propagates target view) success

/-- If the reachable graph is not acyclic, some requested root is refused at every budget. -/
theorem extendedShortCircuitRule3Key_exists_unsuccessful_of_not_acyclic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {roots : List (input.LocalizedRerootCursor carrierFuel)}
    (notAcyclic : ¬ Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) roots) :
    ∃ root ∈ roots, ∀ budget,
      ¬ input.successfulExtendedShortCircuitRule3Key target view budget root :=
  exists_unsuccessful_of_not_acyclic
    (input.extendedShortCircuitRule3Key_propagates target view) notAcyclic

/-- A reachable mandatory cycle is a witness that some requested root is refused at every budget. -/
theorem extendedShortCircuitRule3Key_exists_unsuccessful_of_reachable_cycle
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {roots : List (input.LocalizedRerootCursor carrierFuel)}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (reachable : Reachable (input.preflightExtendedWeightedDemandGraph carrierFuel) roots cursor)
    (cycle : Relation.TransGen
      (Edge (input.preflightExtendedWeightedDemandGraph carrierFuel)) cursor cursor) :
    ∃ root ∈ roots, ∀ budget,
      ¬ input.successfulExtendedShortCircuitRule3Key target view budget root :=
  exists_unsuccessful_of_reachable_cycle
    (input.extendedShortCircuitRule3Key_propagates target view) reachable cycle

/-! ## Frame-level conclusions -/

/-- A successful two-pass frame at any budget makes every requested root successful at a smaller
budget, hence the reachable graph is acyclic. -/
theorem extendedShortCircuitRule3Frame_acyclic_of_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (succeeds : ∃ budget frame,
      input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view budget roots = some frame) :
    Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) roots := by
  obtain ⟨budget, frame, computed⟩ := succeeds
  cases budget with
  | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at computed
  | succ fuel =>
    apply input.extendedShortCircuitRule3Key_acyclic_of_all_successful target view
    intro root member
    exact ⟨fuel, input.extendedShortCircuitRule3Frame_some_rawKeys_successful
      target view fuel roots frame computed root member⟩

/-- The molecular refusal theorem: if the reachable preflight-pruned demand graph is not acyclic,
the two-pass extended frame evaluator returns `none` at *every* budget, for the fixed target and
dependency view and every exclusion-independent raw pass. -/
theorem extendedShortCircuitRule3Frame_none_of_not_acyclic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (notAcyclic : ¬ Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) roots) :
    ∀ budget, input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view budget roots = none := by
  obtain ⟨root, rootMember, rootNever⟩ :=
    exists_unsuccessful_of_not_acyclic
      (input.extendedShortCircuitRule3Key_propagates target view) notAcyclic
  intro budget
  cases budget with
  | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameExec?]
  | succ fuel =>
    cases frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view (fuel + 1) roots with
    | none => rfl
    | some frame =>
      have rawSuccess := input.extendedShortCircuitRule3Frame_some_rawKeys_successful
        target view fuel roots frame frameComputed root rootMember
      exact (rootNever fuel rawSuccess).elim

/-- Dual witness form: a mandatory cycle at a reachable cursor forces the two-pass frame to `none`
at every budget. -/
theorem extendedShortCircuitRule3Frame_none_all_budgets_of_reachable_cycle
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (reachable : Reachable (input.preflightExtendedWeightedDemandGraph carrierFuel) roots cursor)
    (cycle : Relation.TransGen
      (Edge (input.preflightExtendedWeightedDemandGraph carrierFuel)) cursor cursor) :
    ∀ budget, input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view budget roots = none := by
  exact input.extendedShortCircuitRule3Frame_none_of_not_acyclic target view roots
    (not_acyclic_of_reachable_cycle reachable cycle)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
