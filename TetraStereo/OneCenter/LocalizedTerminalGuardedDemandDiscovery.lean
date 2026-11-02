import TetraStereo.OneCenter.LocalizedTerminalGuardedRule3Node
import TetraStereo.OneCenter.LocalizedExtendedDemandDiscovery
import TetraStereo.Certificate.WeightedDemandGraph
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand


































































/-! ## The target/view-parametric guarded weighted demand graph -/

/-- The actual weighted demand graph of the terminal-guarded node evaluator.

Ordinary cut-neighborhood children are `executableLocalizedRerootChildren` and therefore cost
`1` in a checked `RankCertificate`; the callback requests are exactly
`rule3TerminalGuardedNodeCallbackRequests` for the supplied target and view and cost `2`,
including the empty-request frame step.  The graph is parameterized by the actual target and the
actual dependency view, because the guard and hence the pruned demand depend on both. -/
def terminalGuardedWeightedDemandGraph
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    Graph (input.LocalizedRerootCursor fuel) where
  children := fun cursor => input.executableLocalizedRerootChildren cursor
  requests := fun cursor =>
    TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests
      input target cursor.occurrence view

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph

@[simp] theorem terminalGuardedWeightedDemandGraph_children
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) :
    (terminalGuardedWeightedDemandGraph input target view).children cursor =
      input.executableLocalizedRerootChildren cursor := rfl

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph_children

@[simp] theorem terminalGuardedWeightedDemandGraph_requests
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) :
    (terminalGuardedWeightedDemandGraph input target view).requests cursor =
      TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests
        input target cursor.occurrence view := rfl

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph_requests

/-- The conservative successors of the guarded graph are exactly the executable structural
children followed by the flattened terminal-guarded callback requests. -/
theorem terminalGuardedWeightedDemandGraph_successors
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) :
    successors (terminalGuardedWeightedDemandGraph input target view) cursor =
      input.executableLocalizedRerootChildren cursor ++
        (TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests
          input target cursor.occurrence view).flatten := rfl

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph_successors

/-! ## Explicit weight retention -/

/-- A checked rank of the guarded graph charges exactly one fuel step for every actual executable
structural child. -/
theorem terminalGuardedRankCertificate_children_weight
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ certificate.vertices)
    (child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    child ∈ certificate.vertices ∧ certificate.height child + 1 ≤ certificate.height cursor :=
  certificate.children cursor member child (by
    simpa only [terminalGuardedWeightedDemandGraph_children] using present)

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedRankCertificate_children_weight

/-- A checked rank of the guarded graph charges exactly two fuel steps (one frame pass plus one
key pass) for every actual terminal-guarded callback request, including an empty request. -/
theorem terminalGuardedRankCertificate_callbacks_weight
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ certificate.vertices)
    (request : List (input.LocalizedRerootCursor fuel))
    (present : request ∈ TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests
      input target cursor.occurrence view) :
    (∀ reference ∈ request, reference ∈ certificate.vertices) ∧
      listHeight certificate.height request + 2 ≤ certificate.height cursor :=
  certificate.callbacks cursor member request (by
    simpa only [terminalGuardedWeightedDemandGraph_requests] using present)

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedRankCertificate_callbacks_weight

/-! ## Inclusion in the actual extended demand graph -/

/-- The guarded graph's request list at any cursor is a sublist of the existing extended-node
request list.  This is the exact request-level pruning statement: it retains every actual
request that the guarded evaluator can still perform (including real sibling requests) and only
removes the lists that the guard-accepted branch and the route fallback leave unused. -/
theorem terminalGuardedWeightedDemandGraph_requests_sublist
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) :
    ((terminalGuardedWeightedDemandGraph input target view).requests cursor).Sublist
      (input.rule3ExtendedNodeCallbackRequests cursor.occurrence) := by
  rw [terminalGuardedWeightedDemandGraph_requests]
  exact TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests_sublist
    input target cursor.occurrence view

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph_requests_sublist

/-- Every terminal-guarded request is an existing extended-node request at the same occurrence.
This is the pointwise form of
`rule3TerminalGuardedNodeCallbackRequests_sublist`, independent of the callback and of every
successful evaluation. -/
theorem terminalGuardedNodeCallbackRequests_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ∀ request ∈ TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests
        input target occurrence view,
      request ∈ input.rule3ExtendedNodeCallbackRequests occurrence :=
  fun _request requested =>
    (TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests_sublist
      input target occurrence view).subset requested

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedNodeCallbackRequests_subset

/-- Actual guarded callback edges, flattened, are members of the flattened extended request
list. -/
theorem terminalGuardedCallbackSuccessors_subset_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) :
    ∀ child ∈ (TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests
        input target cursor.occurrence view).flatten,
      child ∈ (input.rule3ExtendedNodeCallbackRequests cursor.occurrence).flatten := by
  intro child present
  exact flatten_subset_of_mem_subset
    (fun request requested =>
      terminalGuardedNodeCallbackRequests_subset input target view cursor.occurrence
        request requested)
    child present

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedCallbackSuccessors_subset_extended

/-- Every successor of the guarded graph is an extended-graph successor: the structural child
lists coincide and every guarded callback request was already an extended request. -/
theorem terminalGuardedWeightedDemandSuccessors_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) :
    ∀ child ∈ successors (terminalGuardedWeightedDemandGraph input target view) cursor,
      child ∈ input.extendedRule3DemandSuccessors cursor := by
  intro child present
  rw [terminalGuardedWeightedDemandGraph_successors] at present
  change child ∈ input.executableLocalizedRerootChildren cursor ++
    (input.rule3ExtendedNodeCallbackRequests cursor.occurrence).flatten
  rcases List.mem_append.mp present with childPresent | callbackPresent
  · exact List.mem_append_left _ childPresent
  · exact List.mem_append_right _
      (terminalGuardedCallbackSuccessors_subset_extended input target view cursor
        child callbackPresent)

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandSuccessors_subset

/-- Every edge of the guarded weighted graph is an actual extended demand edge. -/
theorem terminalGuardedWeightedEdge_subset_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    {parent child : input.LocalizedRerootCursor fuel}
    (edge : Edge (terminalGuardedWeightedDemandGraph input target view) parent child) :
    input.ExtendedRule3DemandEdge parent child :=
  terminalGuardedWeightedDemandSuccessors_subset input target view parent child edge

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedEdge_subset_extended

/-- Guarded reachability is contained in extended reachability, path by path. -/
theorem terminalGuardedWeightedReachable_subset_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (cursor : input.LocalizedRerootCursor fuel)
    (reachable : Reachable (terminalGuardedWeightedDemandGraph input target view) roots cursor) :
    input.ExtendedRule3DemandReachable roots cursor := by
  obtain ⟨root, member, path⟩ := reachable
  exact ⟨root, member, Relation.ReflTransGen.mono
    (fun _ _ edge => terminalGuardedWeightedEdge_subset_extended input target view edge) path⟩

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedReachable_subset_extended

/-- Acyclicity of the existing extended graph implies acyclicity of the guarded graph.  Only this
direction holds: the guard removes requests and therefore can only destroy cycles.  No claim is
made that removing one edge makes an arbitrary extended graph acyclic. -/
theorem terminalGuardedWeightedDemandAcyclic_of_extended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : input.ExtendedRule3DemandAcyclic roots) :
    Acyclic (terminalGuardedWeightedDemandGraph input target view) roots := by
  intro cursor reachable cycle
  exact acyclic cursor
    (terminalGuardedWeightedReachable_subset_extended input target view roots cursor reachable)
    (Relation.TransGen.mono
      (fun _ _ edge => terminalGuardedWeightedEdge_subset_extended input target view edge) cycle)

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandAcyclic_of_extended

/-! ## Exact zero demand at an actually accepted terminal guard -/

/-- At a cursor whose occurrence is an actually accepted terminal guard, the guarded graph
demands no callback at all.  The hypotheses are the actual branch facts: the odd route is absent,
the ordinary route certificate is present, the physical endpoint frame is computed, and the
executable guard `localizedRule3TerminalGuard?` returns a witness.  No callback value, successful
recursive key or frame is assumed. -/
theorem terminalGuardedWeightedDemandGraph_requests_eq_nil_of_guard
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (witness : TerminalGuardedRule3Node.LocalizedRule3TerminalGuardWitness
      input target view topology)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (guardComputed :
      TerminalGuardedRule3Node.localizedRule3TerminalGuard? input target view topology =
        some witness)
    (cursor : input.LocalizedRerootCursor fuel)
    (sameOccurrence : cursor.occurrence = occurrence) :
    (terminalGuardedWeightedDemandGraph input target view).requests cursor = [] := by
  rw [terminalGuardedWeightedDemandGraph_requests, sameOccurrence]
  exact TerminalGuardedRule3Node.rule3TerminalGuardedNodeCallbackRequests_eq_nil_of_guard
    input target occurrence view topology witness oddRoute ordinaryRoute topologyComputed
    guardComputed

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph_requests_eq_nil_of_guard

/-- At an actually accepted terminal guard the guarded graph's successor list is exactly the
executable structural child list: the callback part vanishes identically. -/
theorem terminalGuardedWeightedDemandGraph_successors_eq_children_of_guard
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (witness : TerminalGuardedRule3Node.LocalizedRule3TerminalGuardWitness
      input target view topology)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (guardComputed :
      TerminalGuardedRule3Node.localizedRule3TerminalGuard? input target view topology =
        some witness)
    (cursor : input.LocalizedRerootCursor fuel)
    (sameOccurrence : cursor.occurrence = occurrence) :
    successors (terminalGuardedWeightedDemandGraph input target view) cursor =
      input.executableLocalizedRerootChildren cursor := by
  unfold successors
  rw [terminalGuardedWeightedDemandGraph_children,
    terminalGuardedWeightedDemandGraph_requests_eq_nil_of_guard input target occurrence view
      topology witness oddRoute ordinaryRoute topologyComputed guardComputed cursor sameOccurrence,
    List.flatten_nil, List.append_nil]

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph_successors_eq_children_of_guard

/-- At an actually accepted terminal guard, an edge of the guarded graph is exactly a structural
child edge.  This is the graph-level face of the evaluator's zero callback demand. -/
theorem terminalGuardedWeightedEdge_iff_structural_of_guard
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (witness : TerminalGuardedRule3Node.LocalizedRule3TerminalGuardWitness
      input target view topology)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (guardComputed :
      TerminalGuardedRule3Node.localizedRule3TerminalGuard? input target view topology =
        some witness)
    (cursor child : input.LocalizedRerootCursor fuel)
    (sameOccurrence : cursor.occurrence = occurrence) :
    Edge (terminalGuardedWeightedDemandGraph input target view) cursor child ↔
      child ∈ input.executableLocalizedRerootChildren cursor := by
  show child ∈ successors (terminalGuardedWeightedDemandGraph input target view) cursor ↔
    child ∈ input.executableLocalizedRerootChildren cursor
  rw [terminalGuardedWeightedDemandGraph_successors_eq_children_of_guard input target occurrence
    view topology witness oddRoute ordinaryRoute topologyComputed guardComputed cursor
    sameOccurrence]

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedEdge_iff_structural_of_guard

/-! ## Graph-to-node locality bridge

The sibling recursive-key module must prove stability of the *terminal-guarded* recursion.  This
section supplies the precise interface: graph-request agreement at a cursor is exactly the
hypothesis of the existing terminal-guarded node locality theorem.  It is not a stability theorem
for the old extended evaluator. -/

/-- Agreement on the guarded graph's request list at a cursor implies callback locality of the
actual terminal-guarded node evaluator at the matching occurrence.  The exclusion list is
arbitrary and the guard computation is never replaced by an assumption. -/
theorem terminalGuardedWeightedDemandGraph_node_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (cursor : input.LocalizedRerootCursor fuel)
    (sameOccurrence : cursor.occurrence = occurrence)
    (agree : input.Rule3CallbackAgreesOn
      ((terminalGuardedWeightedDemandGraph input target view).requests cursor) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    TerminalGuardedRule3Node.localizedRule3TerminalGuardedNodeWithExec?
        input target occurrence view before excluded =
      TerminalGuardedRule3Node.localizedRule3TerminalGuardedNodeWithExec?
        input target occurrence view after excluded := by
  apply TerminalGuardedRule3Node.rule3TerminalGuardedNode_callback_local
    input target occurrence view before after
  intro cursors member
  exact agree cursors (by
    simpa only [terminalGuardedWeightedDemandGraph_requests, sameOccurrence] using member)

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedWeightedDemandGraph_node_local

/-! ## Executable discovery with the input-derived structural budget -/

/-- Uniform structural traversal budget, identical to the concrete extended constructor:
`occurrenceCount * (occurrenceCount + 1) + 1`.  It is derived from the finite occurrence carrier
of the input and depends on no target, view, desired result or successful evaluation. -/
def terminalGuardedDemandTraversalBudget (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Nat :=
  let occurrenceCount := (input.localizedOccurrenceCarrier fuel).length
  occurrenceCount * (occurrenceCount + 1) + 1

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalGuardedDemandTraversalBudget





def prepareTerminalGuardedDemandPlan
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel)) :
    Except (DiscoveryFailure (input.LocalizedRerootCursor fuel))
      (Plan (terminalGuardedWeightedDemandGraph input target view) roots) :=
  prepare (terminalGuardedWeightedDemandGraph input target view)
    (terminalGuardedDemandTraversalBudget input fuel) roots

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareTerminalGuardedDemandPlan





theorem prepareTerminalGuardedDemandPlan_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (succeeds : ∃ plan,
      prepareTerminalGuardedDemandPlan input target view roots = .ok plan) :
    Acyclic (terminalGuardedWeightedDemandGraph input target view) roots := by
  obtain ⟨plan, _⟩ := succeeds
  exact plan.acyclic

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareTerminalGuardedDemandPlan_acyclic








/-- The ranks of an existing checked extended certificate certify the terminal-guarded graph
unchanged.  Child edges are identical; each guarded request is first embedded into the extended
request list and only the generic list maximum is transported. -/
def ExtendedRule3DemandRankCertificate.toTerminalGuardedRankCertificate
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    RankCertificate (terminalGuardedWeightedDemandGraph input target view) where
  vertices := certificate.vertices
  height := certificate.height
  positive := certificate.positive
  children := by
    intro cursor member child present
    exact certificate.children cursor member child (by
      simpa only [terminalGuardedWeightedDemandGraph_children] using present)
  callbacks := by
    intro cursor member request requested
    have requested' : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence := by
      apply terminalGuardedNodeCallbackRequests_subset input target view cursor.occurrence request
      simpa only [terminalGuardedWeightedDemandGraph_requests] using requested
    obtain ⟨covered, bounded⟩ := certificate.callbacks cursor member request requested'
    refine ⟨covered, ?_⟩
    rw [weightedListHeight_eq_rule3CursorListHeight]
    exact bounded

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedRule3DemandRankCertificate.toTerminalGuardedRankCertificate



def ExtendedRule3DemandPlan.toTerminalGuardedPlan
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    Plan (terminalGuardedWeightedDemandGraph input target view) roots where
  ranks := plan.ranks.toTerminalGuardedRankCertificate target view
  covers := plan.covers

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedRule3DemandPlan.toTerminalGuardedPlan


theorem ExtendedRule3DemandPlan.toTerminalGuardedPlan_bound
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    (plan.toTerminalGuardedPlan target view).bound = plan.bound := by
  show listHeight plan.ranks.height roots + 1 =
    rule3CursorListHeight plan.ranks.height roots + 1
  rw [weightedListHeight_eq_rule3CursorListHeight]

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedRule3DemandPlan.toTerminalGuardedPlan_bound



theorem ExtendedRule3DemandPlan.terminalGuardedAcyclic
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    Acyclic (terminalGuardedWeightedDemandGraph input target view) roots :=
  (plan.toTerminalGuardedPlan target view).acyclic

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ExtendedRule3DemandPlan.terminalGuardedAcyclic

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
