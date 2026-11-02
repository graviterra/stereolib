import TetraStereo.OneCenter.LocalizedTerminalGuardedDemandDiscovery
import TetraStereo.OneCenter.LocalizedTerminalGuardedObservationAdapter
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter









































































/-! ## The successor recursion equations of the fully guarded mutual evaluator -/

/-- The two executable functions of the fully terminal-guarded mutual key/frame recursion together
with their successor equations.

The `key_succ` field is exactly the `fuel + 1` branch of the actual mutually recursive key
definition: the actual-reference node adapter receives the fully guarded frame callback at the
predecessor index; accepted guards demand no callback, and the structural child keys use the
fully guarded key at the predecessor index.  The `frame_succ` field is exactly the `fuel + 1`
branch of the actual frame: the raw pass uses the key at `[]`, the coupled topology and exclusion
computation are the actual executable ones, and the rebuilt pass uses the key at the computed
exclusion list.  Both fields are definitional for the actual definitions, not additional semantic
assumptions.

The zero branches are deliberately not part of this package: stability is only ever invoked at a
positive threshold, so no zero-fuel computation has to be characterized. -/
structure FullyTerminalGuardedSuccessorRecursion
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) where
  /-- The fully guarded recursive key evaluator. -/
  key : Nat → List input.LocalizedRule3PhysicalUnitId →
    input.LocalizedRerootCursor fuel → Option input.LocalizedRerootRecursiveRule3SpatialKey
  /-- The fully guarded two-pass frame evaluator. -/
  frame : Nat → List (input.LocalizedRerootCursor fuel) →
    Option input.LocalizedRule3CanonicalKeyFrame
  /-- The `fuel + 1` key branch, verbatim. -/
  key_succ : ∀ (predecessor : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
      (cursor : input.LocalizedRerootCursor fuel),
    key (predecessor + 1) excluded cursor =
      (do
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← localizedRule3TerminalGuardedSpatialNodeWithExec?
          input target cursor.occurrence view (frame predecessor) excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM (fun child => key predecessor excluded child)
          let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
          some
            { constitutional := OfficialRuleMajorKey.assemble
                (input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node false)
                (sorted.map fun child => child.constitutional)
              observations := input.localizedRule3SpatialRootObservations observation ++
                input.mergeLocalizedRerootRule3ObservationChildren sorted
              rule3 := input.localizedRule3SpatialRootPriorities observation ++
                input.mergeLocalizedRerootRule3PriorityChildren sorted })
  /-- The `fuel + 1` frame branch, verbatim. -/
  frame_succ : ∀ (predecessor : Nat) (cursors : List (input.LocalizedRerootCursor fuel)),
    frame (predecessor + 1) cursors =
      (do
        let rawKeys ← cursors.mapM (fun cursor => key predecessor [] cursor)
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM (fun cursor => key predecessor excluded cursor)
        some { rawKeys := rawKeys, coupled := coupled, excluded := excluded, keys := keys })

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.FullyTerminalGuardedSuccessorRecursion

/-! ## Threshold-indexed stability predicates -/

/-- Key stability at a rank threshold: every vertex whose checked rank is at most the threshold has
the same full optional key at every two budgets at least the threshold, for an arbitrary fixed
exclusion list. -/
def FullyTerminalGuardedKeyStableAt
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (threshold : Nat) : Prop :=
  ∀ (cursor : input.LocalizedRerootCursor fuel), cursor ∈ certificate.vertices →
    certificate.height cursor ≤ threshold →
      ∀ (first second : Nat), threshold ≤ first → threshold ≤ second →
        ∀ excluded : List input.LocalizedRule3PhysicalUnitId,
          evaluator.key first excluded cursor = evaluator.key second excluded cursor

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.FullyTerminalGuardedKeyStableAt

/-- Frame stability at a rank threshold: every list of covered cursors whose checked list height
plus one is at most the threshold has the same full optional two-pass frame at every two budgets at
least the threshold.  The extra `+ 1` is the predecessor decrement of the frame builder. -/
def FullyTerminalGuardedFrameStableAt
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (threshold : Nat) : Prop :=
  ∀ (cursors : List (input.LocalizedRerootCursor fuel)),
    (∀ cursor ∈ cursors, cursor ∈ certificate.vertices) →
      listHeight certificate.height cursors + 1 ≤ threshold →
        ∀ (first second : Nat), threshold ≤ first → threshold ≤ second →
          evaluator.frame first cursors = evaluator.frame second cursors

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.FullyTerminalGuardedFrameStableAt

/-! ## Plain pointwise `mapM` congruence -/

/-- Equality of two functions on a list gives equality of the corresponding `mapM` computations,
including all refusals. -/
private theorem fullyTerminalGuardedMapM_congr_on {α β : Type} (before after : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, before value = after value) →
      values.mapM before = values.mapM after
  | [], _ => rfl
  | value :: values, agree => by
    have head := agree value (by simp)
    have tail := fullyTerminalGuardedMapM_congr_on before after values
      (fun value present => agree value (by simp [present]))
    simp [head, tail]

/-! ## The simultaneous rank induction -/

/-- **Simultaneous successor step.**  From key and frame stability at threshold `t`, derive both at
threshold `t + 1`.

Key step: writing `first = a + 1` and `second = b + 1` (possible because the threshold is positive
and the vertex rank is positive), the node adapter's two callback arguments are compared on the
matching guarded request list.  Each request is closed by the frame hypothesis at threshold `t`
(the certificate charges `+2`, so `listHeight + 1 ≤ t`).  Each structural child is closed by the key
hypothesis at threshold `t` (the certificate charges `+1`).  The two key successor equations then
reduce the goal to a syntactically identical assembly.

Frame step: the raw pass receives `[]` on both sides, and the rebuilt pass receives the *same*
exclusion list because the raw-key lists are equal.  Both are closed by the key hypothesis at
threshold `t`.  The coupled topology resolution therefore consumes identical raw keys, and the two
frame successor equations reduce the goal to identical frame records. -/
private theorem fullyTerminalGuardedStableAt_succ
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (threshold : Nat)
    (keyPrior : FullyTerminalGuardedKeyStableAt input evaluator certificate threshold)
    (framePrior : FullyTerminalGuardedFrameStableAt input evaluator certificate threshold) :
    FullyTerminalGuardedKeyStableAt input evaluator certificate (threshold + 1) ∧
      FullyTerminalGuardedFrameStableAt input evaluator certificate (threshold + 1) := by
  constructor
  · -- Key stability at the successor threshold.
    intro cursor member heightBound first second firstEnough secondEnough excluded
    have positive := certificate.positive cursor member
    obtain ⟨firstPredecessor, rfl⟩ : ∃ predecessor, first = predecessor + 1 :=
      ⟨first - 1, by omega⟩
    obtain ⟨secondPredecessor, rfl⟩ : ∃ predecessor, second = predecessor + 1 :=
      ⟨second - 1, by omega⟩
    have firstPredecessorEnough : threshold ≤ firstPredecessor := by omega
    have secondPredecessorEnough : threshold ≤ secondPredecessor := by omega
    -- Callback agreement on the matching guarded request list.
    have callbackEq : input.Rule3CallbackAgreesOn
        (localizedRule3TerminalGuardedSpatialNodeCallbackRequests
          input target cursor.occurrence view)
        (evaluator.frame firstPredecessor) (evaluator.frame secondPredecessor) := by
      intro request requested
      have graphRequested :
          request ∈ (terminalGuardedWeightedDemandGraph input target view).requests cursor := by
        simpa only [localizedRule3TerminalGuardedSpatialNodeCallbackRequests,
          terminalGuardedWeightedDemandGraph_requests] using requested
      obtain ⟨covered, bounded⟩ := certificate.callbacks cursor member request graphRequested
      exact framePrior request covered (by omega) firstPredecessor secondPredecessor
        firstPredecessorEnough secondPredecessorEnough
    have nodeEq := localizedRule3TerminalGuardedSpatialNode_callback_local
      input target cursor.occurrence view
      (evaluator.frame firstPredecessor) (evaluator.frame secondPredecessor)
      callbackEq excluded
    -- Structural children, closed by the key hypothesis at the predecessor threshold.
    have childrenEq : (input.executableLocalizedRerootChildren cursor).mapM
        (evaluator.key firstPredecessor excluded) =
      (input.executableLocalizedRerootChildren cursor).mapM
        (evaluator.key secondPredecessor excluded) := by
      apply fullyTerminalGuardedMapM_congr_on
      intro child present
      obtain ⟨covered, bounded⟩ := certificate.children cursor member child present
      exact keyPrior child covered (by omega) firstPredecessor secondPredecessor
        firstPredecessorEnough secondPredecessorEnough excluded
    rw [evaluator.key_succ firstPredecessor excluded cursor,
      evaluator.key_succ secondPredecessor excluded cursor]
    simp only [executableLocalizedRerootChildren?_eq_some, bind, Option.bind,
      nodeEq, childrenEq]
  · -- Frame stability at the successor threshold.
    intro cursors covered heightBound first second firstEnough secondEnough
    obtain ⟨firstPredecessor, rfl⟩ : ∃ predecessor, first = predecessor + 1 :=
      ⟨first - 1, by omega⟩
    obtain ⟨secondPredecessor, rfl⟩ : ∃ predecessor, second = predecessor + 1 :=
      ⟨second - 1, by omega⟩
    have firstPredecessorEnough : threshold ≤ firstPredecessor := by omega
    have secondPredecessorEnough : threshold ≤ secondPredecessor := by omega
    -- Raw pass: both sides use the empty exclusion list.
    have rawEq : cursors.mapM (fun cursor => evaluator.key firstPredecessor [] cursor) =
        cursors.mapM (fun cursor => evaluator.key secondPredecessor [] cursor) := by
      apply fullyTerminalGuardedMapM_congr_on
      intro cursor present
      have heightMember := listHeight_mem certificate.height cursors cursor present
      exact keyPrior cursor (covered cursor present) (by omega) firstPredecessor
        secondPredecessor firstPredecessorEnough secondPredecessorEnough []
    rw [evaluator.frame_succ firstPredecessor cursors,
      evaluator.frame_succ secondPredecessor cursors, rawEq]
    -- The two frames now differ only in the rebuilt key pass.  The raw keys and the coupled
    -- topology are literally the same expressions on both sides, so the exclusion list is too;
    -- only the key budget differs, and that is closed by the predecessor hypothesis.
    have rebuiltEq : ∀ (rawKeys : List input.LocalizedRerootRecursiveRule3SpatialKey)
        (topology : input.LocalizedRule3CoupledTopologyResolution),
        cursors.mapM
            (fun cursor => evaluator.key firstPredecessor
              (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology) cursor) =
          cursors.mapM
            (fun cursor => evaluator.key secondPredecessor
              (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology) cursor) := by
      intro rawKeys topology
      apply fullyTerminalGuardedMapM_congr_on
      intro cursor present
      have heightMember := listHeight_mem certificate.height cursors cursor present
      exact keyPrior cursor (covered cursor present) (by omega) firstPredecessor
        secondPredecessor firstPredecessorEnough secondPredecessorEnough _
    simp only [bind, Option.bind, rebuiltEq]

/-- **Stability at every threshold.**  Ordinary induction on the threshold, with the simultaneous
successor step.  Both base cases are vacuous: a covered vertex has positive rank, so no vertex rank
is at most `0`, and `listHeight + 1 ≤ 0` is impossible. -/
theorem fullyTerminalGuardedStableAt
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view)) :
    ∀ threshold,
      FullyTerminalGuardedKeyStableAt input evaluator certificate threshold ∧
        FullyTerminalGuardedFrameStableAt input evaluator certificate threshold := by
  intro threshold
  induction threshold with
  | zero =>
      constructor
      · intro cursor member heightBound first second firstEnough secondEnough excluded
        have positive := certificate.positive cursor member
        omega
      · intro cursors covered heightBound first second firstEnough secondEnough
        omega
  | succ threshold induction =>
      exact fullyTerminalGuardedStableAt_succ input evaluator certificate threshold
        induction.1 induction.2

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.fullyTerminalGuardedStableAt

/-! ## Stability from a matching guarded rank certificate -/

/-- **Full-`Option` key stability from the matching guarded rank.**  Every cursor in the checked
closed vertex set has the same complete optional key result at every two budgets above its checked
rank, under any fixed exclusion list.  Only `RankCertificate (terminalGuardedWeightedDemandGraph
input target view)` is assumed; no old extended rank, no successful evaluation and no acyclic
premise appears. -/
theorem fullyTerminalGuardedKey_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ certificate.vertices)
    (first second : Nat) (firstEnough : certificate.height cursor ≤ first)
    (secondEnough : certificate.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    evaluator.key first excluded cursor = evaluator.key second excluded cursor :=
  (fullyTerminalGuardedStableAt input evaluator certificate (certificate.height cursor)).1
    cursor member (Nat.le_refl _) first second firstEnough secondEnough excluded

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.fullyTerminalGuardedKey_stable

/-- **Full-`Option` frame stability from the matching guarded rank.**  Every list of covered
cursors has the same complete optional two-pass frame result at every two budgets above the checked
list height plus one.  Both raw and rebuilt passes, the coupled-topology refusal, and every
exclusion branch are preserved. -/
theorem fullyTerminalGuardedFrame_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (certificate : RankCertificate (terminalGuardedWeightedDemandGraph input target view))
    (cursors : List (input.LocalizedRerootCursor fuel))
    (covered : ∀ cursor ∈ cursors, cursor ∈ certificate.vertices)
    (first second : Nat)
    (firstEnough : listHeight certificate.height cursors + 1 ≤ first)
    (secondEnough : listHeight certificate.height cursors + 1 ≤ second) :
    evaluator.frame first cursors = evaluator.frame second cursors :=
  (fullyTerminalGuardedStableAt input evaluator certificate
    (listHeight certificate.height cursors + 1)).2
    cursors covered (Nat.le_refl _) first second firstEnough secondEnough

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.fullyTerminalGuardedFrame_stable





def FullyTerminalGuardedPlan.evaluate
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  evaluator.frame plan.bound roots

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.FullyTerminalGuardedPlan.evaluate




theorem FullyTerminalGuardedPlan.evaluate_eq_above
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    FullyTerminalGuardedPlan.evaluate plan evaluator = evaluator.frame budget roots := by
  unfold FullyTerminalGuardedPlan.evaluate
  exact fullyTerminalGuardedFrame_stable input evaluator plan.ranks roots plan.covers
    plan.bound budget (Nat.le_refl _) enough

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.FullyTerminalGuardedPlan.evaluate_eq_above


theorem FullyTerminalGuardedPlan.key_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    {view : input.LocalizedDependencyView target}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ plan.ranks.vertices)
    (first second : Nat) (firstEnough : plan.ranks.height cursor ≤ first)
    (secondEnough : plan.ranks.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    evaluator.key first excluded cursor = evaluator.key second excluded cursor :=
  fullyTerminalGuardedKey_stable input evaluator plan.ranks cursor member first second
    firstEnough secondEnough excluded

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.FullyTerminalGuardedPlan.key_stable

/-! ## From the executable guarded discovery to stability -/




theorem prepareFullyTerminalGuardedDemandPlan_key_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (_prepared : prepareTerminalGuardedDemandPlan input target view roots = .ok plan)
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ plan.ranks.vertices)
    (first second : Nat) (firstEnough : plan.ranks.height cursor ≤ first)
    (secondEnough : plan.ranks.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    evaluator.key first excluded cursor = evaluator.key second excluded cursor :=
  FullyTerminalGuardedPlan.key_stable plan evaluator cursor member first second
    firstEnough secondEnough excluded

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareFullyTerminalGuardedDemandPlan_key_stable



theorem prepareFullyTerminalGuardedDemandPlan_frame_stable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (evaluator : FullyTerminalGuardedSuccessorRecursion input target view)
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (_prepared : prepareTerminalGuardedDemandPlan input target view roots = .ok plan)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    FullyTerminalGuardedPlan.evaluate plan evaluator = evaluator.frame budget roots :=
  FullyTerminalGuardedPlan.evaluate_eq_above plan evaluator budget enough

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareFullyTerminalGuardedDemandPlan_frame_stable



theorem prepareFullyTerminalGuardedDemandPlan_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (roots : List (input.LocalizedRerootCursor fuel))
    (plan : Plan (terminalGuardedWeightedDemandGraph input target view) roots)
    (_prepared : prepareTerminalGuardedDemandPlan input target view roots = .ok plan) :
    Acyclic (terminalGuardedWeightedDemandGraph input target view) roots :=

  prepareTerminalGuardedDemandPlan_acyclic input target view roots ⟨plan, _prepared⟩

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareFullyTerminalGuardedDemandPlan_acyclic

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
