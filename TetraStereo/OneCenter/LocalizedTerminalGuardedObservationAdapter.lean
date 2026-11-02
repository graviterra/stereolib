import TetraStereo.OneCenter.LocalizedTerminalGuardedRule3Node
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Terminal-guarded node observations as actual extension-key observations

`LocalizedTerminalGuardedRule3Node` introduced a direct guarded node result: a physical endpoint
topology together with the endpoint side accepted by the actual, executable terminal-reference
guard.  That type deliberately does not carry an opposite raw reference, an opposite frame or an
opposite priority, so it cannot be stored in an existing extended Rule-3 key, whose sparse
observations are `LocalizedRule3SpatialNodeResult` values.

This module supplies the smallest sound adapter.

* `localizedRule3TerminalGuardedDirectObservation?` converts an accepted guarded identity into a
  genuine `LocalizedRule3SpatialNodeResult`: the two *physical* endpoints of the recovered topology,
  geometry `.nonstereogenic`, and one **actual** explicit substituent per endpoint.  The guarded
  side's diagnostic reference is exactly the guard certificate's first candidate; the opposite
  side's is the canonical first element of the actual, canonically sorted explicit-substituent
  list.  No callback, no opposite endpoint frame and no opposite endpoint priority is consulted.
  When the opposite endpoint has no explicit substituent the conversion is an explicit refusal
  (`none`).

* `localizedRule3TerminalGuardedSpatialNodeWithExec?` is the executable node adapter with exactly
  the nested-`Option` discipline of `localizedRule3ExtendedShortCircuitNodeWithExec?`: outer `none`
  is refusal/unresolved, inner `none` is "no geometrical unit".  Every fallback branch is literally
  the old computation; only an accepted guard changes the value, and only in its diagnostic raw
  references.

* The reduced callback demand is inherited unchanged from the guarded node evaluator
  (`rule3TerminalGuardedNodeCallbackRequests`), so an accepted guard demands no callback at all and
  callback locality holds on exactly that list.

Main results:

* `..._components` / `..._sound`: the direct observation has the physical endpoints, a
  nonstereogenic geometry, and actual explicit substituents on both sides (independent declarative
  guard semantics);
* `..._physicalUnitId` / `..._observable` / `..._unit_priority`: physical identity and the common
  nonstereogenic observable agree with the guarded identity;
* `..._callback_local`: callback locality on the actual reduced request list;
* `..._guard_branch_candidate` / `..._guard_branch_excluded` / `..._guard_branch_refusal`: exact
  exclusion and candidate-lookup behaviour on the guarded branch;
* `..._refines_extended_none` and `..._refines_extended_observation`: every former old success is
  preserved, with the same physical identity, the same geometry, the same Rule-3 priority and the
  same common observable; only diagnostic raw references may differ.

Nothing here claims chemical realizability, semantic-model existence, or raw-record equality with
the old evaluator.  The constructed references are physical non-partner neighbours, not claimed to
be constitutional senior references; the old `DeclarativeLocalizedRule3SpatialNode` meaning is
therefore deliberately **not** asserted for them.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter

open TetraStereo.OneCenter
open TerminalGuardedRule3Node
open TerminalEndpointObservation

/-! ## Actual explicit substituents as diagnostic references -/

/-- Canonical first actual non-partner neighbour of one endpoint, in the same canonical atom order
used by the production endpoint compilers.  This is a molecule lookup: it never consults a
callback and never inspects the opposite endpoint's frame. -/
def localizedRule3CanonicalExplicitSubstituent?
    (input : CertifiedLocalizedCIPInput) (endpoint partner : input.Atom) : Option input.Atom :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [] => none
  | candidate :: _ => some candidate

/-- A successful canonical candidate lookup is a real member of the actual explicit-substituent
list. -/
theorem localizedRule3CanonicalExplicitSubstituent?_mem
    (input : CertifiedLocalizedCIPInput) (endpoint partner candidate : input.Atom)
    (computed : localizedRule3CanonicalExplicitSubstituent? input endpoint partner = some candidate) :
    candidate ∈ input.localizedRule3ExplicitSubstituents endpoint partner := by
  unfold localizedRule3CanonicalExplicitSubstituent? at computed
  cases candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp [candidates] at computed
  | cons head tail =>
      rw [candidates] at computed
      simp only [Option.some.injEq] at computed
      rw [← computed]
      simp

/-- A successful canonical candidate lookup is genuinely adjacent to the endpoint. -/
theorem localizedRule3CanonicalExplicitSubstituent?_adjacent
    (input : CertifiedLocalizedCIPInput) (endpoint partner candidate : input.Atom)
    (computed : localizedRule3CanonicalExplicitSubstituent? input endpoint partner = some candidate) :
    input.moleculeGraph.Adj endpoint candidate :=
  ((input.mem_localizedRule3ExplicitSubstituents_iff endpoint partner candidate).mp
    (localizedRule3CanonicalExplicitSubstituent?_mem input endpoint partner candidate computed)).1

/-- A successful canonical candidate lookup is distinct from the endpoint itself. -/
theorem localizedRule3CanonicalExplicitSubstituent?_ne_endpoint
    (input : CertifiedLocalizedCIPInput) (endpoint partner candidate : input.Atom)
    (computed : localizedRule3CanonicalExplicitSubstituent? input endpoint partner = some candidate) :
    candidate ≠ endpoint :=
  input.localizedRule3ExplicitSubstituent_ne_endpoint endpoint partner candidate
    (localizedRule3CanonicalExplicitSubstituent?_mem input endpoint partner candidate computed)

/-- A successful production short-circuit endpoint compilation exposes a nonempty actual candidate
list.  Its very first case is `match … with | [first, second] => … | _ => none`, so success forces
at least one candidate. -/
theorem exists_cons_of_localizedRule3ShortCircuitEndpointPriorityExec?_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view callback endpoint partner endpointCursor = some result) :
    ∃ first rest, input.localizedRule3ExplicitSubstituents endpoint partner = first :: rest := by
  unfold localizedRule3ShortCircuitEndpointPriorityExec? at computed
  cases candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp [candidates] at computed
  | cons first rest => exact ⟨first, rest, rfl⟩

/-- Consequently the canonical actual candidate exists at every endpoint that the production
short-circuit endpoint compiler accepts. -/
theorem localizedRule3CanonicalExplicitSubstituent?_isSome_of_shortCircuitEndpointPriorityExec?_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view callback endpoint partner endpointCursor = some result) :
    ∃ candidate, localizedRule3CanonicalExplicitSubstituent? input endpoint partner = some candidate := by
  obtain ⟨first, rest, candidates⟩ :=
    exists_cons_of_localizedRule3ShortCircuitEndpointPriorityExec?_some input target view callback
      endpoint partner endpointCursor result computed
  exact ⟨first, by
    unfold localizedRule3CanonicalExplicitSubstituent?
    rw [candidates]⟩

/-- The guarded side's canonical actual candidate is exactly the guard certificate's first
candidate.  The certificate records that the whole candidate list is `[first, second]`. -/
theorem localizedRule3CanonicalExplicitSubstituent?_terminalReferencePair_left
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor) :
    localizedRule3CanonicalExplicitSubstituent? input endpoint partner = some certificate.first := by
  unfold localizedRule3CanonicalExplicitSubstituent?
  rw [certificate.candidates]

/-! ## The direct guarded observation -/

/-- Convert an accepted guarded identity into a genuine `LocalizedRule3SpatialNodeResult`.

The two physical endpoints are exactly those of the recovered topology, the geometry is
`.nonstereogenic`, and each diagnostic reference is the canonical first **actual** explicit
substituent of its endpoint.  No callback and no opposite frame are consulted.  If either endpoint
has no explicit substituent the conversion refuses with `none`. -/
def localizedRule3TerminalGuardedDirectObservation?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    Option input.LocalizedRule3SpatialNodeResult :=
  match localizedRule3CanonicalExplicitSubstituent?
      input identity.topology.left identity.topology.right,
    localizedRule3CanonicalExplicitSubstituent?
      input identity.topology.right identity.topology.left with
  | some leftReference, some rightReference =>
      some
        { left := identity.topology.left
          right := identity.topology.right
          unit :=
            { leftReference := leftReference
              rightReference := rightReference
              geometry := OfficialRule3Geometry.nonstereogenic } }
  | _, _ => none

/-- Exact value of the direct observation when both canonical candidate lookups succeed. -/
theorem localizedRule3TerminalGuardedDirectObservation?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (leftReference rightReference : input.Atom)
    (leftComputed : localizedRule3CanonicalExplicitSubstituent?
      input identity.topology.left identity.topology.right = some leftReference)
    (rightComputed : localizedRule3CanonicalExplicitSubstituent?
      input identity.topology.right identity.topology.left = some rightReference) :
    localizedRule3TerminalGuardedDirectObservation? input identity =
      some
        ({ left := identity.topology.left
           right := identity.topology.right
           unit :=
             { leftReference := leftReference
               rightReference := rightReference
               geometry := OfficialRule3Geometry.nonstereogenic } } :
          input.LocalizedRule3SpatialNodeResult) := by
  unfold localizedRule3TerminalGuardedDirectObservation?
  rw [leftComputed, rightComputed]

/-- Independent declarative semantics of a direct terminal-guarded observation: the physical
endpoints are exactly the recovered topology, the physical bond is order two, the geometry is
nonstereogenic, and both diagnostic references are actual non-partner neighbours of their
endpoints.  This is a new guard-level meaning; it deliberately does not assert the older
`DeclarativeLocalizedRule3SpatialNode` senior-reference clauses. -/
def DeclarativeLocalizedRule3TerminalGuardedObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult) : Prop :=
  observation.left = topology.left ∧
    observation.right = topology.right ∧
    input.moleculeGraph.bond topology.left topology.right = 2 ∧
    observation.unit.geometry = OfficialRule3Geometry.nonstereogenic ∧
    observation.unit.leftReference ∈
      input.localizedRule3ExplicitSubstituents topology.left topology.right ∧
    observation.unit.rightReference ∈
      input.localizedRule3ExplicitSubstituents topology.right topology.left

/-- Complete component data of a successful direct observation, without the bond clause (which the
identity does not carry; the evaluator obtains it from the recovered topology). -/
theorem localizedRule3TerminalGuardedDirectObservation?_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    observation.left = identity.topology.left ∧
      observation.right = identity.topology.right ∧
      observation.unit.geometry = OfficialRule3Geometry.nonstereogenic ∧
      observation.unit.leftReference ∈
        input.localizedRule3ExplicitSubstituents identity.topology.left identity.topology.right ∧
      observation.unit.rightReference ∈
        input.localizedRule3ExplicitSubstituents identity.topology.right identity.topology.left := by
  unfold localizedRule3TerminalGuardedDirectObservation? at computed
  cases leftComputed :
      localizedRule3CanonicalExplicitSubstituent?
        input identity.topology.left identity.topology.right with
  | none => simp [leftComputed] at computed
  | some leftReference =>
      cases rightComputed :
          localizedRule3CanonicalExplicitSubstituent?
            input identity.topology.right identity.topology.left with
      | none => simp [leftComputed, rightComputed] at computed
      | some rightReference =>
          simp only [leftComputed, rightComputed, Option.some.injEq] at computed
          rw [← computed]
          refine ⟨rfl, rfl, rfl, ?_, ?_⟩
          · exact localizedRule3CanonicalExplicitSubstituent?_mem input
              identity.topology.left identity.topology.right leftReference leftComputed
          · exact localizedRule3CanonicalExplicitSubstituent?_mem input
              identity.topology.right identity.topology.left rightReference rightComputed

/-- The direct observation has its independent declarative guard meaning whenever the recovered
topology is a physical double bond. -/
theorem localizedRule3TerminalGuardedDirectObservation?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (doubleBond : input.moleculeGraph.bond identity.topology.left identity.topology.right = 2)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    DeclarativeLocalizedRule3TerminalGuardedObservation input identity.topology observation := by
  obtain ⟨left, right, geometry, leftPresent, rightPresent⟩ :=
    localizedRule3TerminalGuardedDirectObservation?_components input identity observation computed
  exact ⟨left, right, doubleBond, geometry, leftPresent, rightPresent⟩

/-- The direct observation preserves the physical left endpoint. -/
theorem localizedRule3TerminalGuardedDirectObservation?_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    observation.left = identity.topology.left :=
  (localizedRule3TerminalGuardedDirectObservation?_components input identity observation computed).1

/-- The direct observation preserves the physical right endpoint. -/
theorem localizedRule3TerminalGuardedDirectObservation?_right
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    observation.right = identity.topology.right :=
  (localizedRule3TerminalGuardedDirectObservation?_components input identity observation computed).2.1

/-- The direct observation carries the nonstereogenic geometry certified by the guard. -/
theorem localizedRule3TerminalGuardedDirectObservation?_geometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    observation.unit.geometry = OfficialRule3Geometry.nonstereogenic :=
  (localizedRule3TerminalGuardedDirectObservation?_components input identity observation computed).2.2.1

/-- Consequently the Rule-3 priority carried by the direct observation is the nonstereogenic
priority. -/
theorem localizedRule3TerminalGuardedDirectObservation?_unit_priority
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    observation.unit.geometry.priority = OfficialRule3Geometry.nonstereogenic.priority := by
  rw [localizedRule3TerminalGuardedDirectObservation?_geometry input identity observation computed]

/-- The direct observation's physical-unit identity is exactly the guarded identity's canonical
ordered endpoint pair. -/
theorem localizedRule3TerminalGuardedDirectObservation?_physicalUnitId
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    observation.physicalUnitId = identity.physicalUnitId := by
  obtain ⟨left, right, _, _, _⟩ :=
    localizedRule3TerminalGuardedDirectObservation?_components input identity observation computed
  simp only [LocalizedRule3SpatialNodeResult.physicalUnitId,
    LocalizedRule3TerminalGuardedIdentity.physicalUnitId, left, right]

/-- The direct observation's common observable projection is exactly the guarded identity's
observable: same physical endpoints and the same nonstereogenic geometry. -/
theorem localizedRule3TerminalGuardedDirectObservation?_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (observation : input.LocalizedRule3SpatialNodeResult)
    (computed : localizedRule3TerminalGuardedDirectObservation? input identity = some observation) :
    LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation =
      LocalizedRule3TerminalGuardedIdentity.observable identity := by
  obtain ⟨left, right, geometry, _, _⟩ :=
    localizedRule3TerminalGuardedDirectObservation?_components input identity observation computed
  simp only [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable,
    LocalizedRule3TerminalGuardedIdentity.observable, left, right, geometry]

/-- The direct observation exists as soon as both canonical actual candidate lookups succeed. -/
theorem localizedRule3TerminalGuardedDirectObservation?_isSome_of_candidates
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    (leftExists : ∃ candidate : input.Atom,
      localizedRule3CanonicalExplicitSubstituent?
        input identity.topology.left identity.topology.right = some candidate)
    (rightExists : ∃ candidate : input.Atom,
      localizedRule3CanonicalExplicitSubstituent?
        input identity.topology.right identity.topology.left = some candidate) :
    ∃ observation,
      localizedRule3TerminalGuardedDirectObservation? input identity = some observation := by
  obtain ⟨leftReference, leftComputed⟩ := leftExists
  obtain ⟨rightReference, rightComputed⟩ := rightExists
  exact ⟨_, localizedRule3TerminalGuardedDirectObservation?_eq input identity
    leftReference rightReference leftComputed rightComputed⟩

/-! ## Certificate-backed references on the guarded side -/

/-- On a left guard the diagnostic left reference is exactly the certificate's actual first
candidate; the opposite reference is any actual canonical candidate. -/
theorem localizedRule3TerminalGuardedDirectObservation?_leftCertificate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (certificate : TerminalReferencePair input target view
      topology.left topology.right topology.leftCursor)
    (rightReference : input.Atom)
    (rightComputed : localizedRule3CanonicalExplicitSubstituent?
      input topology.right topology.left = some rightReference) :
    localizedRule3TerminalGuardedDirectObservation? input
        ({ topology := topology, side := LocalizedRule3TerminalGuardSide.left } :
          LocalizedRule3TerminalGuardedIdentity input carrierFuel) =
      some
        ({ left := topology.left
           right := topology.right
           unit :=
             { leftReference := certificate.first
               rightReference := rightReference
               geometry := OfficialRule3Geometry.nonstereogenic } } :
          input.LocalizedRule3SpatialNodeResult) :=
  localizedRule3TerminalGuardedDirectObservation?_eq input
    ({ topology := topology, side := LocalizedRule3TerminalGuardSide.left } :
      LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    certificate.first rightReference
    (localizedRule3CanonicalExplicitSubstituent?_terminalReferencePair_left certificate)
    rightComputed

/-- On a right guard the diagnostic right reference is exactly the certificate's actual first
candidate; the opposite reference is any actual canonical candidate. -/
theorem localizedRule3TerminalGuardedDirectObservation?_rightCertificate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (certificate : TerminalReferencePair input target view
      topology.right topology.left topology.rightCursor)
    (leftReference : input.Atom)
    (leftComputed : localizedRule3CanonicalExplicitSubstituent?
      input topology.left topology.right = some leftReference) :
    localizedRule3TerminalGuardedDirectObservation? input
        ({ topology := topology, side := LocalizedRule3TerminalGuardSide.right } :
          LocalizedRule3TerminalGuardedIdentity input carrierFuel) =
      some
        ({ left := topology.left
           right := topology.right
           unit :=
             { leftReference := leftReference
               rightReference := certificate.first
               geometry := OfficialRule3Geometry.nonstereogenic } } :
          input.LocalizedRule3SpatialNodeResult) :=
  localizedRule3TerminalGuardedDirectObservation?_eq input
    ({ topology := topology, side := LocalizedRule3TerminalGuardSide.right } :
      LocalizedRule3TerminalGuardedIdentity input carrierFuel)
    leftReference certificate.first
    leftComputed
    (localizedRule3CanonicalExplicitSubstituent?_terminalReferencePair_left certificate)

/-! ## The executable node adapter into actual spatial observations -/

/-- Convert one terminal-guarded node result into an actual spatial observation: an ordinary result
is passed through untouched, while a direct identity is converted using only actual explicit
substituents.  The direct conversion may refuse (`none`) when the non-guarded endpoint has no
explicit substituent; the guarded side's reference is always the certificate's first candidate. -/
def localizedRule3TerminalGuardedNodeResultToSpatialNodeResult?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (result : LocalizedRule3TerminalGuardedNodeResult input carrierFuel) :
    Option input.LocalizedRule3SpatialNodeResult :=
  match result with
  | .ordinary observation => some observation
  | .direct identity => localizedRule3TerminalGuardedDirectObservation? input identity

/-- Lift a whole guarded node outcome into the nested-option discipline of the extended node
evaluator.  Outer `none` means refusal or unresolved computation; inner `none` means "resolved,
but no geometrical unit".  An accepted guard whose direct conversion refuses is an outer refusal,
which is the documented domain restriction of the adapter. -/
def localizedRule3TerminalGuardedSpatialOutcome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (value : Option (Option (LocalizedRule3TerminalGuardedNodeResult input carrierFuel))) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  match value with
  | none => none
  | some none => some none
  | some (some result) =>
      Option.map Option.some
        (localizedRule3TerminalGuardedNodeResultToSpatialNodeResult? input result)

/-- The executable node adapter: run the terminal-guarded evaluator and reinterpret its result as
an actual `LocalizedRule3SpatialNodeResult` outcome.  Fallback branches are the old extended
computation up to the identity reinterpretation; an accepted guard yields the direct observation
built from actual explicit substituents. -/
def localizedRule3TerminalGuardedSpatialNodeWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  localizedRule3TerminalGuardedSpatialOutcome input
    (localizedRule3TerminalGuardedNodeWithExec? input target occurrence view callback excluded)

/-- Callback demand of the adapted node evaluator.  It is exactly the demand of the terminal-guarded
evaluator, hence empty on every accepted guard and the full extended-node demand on every fallback
branch.  No sibling demand is added, removed or identified with a phantom duplicate. -/
def localizedRule3TerminalGuardedSpatialNodeCallbackRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    List (List (input.LocalizedRerootCursor carrierFuel)) :=
  rule3TerminalGuardedNodeCallbackRequests input target occurrence view

/-- The adapter's callback demand is the guarded evaluator's actual reduced demand. -/
theorem localizedRule3TerminalGuardedSpatialNodeCallbackRequests_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedRule3TerminalGuardedSpatialNodeCallbackRequests input target occurrence view =
      rule3TerminalGuardedNodeCallbackRequests input target occurrence view :=
  rfl

/-- On an accepted guard the adapter demands no callback at all. -/
theorem localizedRule3TerminalGuardedSpatialNodeCallbackRequests_eq_nil_of_guard
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (witness : LocalizedRule3TerminalGuardWitness input target view topology)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (guardComputed : localizedRule3TerminalGuard? input target view topology = some witness) :
    localizedRule3TerminalGuardedSpatialNodeCallbackRequests input target occurrence view = [] := by
  rw [localizedRule3TerminalGuardedSpatialNodeCallbackRequests_eq]
  exact rule3TerminalGuardedNodeCallbackRequests_eq_nil_of_guard input target occurrence view
    topology witness oddRoute ordinaryRoute topologyComputed guardComputed

/-- The adapter's demand is always a sublist of the extended-node demand: only an accepted guard
removes demand, and fallback branches retain it verbatim. -/
theorem localizedRule3TerminalGuardedSpatialNodeCallbackRequests_sublist
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (localizedRule3TerminalGuardedSpatialNodeCallbackRequests input target occurrence view).Sublist
      (input.rule3ExtendedNodeCallbackRequests occurrence) := by
  rw [localizedRule3TerminalGuardedSpatialNodeCallbackRequests_eq]
  exact rule3TerminalGuardedNodeCallbackRequests_sublist input target occurrence view

/-- **Callback locality of the adapter.**  Callbacks that agree on the actual reduced request list
produce the same adapted outcome. -/
theorem localizedRule3TerminalGuardedSpatialNode_callback_local
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn
      (localizedRule3TerminalGuardedSpatialNodeCallbackRequests input target occurrence view)
      before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    localizedRule3TerminalGuardedSpatialNodeWithExec? input
        target occurrence view before excluded =
      localizedRule3TerminalGuardedSpatialNodeWithExec? input
        target occurrence view after excluded := by
  unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
  exact congrArg (fun value => localizedRule3TerminalGuardedSpatialOutcome input value)
    (rule3TerminalGuardedNode_callback_local input target occurrence view before after agree excluded)

/-- The reinterpretation is the identity on an ordinary (fallback) outcome.  This is what makes
every fallback branch observably the old computation. -/
theorem localizedRule3TerminalGuardedSpatialOutcome_ordinary
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (value : Option (Option input.LocalizedRule3SpatialNodeResult)) :
    localizedRule3TerminalGuardedSpatialOutcome input
      (localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input value) = value := by
  unfold localizedRule3TerminalGuardedSpatialOutcome localizedRule3TerminalGuardedOrdinary
    localizedRule3TerminalGuardedNodeResultToSpatialNodeResult?
  cases value with
  | none => rfl
  | some inner =>
      cases inner with
      | none => rfl
      | some observation => rfl

/-- The reinterpretation of a non-excluded direct result is exactly the direct observation map. -/
theorem localizedRule3TerminalGuardedSpatialOutcome_direct
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    localizedRule3TerminalGuardedSpatialOutcome input
        (some (some (LocalizedRule3TerminalGuardedNodeResult.direct identity))) =
      Option.map Option.some
        (localizedRule3TerminalGuardedDirectObservation? input identity) :=
  rfl

/-! ## The precise observational relation -/

/-- Precise agreement between an old spatial outcome and an adapted outcome: the same physical
left and right atoms, the same unit geometry, the same physical unit id and the same Rule-3
priority, all at the level of the nested option.  Diagnostic raw references are deliberately not
projected. -/
def LocalizedRule3SpatialNodeObservationCompatible
    (input : CertifiedLocalizedCIPInput)
    (old fresh : Option input.LocalizedRule3SpatialNodeResult) : Prop :=
  Option.map (fun observation => observation.left) fresh =
      Option.map (fun observation => observation.left) old ∧
    Option.map (fun observation => observation.right) fresh =
      Option.map (fun observation => observation.right) old ∧
    Option.map (fun observation => observation.unit.geometry) fresh =
      Option.map (fun observation => observation.unit.geometry) old ∧
    Option.map (fun observation => observation.physicalUnitId) fresh =
      Option.map (fun observation => observation.physicalUnitId) old ∧
    Option.map (fun observation => observation.unit.geometry.priority) fresh =
      Option.map (fun observation => observation.unit.geometry.priority) old

/-- The precise observational relation is reflexive. -/
theorem LocalizedRule3SpatialNodeObservationCompatible_refl
    (input : CertifiedLocalizedCIPInput)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    LocalizedRule3SpatialNodeObservationCompatible input observation observation :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exclusion test on an optional spatial observation: absent observations are never excluded. -/
def localizedRule3SpatialOptionExcluded
    (input : CertifiedLocalizedCIPInput)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult) : Bool :=
  match observation with
  | none => false
  | some observation => excluded.contains observation.physicalUnitId

/-- **Exclusion membership agreement.**  Compatible outcomes have exactly the same exclusion
behaviour at the node evaluator's physical-unit check. -/
theorem LocalizedRule3SpatialNodeObservationCompatible.excluded_eq
    (input : CertifiedLocalizedCIPInput)
    {old fresh : Option input.LocalizedRule3SpatialNodeResult}
    (compatible : LocalizedRule3SpatialNodeObservationCompatible input old fresh)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    localizedRule3SpatialOptionExcluded input excluded fresh =
      localizedRule3SpatialOptionExcluded input excluded old := by
  obtain ⟨_, _, _, physicalEq, _⟩ := compatible
  cases fresh with
  | none =>
      cases old with
      | none => rfl
      | some oldObservation => simp at physicalEq
  | some freshObservation =>
      cases old with
      | none => simp at physicalEq
      | some oldObservation =>
          have unitEq : freshObservation.physicalUnitId = oldObservation.physicalUnitId := by
            simpa using physicalEq
          simp [localizedRule3SpatialOptionExcluded, unitEq]

/-- **Common observable agreement.**  Compatible outcomes have the same physical left and right
atoms and the same geometry at the option level; this is exactly the comparator-visible projection
of the extended key and it contains no diagnostic raw reference. -/
theorem LocalizedRule3SpatialNodeObservationCompatible.commonObservable_eq
    (input : CertifiedLocalizedCIPInput)
    {old fresh : Option input.LocalizedRule3SpatialNodeResult}
    (compatible : LocalizedRule3SpatialNodeObservationCompatible input old fresh) :
    Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable fresh =
      Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable old := by
  obtain ⟨leftEq, rightEq, geometryEq, _, _⟩ := compatible
  cases fresh with
  | none =>
      cases old with
      | none => rfl
      | some oldObservation => simp at leftEq
  | some freshObservation =>
      cases old with
      | none => simp at leftEq
      | some oldObservation =>
          have leftValue : freshObservation.left = oldObservation.left := by
            simpa using leftEq
          have rightValue : freshObservation.right = oldObservation.right := by
            simpa using rightEq
          have geometryValue : freshObservation.unit.geometry =
              oldObservation.unit.geometry := by
            simpa using geometryEq
          simp [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable,
            leftValue, rightValue, geometryValue]

/-! ## Success refinement from the old production node -/

/-- On the ordinary route with a successfully computed old extended node, the old spatial unit
computation succeeded.  This is the production node's own branch structure: the extended evaluator
delegates to the short-circuit node, whose ordinary route returns the spatial unit through the
option monad, so an outer success forces the unit computation to be `some`. -/
theorem localizedRule3TerminalGuardedNode_spatial_of_extended_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = some observation) :
    ∃ result, input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view callback = some result := by
  unfold localizedRule3ExtendedShortCircuitNodeWithExec? at computed
  rw [oddRoute] at computed
  dsimp only at computed
  unfold localizedRule3ShortCircuitNodeWithExec? at computed
  rw [ordinaryRoute] at computed
  dsimp only at computed
  cases spatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view callback with
  | none => simp [spatial] at computed
  | some result => exact ⟨result, rfl⟩

/-- **Success refinement from the old production node.**  Every former old extended-node success
(`some observation`, with the production recursive frame callback at any budget) is preserved by the
adapted evaluator as `some fresh`, and `fresh` agrees with `observation` on the physical left/right
atoms, the unit geometry, the physical unit id and the Rule-3 priority.  Only diagnostic raw
references may differ, and only because the guarded side omits them and the adapter replaces them by
actual explicit substituents. -/
theorem localizedRule3TerminalGuardedSpatialNodeWithExec?_refines_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (budget : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
      excluded = some observation) :
    ∃ fresh : Option input.LocalizedRule3SpatialNodeResult,
      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence view
        (fun cursors =>
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
        excluded = some fresh ∧
      LocalizedRule3SpatialNodeObservationCompatible input observation fresh := by
  unfold localizedRule3TerminalGuardedSpatialNodeWithExec?
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      have nodeEq : localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
          (fun cursors =>
            input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
          excluded =
          localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
            (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
              (fun cursors =>
                input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
              excluded) := by
        simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute]
      refine ⟨observation, ?_,
        LocalizedRule3SpatialNodeObservationCompatible_refl input observation⟩
      rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary, computed]
  | none =>
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | none =>
          have nodeEq : localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
              (fun cursors =>
                input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
              excluded =
              localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
                (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
                  (fun cursors =>
                    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
                  excluded) := by
            simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute, ordinaryRoute]
          refine ⟨observation, ?_,
            LocalizedRule3SpatialNodeObservationCompatible_refl input observation⟩
          rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary, computed]
      | some ordinaryCertificate =>
          cases topologyComputed :
              input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none =>
              have nodeEq : localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
                  (fun cursors =>
                    input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                      target view budget cursors)
                  excluded =
                  localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
                    (input.localizedRule3ExtendedShortCircuitNodeWithExec?
                      target occurrence view
                      (fun cursors =>
                        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                          target view budget cursors)
                      excluded) := by
                simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute, ordinaryRoute,
                  topologyComputed]
              refine ⟨observation, ?_,
                LocalizedRule3SpatialNodeObservationCompatible_refl input observation⟩
              rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary, computed]
          | some topology =>
              cases guardComputed :
                  localizedRule3TerminalGuard? input target view topology with
              | none =>
                  have nodeEq : localizedRule3TerminalGuardedNodeWithExec?
                      input target occurrence view
                      (fun cursors =>
                        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                          target view budget cursors)
                      excluded =
                      localizedRule3TerminalGuardedOrdinary (carrierFuel := carrierFuel) input
                        (input.localizedRule3ExtendedShortCircuitNodeWithExec?
                          target occurrence view
                          (fun cursors =>
                            input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                              target view budget cursors)
                          excluded) := by
                    simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute, ordinaryRoute,
                      topologyComputed, guardComputed]
                  refine ⟨observation, ?_,
                    LocalizedRule3SpatialNodeObservationCompatible_refl input observation⟩
                  rw [nodeEq, localizedRule3TerminalGuardedSpatialOutcome_ordinary, computed]
              | some witness =>
                  let identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel :=
                    { topology := topology, side := witness.side }
                  have nodeEq : localizedRule3TerminalGuardedNodeWithExec?
                      input target occurrence view
                      (fun cursors =>
                        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                          target view budget cursors)
                      excluded =
                      some
                        (if excluded.contains identity.physicalUnitId then
                          none
                        else
                          some (LocalizedRule3TerminalGuardedNodeResult.direct identity)) := by
                    simp [localizedRule3TerminalGuardedNodeWithExec?, oddRoute, ordinaryRoute,
                      topologyComputed, guardComputed, identity]
                  obtain ⟨result, resultComputed, resultObservable⟩ :=
                    localizedRule3TerminalGuardedNodeWithExec?_agrees_with_extended input
                      target occurrence view budget excluded observation computed
                  have resultEq : result =
                      (if excluded.contains identity.physicalUnitId then
                        none
                      else
                        some (LocalizedRule3TerminalGuardedNodeResult.direct identity)) := by
                    have combined := resultComputed.symm.trans nodeEq
                    simpa using combined
                  by_cases excludedCase : excluded.contains identity.physicalUnitId
                  · have resultNone : result = none := by
                      rw [resultEq, if_pos excludedCase]
                    refine ⟨none, ?_, ?_⟩
                    · rw [nodeEq, if_pos excludedCase]
                      simp [localizedRule3TerminalGuardedSpatialOutcome]
                    · have observationNone : observation = none := by
                        have observableNone := resultObservable
                        rw [resultNone] at observableNone
                        simp only [Option.map_none] at observableNone
                        cases observation with
                        | none => rfl
                        | some oldObservation => simp at observableNone
                      rw [observationNone]
                      exact LocalizedRule3SpatialNodeObservationCompatible_refl input none
                  · cases observation with
                    | none =>
                        have resultSome : result =
                            some (LocalizedRule3TerminalGuardedNodeResult.direct identity) := by
                          rw [resultEq, if_neg excludedCase]
                        have observableSome := resultObservable
                        rw [resultSome] at observableSome
                        simp at observableSome
                    | some oldObservation =>
                        have resultSome : result =
                            some (LocalizedRule3TerminalGuardedNodeResult.direct identity) := by
                          rw [resultEq, if_neg excludedCase]
                        have observableEq :
                            LocalizedRule3TerminalGuardedIdentity.observable identity =
                              LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable
                                oldObservation := by
                          have observableSome := resultObservable
                          rw [resultSome] at observableSome
                          simpa using observableSome
                        have oldLeft : oldObservation.left = identity.topology.left := by
                          have projected := congrArg
                            (fun observable :
                              LocalizedRule3TerminalGuardedObservable input => observable.left)
                            observableEq
                          simpa [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable,
                            LocalizedRule3TerminalGuardedIdentity.observable]
                            using projected.symm
                        have oldRight : oldObservation.right = identity.topology.right := by
                          have projected := congrArg
                            (fun observable :
                              LocalizedRule3TerminalGuardedObservable input => observable.right)
                            observableEq
                          simpa [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable,
                            LocalizedRule3TerminalGuardedIdentity.observable]
                            using projected.symm
                        have oldGeometry : oldObservation.unit.geometry =
                            OfficialRule3Geometry.nonstereogenic := by
                          have projected := congrArg
                            (fun observable :
                              LocalizedRule3TerminalGuardedObservable input => observable.geometry)
                            observableEq
                          simpa [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable,
                            LocalizedRule3TerminalGuardedIdentity.observable]
                            using projected.symm
                        have oldPhysical : oldObservation.physicalUnitId =
                            identity.physicalUnitId := by
                          simp only [LocalizedRule3SpatialNodeResult.physicalUnitId,
                            LocalizedRule3TerminalGuardedIdentity.physicalUnitId,
                            oldLeft, oldRight]
                        obtain ⟨spatialResult, spatial⟩ :=
                          localizedRule3TerminalGuardedNode_spatial_of_extended_some input
                            target occurrence view
                            (fun cursors =>
                              input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                                target view budget cursors)
                            excluded (some oldObservation) oddRoute ordinaryRoute computed
                        obtain ⟨leftEndpoint, rightEndpoint, unit, decomposition,
                          leftComputed, rightComputed, unitComputed⟩ :=
                          localizedRule3TerminalGuardedNode_old_spatial_components input
                            target occurrence view
                            (fun cursors =>
                              input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                                target view budget cursors)
                            topology topologyComputed spatialResult spatial
                        have leftExists : ∃ candidate,
                            localizedRule3CanonicalExplicitSubstituent?
                              input identity.topology.left identity.topology.right =
                                some candidate := by
                          obtain ⟨candidate, candidateComputed⟩ :=
                            localizedRule3CanonicalExplicitSubstituent?_isSome_of_shortCircuitEndpointPriorityExec?_some
                              input target view
                              (fun cursors =>
                                input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                                  target view budget cursors)
                              topology.left topology.right topology.leftCursor
                              leftEndpoint leftComputed
                          exact ⟨candidate, by simpa [identity] using candidateComputed⟩
                        have rightExists : ∃ candidate,
                            localizedRule3CanonicalExplicitSubstituent?
                              input identity.topology.right identity.topology.left =
                                some candidate := by
                          obtain ⟨candidate, candidateComputed⟩ :=
                            localizedRule3CanonicalExplicitSubstituent?_isSome_of_shortCircuitEndpointPriorityExec?_some
                              input target view
                              (fun cursors =>
                                input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                                  target view budget cursors)
                              topology.right topology.left topology.rightCursor
                              rightEndpoint rightComputed
                          exact ⟨candidate, by simpa [identity] using candidateComputed⟩
                        obtain ⟨candidateObservation, candidateComputed⟩ :=
                          localizedRule3TerminalGuardedDirectObservation?_isSome_of_candidates input
                            identity leftExists rightExists
                        have candidateLeft : candidateObservation.left =
                            identity.topology.left :=
                          localizedRule3TerminalGuardedDirectObservation?_left input identity
                            candidateObservation candidateComputed
                        have candidateRight : candidateObservation.right =
                            identity.topology.right :=
                          localizedRule3TerminalGuardedDirectObservation?_right input identity
                            candidateObservation candidateComputed
                        have candidateGeometry : candidateObservation.unit.geometry =
                            OfficialRule3Geometry.nonstereogenic :=
                          localizedRule3TerminalGuardedDirectObservation?_geometry input identity
                            candidateObservation candidateComputed
                        have candidatePhysical : candidateObservation.physicalUnitId =
                            identity.physicalUnitId :=
                          localizedRule3TerminalGuardedDirectObservation?_physicalUnitId input
                            identity candidateObservation candidateComputed
                        refine ⟨some candidateObservation, ?_, ?_⟩
                        · rw [nodeEq, if_neg excludedCase]
                          simp [localizedRule3TerminalGuardedSpatialOutcome,
                            localizedRule3TerminalGuardedNodeResultToSpatialNodeResult?,
                            candidateComputed]
                        · unfold LocalizedRule3SpatialNodeObservationCompatible
                          refine ⟨?_, ?_, ?_, ?_, ?_⟩
                          · simp [candidateLeft, oldLeft]
                          · simp [candidateRight, oldRight]
                          · simp [candidateGeometry, oldGeometry]
                          · simp [candidatePhysical, oldPhysical]
                          · simp [candidateGeometry, oldGeometry]

/-- **Success refinement, inner-observation form.**  If the old production node returned an actual
spatial observation, the adapter returns an actual spatial observation with the same physical
left/right atoms, geometry, physical unit id and Rule-3 priority.  This is the form directly usable
by the extended key, whose sparse payload is an inner `LocalizedRule3SpatialNodeResult`. -/
theorem localizedRule3TerminalGuardedSpatialNodeWithExec?_refines_extended_observation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (budget : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (oldObservation : input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
      excluded = some (some oldObservation)) :
    ∃ freshObservation : input.LocalizedRule3SpatialNodeResult,
      localizedRule3TerminalGuardedSpatialNodeWithExec? input target occurrence view
        (fun cursors =>
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
        excluded = some (some freshObservation) ∧
      freshObservation.left = oldObservation.left ∧
      freshObservation.right = oldObservation.right ∧
      freshObservation.unit.geometry = oldObservation.unit.geometry ∧
      freshObservation.physicalUnitId = oldObservation.physicalUnitId ∧
      freshObservation.unit.geometry.priority = oldObservation.unit.geometry.priority := by
  obtain ⟨fresh, freshComputed, compatible⟩ :=
    localizedRule3TerminalGuardedSpatialNodeWithExec?_refines_extended input target occurrence view
      budget excluded (some oldObservation) computed
  obtain ⟨leftEq, rightEq, geometryEq, physicalEq, priorityEq⟩ := compatible
  cases fresh with
  | none => simp at leftEq
  | some freshObservation =>
      refine ⟨freshObservation, freshComputed, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using leftEq
      · simpa using rightEq
      · simpa using geometryEq
      · simpa using physicalEq
      · simpa using priorityEq

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter

/-! ## Kernel-authority certificates -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3CanonicalExplicitSubstituent?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3CanonicalExplicitSubstituent?_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3CanonicalExplicitSubstituent?_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3CanonicalExplicitSubstituent?_ne_endpoint
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.exists_cons_of_localizedRule3ShortCircuitEndpointPriorityExec?_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3CanonicalExplicitSubstituent?_isSome_of_shortCircuitEndpointPriorityExec?_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3CanonicalExplicitSubstituent?_terminalReferencePair_left
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.DeclarativeLocalizedRule3TerminalGuardedObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_components
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_sound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_left
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_right
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_geometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_unit_priority
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_physicalUnitId
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_observable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_isSome_of_candidates
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_leftCertificate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedDirectObservation?_rightCertificate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedNodeResultToSpatialNodeResult?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialOutcome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNodeWithExec?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNodeCallbackRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNodeCallbackRequests_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNodeCallbackRequests_eq_nil_of_guard
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNodeCallbackRequests_sublist
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNode_callback_local
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialOutcome_ordinary
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialOutcome_direct
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.LocalizedRule3SpatialNodeObservationCompatible
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.LocalizedRule3SpatialNodeObservationCompatible_refl
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3SpatialOptionExcluded
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.LocalizedRule3SpatialNodeObservationCompatible.excluded_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.LocalizedRule3SpatialNodeObservationCompatible.commonObservable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedNode_spatial_of_extended_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNodeWithExec?_refines_extended
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedObservationAdapter.localizedRule3TerminalGuardedSpatialNodeWithExec?_refines_extended_observation
