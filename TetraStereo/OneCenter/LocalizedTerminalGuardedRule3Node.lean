import TetraStereo.OneCenter.LocalizedTerminalEndpointObservationAbsorption
import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery

set_option autoImplicit false

/-!
# Terminal-guarded ordinary-node Rule-3 observation evaluation

This module integrates the independently checked terminal-reference guard of
`CertifiedLocalizedCIPInput.TerminalEndpointObservation` into ordinary-node observation evaluation.
The guard is the *actual* computation `terminalReferencePair?`: it performs the real candidate and
reference-cursor lookups, the executable leaf and structural-nonunit checks, the label and root
distance comparisons, and the actual compound Rules-4b--5 key compilations and comparison under the
supplied dependency view, followed by a successful production two-terminal frame computation.  No
field of the certificate is assumed.

The new evaluator `localizedRule3TerminalGuardedNodeWithExec?` mirrors the branch order of
`localizedRule3ExtendedShortCircuitNodeWithExec?`.  On the ordinary route, once the physical
endpoint topology is recovered, it runs the guard on the left endpoint and then, if necessary, on
the right endpoint.  When a guard accepts, the evaluator returns a
`LocalizedRule3TerminalGuardedNodeResult.direct` identity: the physical topology, the accepted side
and the nonstereogenic geometry.  It does **not** invent the opposite raw reference or frame, and it
does not inspect the opposite endpoint at all.  In every other case the evaluator falls back to the
existing extended evaluator and tags its result `ordinary`; the fallback is literally the old
computation, so no success is lost.

The callback demand is reduced accordingly: `rule3TerminalGuardedNodeCallbackRequests` is `[]` on
the guarded branches and the original `rule3ExtendedNodeCallbackRequests` on every fallback branch.
In particular the guarded branch demands neither a callback for the opposite endpoint nor any
sibling demand.  Callback locality is proved for the full reduced request list.

The geometry claim is *not* assumed from the guard's shape.  The guard certificate carries a
successful production frame computation, and the two-terminal frame theorem is applied only to
that successful computation: the certificate's own frame keys are the two canonical terminal keys
(the module never claims that terminal shape alone produces a frame).  For agreement with the old
evaluator, the same theorem is applied to the old evaluator's *successful* production callback at
its own budget; only successes are compared.

The guard remains fully view-dependent: the compound Rules-4b--5 key compilations and the frame
computation consume the supplied `LocalizedDependencyView`.  Nothing here is called graph-only or
view-independent, and no general constitutional tie suppression is introduced.

No semantic-model existence or nonexistence and no chemical-realizability claim is made.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedRule3Node

open TetraStereo.OneCenter
open TerminalEndpointObservation

/-! ## Explicit observable and result types -/

/-- Which endpoint of the physical double-bond topology accepted the terminal guard. -/
inductive LocalizedRule3TerminalGuardSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The observable identity emitted by an accepted guard.  It contains the actual physical endpoint
topology and the accepted side; its geometry is nonstereogenic by construction.  It deliberately
does not contain an opposite raw reference, opposite frame or opposite priority. -/
structure LocalizedRule3TerminalGuardedIdentity
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel
  side : LocalizedRule3TerminalGuardSide

/-- Physical unit identity of a guarded identity: the canonical ordered endpoint pair. -/
def LocalizedRule3TerminalGuardedIdentity.physicalUnitId
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    input.LocalizedRule3PhysicalUnitId :=
  input.localizedRule3PhysicalUnitId identity.topology.left identity.topology.right

/-- The common nonstereogenic observable projection.  This is the agreement granularity between the
guarded identity and the old observation: the two physical endpoints and the geometry.  No raw
reference is part of this projection. -/
structure LocalizedRule3TerminalGuardedObservable (input : CertifiedLocalizedCIPInput) where
  left : input.Atom
  right : input.Atom
  geometry : OfficialRule3Geometry
  deriving DecidableEq, Repr

/-- Observable projection of a guarded identity. -/
def LocalizedRule3TerminalGuardedIdentity.observable
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    LocalizedRule3TerminalGuardedObservable input :=
  { left := identity.topology.left
    right := identity.topology.right
    geometry := OfficialRule3Geometry.nonstereogenic }

/-- Observable projection of an old spatial node observation.  This retains the old left and right
endpoints and the old unit geometry; the possibly opposite raw references are not projected. -/
def LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable
    {input : CertifiedLocalizedCIPInput}
    (observation : input.LocalizedRule3SpatialNodeResult) :
    LocalizedRule3TerminalGuardedObservable input :=
  { left := observation.left
    right := observation.right
    geometry := observation.unit.geometry }

/-- The terminal-guarded node result: either a directly accepted nonstereogenic identity or the
untouched ordinary observation produced by the existing extended evaluator. -/
inductive LocalizedRule3TerminalGuardedNodeResult
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  | direct (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel)
  | ordinary (observation : input.LocalizedRule3SpatialNodeResult)

/-- Observable projection of a terminal-guarded node result. -/
def LocalizedRule3TerminalGuardedNodeResult.observable
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (result : LocalizedRule3TerminalGuardedNodeResult input carrierFuel) :
    LocalizedRule3TerminalGuardedObservable input :=
  match result with
  | .direct identity => identity.observable
  | .ordinary observation =>
      LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation

@[simp] theorem LocalizedRule3TerminalGuardedNodeResult.observable_direct
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    (LocalizedRule3TerminalGuardedNodeResult.direct identity).observable =
      identity.observable :=
  rfl

@[simp] theorem LocalizedRule3TerminalGuardedNodeResult.observable_ordinary
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observation : input.LocalizedRule3SpatialNodeResult) :
    (LocalizedRule3TerminalGuardedNodeResult.ordinary
        (carrierFuel := carrierFuel) observation).observable =
      LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation :=
  rfl

@[simp] theorem LocalizedRule3TerminalGuardedIdentity.observable_geometry
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    identity.observable.geometry = OfficialRule3Geometry.nonstereogenic :=
  rfl

@[simp] theorem LocalizedRule3TerminalGuardedIdentity.observable_left
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    identity.observable.left = identity.topology.left :=
  rfl

@[simp] theorem LocalizedRule3TerminalGuardedIdentity.observable_right
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel) :
    identity.observable.right = identity.topology.right :=
  rfl

/-! ## The checked guard on one endpoint of a recovered topology -/

/-- A guard witness either certifies the left endpoint (with the opposite endpoint and its cursor
fixed by the recovered topology) or the right endpoint.  The certificate is the actual computed
`TerminalReferencePair`; the constructor index records exactly which side was certified. -/
inductive LocalizedRule3TerminalGuardWitness
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel) where
  | left (certificate : TerminalReferencePair input target view
      topology.left topology.right topology.leftCursor)
  | right (certificate : TerminalReferencePair input target view
      topology.right topology.left topology.rightCursor)

/-- The accepted side of a guard witness. -/
def LocalizedRule3TerminalGuardWitness.side
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (witness : LocalizedRule3TerminalGuardWitness input target view topology) :
    LocalizedRule3TerminalGuardSide :=
  match witness with
  | .left _ => .left
  | .right _ => .right

/-- Run the actual terminal-reference check on the left endpoint first, then on the right endpoint.
The check is the staged executable guard; it performs all source lookups and frame computations
itself and never consults a supplied callback. -/
def localizedRule3TerminalGuard?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel) :
    Option (LocalizedRule3TerminalGuardWitness input target view topology) :=
  match terminalReferencePair? input target view topology.left topology.right topology.leftCursor with
  | some certificate => some (.left certificate)
  | none =>
      match terminalReferencePair? input target view topology.right topology.left topology.rightCursor with
      | some certificate => some (.right certificate)
      | none => none

/-! ## The guarded ordinary-node evaluator -/

/-- The fallback map: the existing extended evaluator's nested option is tagged `ordinary`. -/
def localizedRule3TerminalGuardedOrdinary
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (value : Option (Option input.LocalizedRule3SpatialNodeResult)) :
    Option (Option (LocalizedRule3TerminalGuardedNodeResult input carrierFuel)) :=
  Option.map (Option.map (fun observation =>
    LocalizedRule3TerminalGuardedNodeResult.ordinary (input := input) (carrierFuel := carrierFuel)
      observation)) value

/-- The ordinary-node terminal-guarded evaluator.

Branch order is exactly that of the existing extended evaluator, so the fallback cases are the old
computation.  On the ordinary route with a recovered physical topology, the left guard is tried
first and the right guard second.  An accepted guard emits the direct nonstereogenic identity and
performs the same physical-unit exclusion as the ordinary route.  Every other case falls back to the
extended evaluator, which remains the only user of the callback. -/
def localizedRule3TerminalGuardedNodeWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option (LocalizedRule3TerminalGuardedNodeResult input carrierFuel)) :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | some _ =>
      localizedRule3TerminalGuardedOrdinary input
        (input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target occurrence view callback excluded)
  | none =>
      match input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | none =>
          localizedRule3TerminalGuardedOrdinary input
            (input.localizedRule3ExtendedShortCircuitNodeWithExec?
              target occurrence view callback excluded)
      | some _ =>
          match input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none =>
              localizedRule3TerminalGuardedOrdinary input
                (input.localizedRule3ExtendedShortCircuitNodeWithExec?
                  target occurrence view callback excluded)
          | some topology =>
              match localizedRule3TerminalGuard? input target view topology with
              | some witness =>
                  let identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel :=
                    { topology := topology, side := witness.side }
                  some
                    (if excluded.contains identity.physicalUnitId then
                      none
                    else
                      some (LocalizedRule3TerminalGuardedNodeResult.direct identity))
              | none =>
                  localizedRule3TerminalGuardedOrdinary input
                    (input.localizedRule3ExtendedShortCircuitNodeWithExec?
                      target occurrence view callback excluded)

/-! ## The explicit reduced callback request list -/

/-- Callback demand of the terminal-guarded evaluator.  It is `[]` exactly on the branches where a
guard accepts, and the full original extended-node demand on every fallback branch.  In particular
an accepted guard demands no callback at all, hence not the opposite endpoint's callback and no
sibling-cycle demand. -/
def rule3TerminalGuardedNodeCallbackRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    List (List (input.LocalizedRerootCursor carrierFuel)) :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | some _ => input.rule3ExtendedNodeCallbackRequests occurrence
  | none =>
      match input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | none => input.rule3ExtendedNodeCallbackRequests occurrence
      | some _ =>
          match input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none => input.rule3ExtendedNodeCallbackRequests occurrence
          | some topology =>
              match localizedRule3TerminalGuard? input target view topology with
              | some _ => []
              | none => input.rule3ExtendedNodeCallbackRequests occurrence

/-- On an accepted guard the reduced request list is empty: no callback is demanded at all. -/
theorem rule3TerminalGuardedNodeCallbackRequests_eq_nil_of_guard
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
    rule3TerminalGuardedNodeCallbackRequests input target occurrence view = [] := by
  simp only [rule3TerminalGuardedNodeCallbackRequests, oddRoute, ordinaryRoute,
    topologyComputed, guardComputed]

/-- **No sibling-cycle demand on an accepted guard.**  Every request list is absent from the reduced
demand, so in particular no sibling request, no opposite-endpoint request and no other cycle edge is
demanded on the guarded branch. -/
theorem rule3TerminalGuardedNodeCallbackRequests_not_mem_of_guard
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
    (guardComputed : localizedRule3TerminalGuard? input target view topology = some witness)
    (request : List (input.LocalizedRerootCursor carrierFuel)) :
    request ∉ rule3TerminalGuardedNodeCallbackRequests input target occurrence view := by
  rw [rule3TerminalGuardedNodeCallbackRequests_eq_nil_of_guard input target occurrence view
    topology witness oddRoute ordinaryRoute topologyComputed guardComputed]
  simp

/-- In every fallback case, the reduced request list is exactly the existing extended-node list. -/
theorem rule3TerminalGuardedNodeCallbackRequests_eq_extended_of_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (guardComputed : localizedRule3TerminalGuard? input target view topology = none) :
    rule3TerminalGuardedNodeCallbackRequests input target occurrence view =
      input.rule3ExtendedNodeCallbackRequests occurrence := by
  simp only [rule3TerminalGuardedNodeCallbackRequests, oddRoute, ordinaryRoute,
    topologyComputed, guardComputed]

/-- The reduced request list is always a sublist of the extended-node request list: the guarded
branches only remove demand, and the fallback branches retain it verbatim. -/
theorem rule3TerminalGuardedNodeCallbackRequests_sublist
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (rule3TerminalGuardedNodeCallbackRequests input target occurrence view).Sublist
      (input.rule3ExtendedNodeCallbackRequests occurrence) := by
  unfold rule3TerminalGuardedNodeCallbackRequests
  repeat' split
  all_goals first
    | exact List.Sublist.refl _
    | exact List.nil_sublist _

/-! ## Callback locality -/

/-- **Callback locality.**  Two callbacks that agree on the reduced request list produce exactly the
same guarded evaluation.  A guarded branch never invokes the callback; every fallback branch is the
old evaluator, whose locality theorem is applied to the retained requests. -/
theorem rule3TerminalGuardedNode_callback_local
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn
      (rule3TerminalGuardedNodeCallbackRequests input target occurrence view) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    localizedRule3TerminalGuardedNodeWithExec? input
        target occurrence view before excluded =
      localizedRule3TerminalGuardedNodeWithExec? input
        target occurrence view after excluded := by
  unfold localizedRule3TerminalGuardedNodeWithExec?
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      have extendedAgree : input.Rule3CallbackAgreesOn
          (input.rule3ExtendedNodeCallbackRequests occurrence) before after := by
        intro cursors member
        exact agree cursors (by
          simpa only [rule3TerminalGuardedNodeCallbackRequests, oddRoute] using member)
      exact congrArg (localizedRule3TerminalGuardedOrdinary input)
        (input.rule3ExtendedNode_callback_local target occurrence view before after
          extendedAgree excluded)
  | none =>
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | none =>
          have extendedAgree : input.Rule3CallbackAgreesOn
              (input.rule3ExtendedNodeCallbackRequests occurrence) before after := by
            intro cursors member
            exact agree cursors (by
              simpa only [rule3TerminalGuardedNodeCallbackRequests, oddRoute,
                ordinaryRoute] using member)
          exact congrArg (localizedRule3TerminalGuardedOrdinary input)
            (input.rule3ExtendedNode_callback_local target occurrence view before after
              extendedAgree excluded)
      | some certificate =>
          cases topologyComputed :
              input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none =>
              have extendedAgree : input.Rule3CallbackAgreesOn
                  (input.rule3ExtendedNodeCallbackRequests occurrence) before after := by
                intro cursors member
                exact agree cursors (by
                  simpa only [rule3TerminalGuardedNodeCallbackRequests, oddRoute,
                    ordinaryRoute, topologyComputed] using member)
              exact congrArg (localizedRule3TerminalGuardedOrdinary input)
                (input.rule3ExtendedNode_callback_local target occurrence view before after
                  extendedAgree excluded)
          | some topology =>
              cases guardComputed : localizedRule3TerminalGuard? input target view topology with
              | some witness =>
                  simp only [guardComputed]
              | none =>
                  have extendedAgree : input.Rule3CallbackAgreesOn
                      (input.rule3ExtendedNodeCallbackRequests occurrence) before after := by
                    intro cursors member
                    exact agree cursors (by
                      simpa only [rule3TerminalGuardedNodeCallbackRequests, oddRoute,
                        ordinaryRoute, topologyComputed, guardComputed] using member)
                  simp only [guardComputed]
                  exact congrArg (localizedRule3TerminalGuardedOrdinary input)
                    (input.rule3ExtendedNode_callback_local target occurrence view before after
                      extendedAgree excluded)

/-- The guarded branch's evaluation is independent of the callback, stated directly.  This is the
explicit form of the reduced demand: once the guard accepts, no callback value is inspected. -/
theorem localizedRule3TerminalGuardedNodeWithExec?_guard_callback_independent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (witness : LocalizedRule3TerminalGuardWitness input target view topology)
    (firstCallback secondCallback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (guardComputed : localizedRule3TerminalGuard? input target view topology = some witness) :
    localizedRule3TerminalGuardedNodeWithExec? input
        target occurrence view firstCallback excluded =
      localizedRule3TerminalGuardedNodeWithExec? input
        target occurrence view secondCallback excluded := by
  unfold localizedRule3TerminalGuardedNodeWithExec?
  simp only [oddRoute, ordinaryRoute, topologyComputed, guardComputed]

/-! ## Production-callback endpoint soundness from the certificate -/

private theorem option_some_bind_apply {α β : Type} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-- If a successful endpoint selector's callback is faithful on the certificate's two reference
cursors (every returned frame carries exactly the two canonical terminal keys), then the selector's
result is exactly the certificate's nonstereogenic endpoint.  The certificate itself supplies the
constitutional and Rules-4b--5 ties; the callback hypothesis only constrains a *successful* frame. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_terminalPair_of_callback_keys
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (faithful : ∀ frame, callback [certificate.firstCursor, certificate.secondCursor] = some frame →
      frame.keys =
        [terminalRule3Key input certificate.firstCursor,
         terminalRule3Key input certificate.secondCursor])
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (frameComputed : callback [certificate.firstCursor, certificate.secondCursor] = some frame) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view callback endpoint partner endpointCursor =
      some
        { firstCursor := certificate.firstCursor
          secondCursor := certificate.secondCursor
          rule3Frame := frame
          endpointFrame := certificate.endpointFrame } := by
  have frameKeys := faithful frame frameComputed
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
  rw [certificate.candidates]
  dsimp only
  rw [certificate.firstComputed, option_some_bind_apply,
      certificate.secondComputed, option_some_bind_apply, frameComputed,
      option_some_bind_apply]
  try dsimp only
  rw [frameKeys]
  try dsimp only
  rw [certificate.firstRule45Computed, option_some_bind_apply,
      certificate.secondRule45Computed, option_some_bind_apply]
  rfl

/-- If a successful endpoint selector's callback is faithful on the certificate's two reference
cursors (every returned frame carries exactly the two canonical terminal keys), then the selector's
result is exactly the certificate's nonstereogenic endpoint.  The certificate itself supplies the
constitutional and Rules-4b--5 ties; the callback hypothesis only constrains a *successful* frame. -/
theorem endpointResult_eq_shortCircuitEndpoint_of_callback_keys
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (faithful : ∀ frame, callback [certificate.firstCursor, certificate.secondCursor] = some frame →
      frame.keys =
        [terminalRule3Key input certificate.firstCursor,
         terminalRule3Key input certificate.secondCursor])
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view callback endpoint partner endpointCursor = some result) :
    result = certificate.shortCircuitEndpoint := by
  have rootTied : input.compareLocalizedRerootCursorConstitutionalRoot
      certificate.firstCursor certificate.secondCursor = Ordering.eq :=
    compareLocalizedRerootCursorConstitutionalRoot_eq_of_label input
      certificate.firstCursor certificate.secondCursor certificate.labelEq
  have constitutionalTied : input.compareLocalizedConstitutionalCursors?
      certificate.firstCursor certificate.secondCursor = some Ordering.eq :=
    compareLocalizedConstitutionalCursors?_terminal_eq input
      certificate.firstCursor certificate.secondCursor certificate.firstChildren
      certificate.secondChildren certificate.labelEq certificate.distanceEq
  unfold localizedRule3ShortCircuitEndpointPriorityExec? at computed
  rw [certificate.candidates] at computed
  dsimp only at computed
  rw [certificate.firstComputed, option_some_bind_apply,
      certificate.secondComputed, option_some_bind_apply] at computed
  rw [rootTied] at computed
  dsimp only at computed
  rw [constitutionalTied] at computed
  simp only [] at computed
  cases frameComputed : callback [certificate.firstCursor, certificate.secondCursor] with
  | none =>
      unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec? at computed
      rw [certificate.candidates] at computed
      dsimp only at computed
      rw [certificate.firstComputed, option_some_bind_apply,
          certificate.secondComputed, option_some_bind_apply, frameComputed] at computed
      simp at computed
  | some frame =>
      rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_terminalPair_of_callback_keys
            certificate callback faithful frame frameComputed,
          option_some_bind_apply] at computed
      try dsimp only at computed
      rw [certificate.endpointPriority_eq_nonstereogenic] at computed
      simpa [TerminalReferencePair.shortCircuitEndpoint] using
        (Option.some.inj computed).symm

/-- The production recursive frame callback is faithful on the certificate's reference pair at every
budget at which it actually returns a frame.  This is the only place the two-terminal frame theorem
is used for the old evaluator: it is applied to the callback's *successful* computation, never to
the mere terminal shape. -/
theorem endpointResult_eq_shortCircuitEndpoint_production
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {endpoint partner : input.Atom}
    {endpointCursor : input.LocalizedRerootCursor carrierFuel}
    (certificate : TerminalReferencePair input target view endpoint partner endpointCursor)
    (budget : Nat)
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityExec? target view
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
      endpoint partner endpointCursor = some result) :
    result = certificate.shortCircuitEndpoint := by
  refine endpointResult_eq_shortCircuitEndpoint_of_callback_keys certificate _ ?_ result computed
  intro frame frameComputed
  have frameComputed' : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view budget [certificate.firstCursor, certificate.secondCursor] = some frame :=
    frameComputed
  have positive : 0 < budget := by
    cases budget with
    | zero =>
        simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at frameComputed'
    | succ predecessor => omega
  exact buildLocalizedExtendedShortCircuitRule3FrameExec?_two_terminal input target view
    certificate.firstCursor certificate.secondCursor certificate.firstChildren
    certificate.secondChildren certificate.firstNonunit certificate.secondNonunit
    positive frame frameComputed'

/-! ## Absorption for either guarded side -/

/-- Absorption when the *right* endpoint is the certified one.  This is the mirror of the staged
left-endpoint theorem and needs no opposite frame: the nonstereogenic priority of the certified
endpoint alone forces the unit core geometry. -/
theorem localizedRule3ShortCircuitSpatialUnit?_of_right_nonstereogenic
    (input : CertifiedLocalizedCIPInput)
    (left right : input.Atom)
    (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (rightNonstereogenic : rightEndpoint.priority = LocalizedRule3EndpointPriority.nonstereogenic)
    (doubleBond : input.moleculeGraph.bond left right = 2) :
    ∃ unit,
      input.localizedRule3ShortCircuitSpatialUnit? left right leftEndpoint rightEndpoint =
        some unit ∧
      unit.core.geometry = OfficialRule3Geometry.nonstereogenic := by
  cases leftPriority : leftEndpoint.priority with
  | nonstereogenic =>
      exact
        ⟨{ left := leftEndpoint
           right := rightEndpoint
           core :=
             { leftPriority := leftEndpoint.priority
               rightPriority := rightEndpoint.priority
               geometry := OfficialRule3Geometry.nonstereogenic } },
         by
           simp [localizedRule3ShortCircuitSpatialUnit?,
             localizedRule3DescriptorBearingSpatialUnitOfPriorities?, doubleBond,
             leftPriority, rightNonstereogenic],
         rfl⟩
  | senior reference =>
      exact
        ⟨{ left := leftEndpoint
           right := rightEndpoint
           core :=
             { leftPriority := leftEndpoint.priority
               rightPriority := rightEndpoint.priority
               geometry := OfficialRule3Geometry.nonstereogenic } },
         by
           simp [localizedRule3ShortCircuitSpatialUnit?,
             localizedRule3DescriptorBearingSpatialUnitOfPriorities?, doubleBond,
             leftPriority, rightNonstereogenic],
         rfl⟩

/-! ## Successful callback frame of the old evaluator -/

/-- The old extended-node evaluator at the production recursive callback returns, in the ordinary
short-circuit route, exactly the spatial observation of a spatial unit whose topology is the
recovered physical topology. -/
theorem localizedRule3TerminalGuardedNode_old_spatial_components
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (spatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view callback = some result) :
    ∃ (leftEndpoint rightEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
      (unit : input.LocalizedRule3ShortCircuitSpatialUnitResult),
      result =
        { topology := topology
          leftEndpoint := leftEndpoint
          rightEndpoint := rightEndpoint
          unit := unit } ∧
      input.localizedRule3ShortCircuitEndpointPriorityExec?
          target view callback topology.left topology.right topology.leftCursor =
        some leftEndpoint ∧
      input.localizedRule3ShortCircuitEndpointPriorityExec?
          target view callback topology.right topology.left topology.rightCursor =
        some rightEndpoint ∧
      input.localizedRule3ShortCircuitSpatialUnit?
          topology.left topology.right leftEndpoint rightEndpoint = some unit := by
  unfold localizedRule3ShortCircuitSpatialUnitWithExec? at spatial
  cases found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp [found] at spatial
  | some topologyFound =>
      have topologyEq : topologyFound = topology :=
        Option.some.inj (found.symm.trans topologyComputed)
      subst topologyFound
      simp [found] at spatial
      cases leftComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
          target view callback topology.left topology.right topology.leftCursor with
      | none => simp [leftComputed] at spatial
      | some leftEndpoint =>
          simp [leftComputed] at spatial
          cases rightComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
              target view callback topology.right topology.left topology.rightCursor with
          | none => simp [rightComputed] at spatial
          | some rightEndpoint =>
              simp [rightComputed] at spatial
              cases unitComputed : input.localizedRule3ShortCircuitSpatialUnit?
                  topology.left topology.right leftEndpoint rightEndpoint with
              | none => simp [unitComputed] at spatial
              | some unit =>
                  have decomposition : result =
                      { topology := topology
                        leftEndpoint := leftEndpoint
                        rightEndpoint := rightEndpoint
                        unit := unit } := by
                    simpa [unitComputed] using spatial.symm
                  exact ⟨leftEndpoint, rightEndpoint, unit, decomposition, rfl, rfl, unitComputed⟩

/-- **Geometric absorption, left guard.**  If the old spatial unit's left endpoint is the certified
one, its core geometry is nonstereogenic, independently of the opposite endpoint result. -/
theorem localizedRule3TerminalGuardedNode_spatial_geometry_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (certificate : TerminalReferencePair input target view
      topology.left topology.right topology.leftCursor)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (spatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view callback = some result)
    (leftCertified : result.leftEndpoint = certificate.shortCircuitEndpoint)
    (doubleBond : input.moleculeGraph.bond topology.left topology.right = 2) :
    result.unit.core.geometry = OfficialRule3Geometry.nonstereogenic := by
  obtain ⟨leftEndpoint, rightEndpoint, unit, decomposition, leftComputed, rightComputed,
    unitComputed⟩ :=
    localizedRule3TerminalGuardedNode_old_spatial_components input target occurrence view callback
      topology topologyComputed result spatial
  cases decomposition
  dsimp only at leftCertified
  rw [leftCertified] at unitComputed
  obtain ⟨unit', unitComputed', geometry⟩ :=
    certificate.shortCircuitSpatialUnit?_of_endpoint rightEndpoint doubleBond
  have unitEq : unit = unit' := Option.some.inj (unitComputed.symm.trans unitComputed')
  rw [unitEq]
  exact geometry

/-- **Geometric absorption, right guard.**  Symmetric form for a certified right endpoint. -/
theorem localizedRule3TerminalGuardedNode_spatial_geometry_right
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (certificate : TerminalReferencePair input target view
      topology.right topology.left topology.rightCursor)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (spatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view callback = some result)
    (rightCertified : result.rightEndpoint = certificate.shortCircuitEndpoint)
    (doubleBond : input.moleculeGraph.bond topology.left topology.right = 2) :
    result.unit.core.geometry = OfficialRule3Geometry.nonstereogenic := by
  obtain ⟨leftEndpoint, rightEndpoint, unit, decomposition, leftComputed, rightComputed,
    unitComputed⟩ :=
    localizedRule3TerminalGuardedNode_old_spatial_components input target occurrence view callback
      topology topologyComputed result spatial
  cases decomposition
  dsimp only at rightCertified
  rw [rightCertified] at unitComputed
  obtain ⟨unit', unitComputed', geometry⟩ :=
    localizedRule3ShortCircuitSpatialUnit?_of_right_nonstereogenic input
      topology.left topology.right leftEndpoint certificate.shortCircuitEndpoint
      (by rfl : certificate.shortCircuitEndpoint.priority =
        LocalizedRule3EndpointPriority.nonstereogenic)
      doubleBond
  have unitEq : unit = unit' := Option.some.inj (unitComputed.symm.trans unitComputed')
  rw [unitEq]
  exact geometry

/-- **Observation agreement.**  For the production recursive frame callback at any budget, every
*successful* old extended-node evaluation is reproduced by the guarded evaluator at the common
nonstereogenic observable projection.  The guarded branch agrees by geometric absorption; fallback
branches are the old computation tagged `ordinary`. -/
theorem localizedRule3TerminalGuardedNodeWithExec?_agrees_with_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (budget : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
      excluded = some observation) :
    ∃ result : Option (LocalizedRule3TerminalGuardedNodeResult input carrierFuel),
      localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
        (fun cursors =>
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget cursors)
        excluded = some result ∧
      Option.map LocalizedRule3TerminalGuardedNodeResult.observable result =
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable observation := by
  unfold localizedRule3TerminalGuardedNodeWithExec?
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some _ =>
      refine ⟨Option.map (fun o =>
          LocalizedRule3TerminalGuardedNodeResult.ordinary (carrierFuel := carrierFuel) o)
          observation, by rw [computed]; rfl, ?_⟩
      cases observation with
      | none => rfl
      | some observation =>
          simp [LocalizedRule3TerminalGuardedNodeResult.observable,
            LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable]
  | none =>
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | none =>
          refine ⟨Option.map (fun o =>
            LocalizedRule3TerminalGuardedNodeResult.ordinary (carrierFuel := carrierFuel) o)
            observation, by rw [computed]; rfl, ?_⟩
          cases observation with
          | none => rfl
          | some observation =>
              simp [LocalizedRule3TerminalGuardedNodeResult.observable,
                LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable]
      | some ordinaryCertificate =>
          cases topologyComputed :
              input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none =>
              refine ⟨Option.map (fun o =>
                LocalizedRule3TerminalGuardedNodeResult.ordinary (carrierFuel := carrierFuel) o)
                observation, by rw [computed]; rfl, ?_⟩
              cases observation with
              | none => rfl
              | some observation =>
                  simp [LocalizedRule3TerminalGuardedNodeResult.observable,
                    LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable]
          | some topology =>
              cases guardComputed : localizedRule3TerminalGuard? input target view topology with
              | none =>
                  refine ⟨Option.map (fun o =>
                    LocalizedRule3TerminalGuardedNodeResult.ordinary
                      (carrierFuel := carrierFuel) o) observation, ?_, ?_⟩
                  · simp only [guardComputed]
                    rw [computed]
                    simp [localizedRule3TerminalGuardedOrdinary]
                  · cases observation with
                    | none => rfl
                    | some observation =>
                        simp [LocalizedRule3TerminalGuardedNodeResult.observable,
                          LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable]
              | some witness =>
                  -- Old success through the ordinary short-circuit route.
                  unfold localizedRule3ExtendedShortCircuitNodeWithExec? at computed
                  rw [oddRoute] at computed
                  dsimp only at computed
                  unfold localizedRule3ShortCircuitNodeWithExec? at computed
                  rw [ordinaryRoute] at computed
                  dsimp only at computed
                  cases spatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
                      target occurrence view
                      (fun cursors => input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                        target view budget cursors) with
                  | none => simp [spatial] at computed
                  | some spatialResult =>
                      simp [spatial] at computed
                      -- The old observation is the spatial observation, modulo exclusion.
                      have oldObservation :
                          observation =
                            (if excluded.contains
                                (input.localizedRule3ShortCircuitSpatialObservation
                                  spatialResult).physicalUnitId then
                              none
                            else
                              some (input.localizedRule3ShortCircuitSpatialObservation
                                spatialResult)) := by
                        simpa using computed.symm
                      -- Destructure the spatial result and recover the physical double bond.
                      obtain ⟨leftEndpoint, rightEndpoint, unit, decomposition,
                        leftComputed, rightComputed, unitComputed⟩ :=
                        localizedRule3TerminalGuardedNode_old_spatial_components input
                          target occurrence view
                          (fun cursors =>
                            input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                              target view budget cursors)
                          topology topologyComputed spatialResult spatial
                      have doubleBond :
                          input.moleculeGraph.bond topology.left topology.right = 2 :=
                        (input.localizedRule3PhysicalEndpointCursorFrameExec?_sound
                          occurrence topology topologyComputed).2.2.2.1
                      -- Split on which endpoint the guard certified.
                      cases witness with
                      | left certificate =>
                          simp only [LocalizedRule3TerminalGuardWitness.side]
                          have leftField : spatialResult.leftEndpoint = leftEndpoint := by
                            simpa using congrArg
                              (fun r : input.LocalizedRule3ShortCircuitSpatialResult
                                carrierFuel => r.leftEndpoint) decomposition
                          have leftCertified : spatialResult.leftEndpoint =
                              certificate.shortCircuitEndpoint :=
                            leftField.trans
                              (endpointResult_eq_shortCircuitEndpoint_production certificate
                                budget leftEndpoint leftComputed)
                          have geometryNonstereogenic :
                              spatialResult.unit.core.geometry =
                                OfficialRule3Geometry.nonstereogenic :=
                            localizedRule3TerminalGuardedNode_spatial_geometry_left input
                              target occurrence view
                              (fun cursors =>
                                input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                                  target view budget cursors)
                              topology topologyComputed certificate spatialResult spatial
                              leftCertified doubleBond
                          rw [decomposition] at oldObservation
                          rw [decomposition] at geometryNonstereogenic
                          have geometry' : unit.core.geometry =
                              OfficialRule3Geometry.nonstereogenic := by
                            simpa using geometryNonstereogenic
                          let identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel :=
                            { topology := topology, side := LocalizedRule3TerminalGuardSide.left }
                          have identityEq : identity =
                              { topology := topology
                                side := LocalizedRule3TerminalGuardSide.left } :=
                            rfl
                          refine ⟨if excluded.contains identity.physicalUnitId then
                              none
                            else
                              some (LocalizedRule3TerminalGuardedNodeResult.direct identity),
                            ?_, ?_⟩
                          · simp only [guardComputed, identityEq]
                          have conditionEq : excluded.contains identity.physicalUnitId =
                              excluded.contains
                                (input.localizedRule3ShortCircuitSpatialObservation
                                  { topology := topology
                                    leftEndpoint := leftEndpoint
                                    rightEndpoint := rightEndpoint
                                    unit := unit }).physicalUnitId := by
                            rw [identityEq]
                            simp [LocalizedRule3TerminalGuardedIdentity.physicalUnitId,
                              localizedRule3ShortCircuitSpatialObservation,
                              LocalizedRule3SpatialNodeResult.physicalUnitId]
                          rw [oldObservation]
                          by_cases excludedCase : excluded.contains identity.physicalUnitId
                          · have oldCase : excluded.contains
                                (input.localizedRule3ShortCircuitSpatialObservation
                                  { topology := topology
                                    leftEndpoint := leftEndpoint
                                    rightEndpoint := rightEndpoint
                                    unit := unit }).physicalUnitId := by
                              rw [← conditionEq]
                              exact excludedCase
                            rw [if_pos excludedCase, if_pos oldCase]
                            rfl
                          · have oldCase : ¬ excluded.contains
                                (input.localizedRule3ShortCircuitSpatialObservation
                                  { topology := topology
                                    leftEndpoint := leftEndpoint
                                    rightEndpoint := rightEndpoint
                                    unit := unit }).physicalUnitId := by
                              intro h
                              exact excludedCase (by rw [conditionEq]; exact h)
                            rw [if_neg excludedCase, if_neg oldCase]
                            simp [identityEq,
                              LocalizedRule3TerminalGuardedIdentity.observable,
                              LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable,
                              localizedRule3ShortCircuitSpatialObservation, geometry']
                      | right certificate =>
                          simp only [LocalizedRule3TerminalGuardWitness.side]
                          have rightField : spatialResult.rightEndpoint = rightEndpoint := by
                            simpa using congrArg
                              (fun r : input.LocalizedRule3ShortCircuitSpatialResult
                                carrierFuel => r.rightEndpoint) decomposition
                          have rightCertified : spatialResult.rightEndpoint =
                              certificate.shortCircuitEndpoint :=
                            rightField.trans
                              (endpointResult_eq_shortCircuitEndpoint_production certificate
                                budget rightEndpoint rightComputed)
                          have geometryNonstereogenic :
                              spatialResult.unit.core.geometry =
                                OfficialRule3Geometry.nonstereogenic :=
                            localizedRule3TerminalGuardedNode_spatial_geometry_right input
                              target occurrence view
                              (fun cursors =>
                                input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                                  target view budget cursors)
                              topology topologyComputed certificate spatialResult spatial
                              rightCertified doubleBond
                          rw [decomposition] at oldObservation
                          rw [decomposition] at geometryNonstereogenic
                          have geometry' : unit.core.geometry =
                              OfficialRule3Geometry.nonstereogenic := by
                            simpa using geometryNonstereogenic
                          let identity : LocalizedRule3TerminalGuardedIdentity input carrierFuel :=
                            { topology := topology, side := LocalizedRule3TerminalGuardSide.right }
                          have identityEq : identity =
                              { topology := topology
                                side := LocalizedRule3TerminalGuardSide.right } :=
                            rfl
                          refine ⟨if excluded.contains identity.physicalUnitId then
                              none
                            else
                              some (LocalizedRule3TerminalGuardedNodeResult.direct identity),
                            ?_, ?_⟩
                          · simp only [guardComputed, identityEq]
                          have conditionEq : excluded.contains identity.physicalUnitId =
                              excluded.contains
                                (input.localizedRule3ShortCircuitSpatialObservation
                                  { topology := topology
                                    leftEndpoint := leftEndpoint
                                    rightEndpoint := rightEndpoint
                                    unit := unit }).physicalUnitId := by
                            rw [identityEq]
                            simp [LocalizedRule3TerminalGuardedIdentity.physicalUnitId,
                              localizedRule3ShortCircuitSpatialObservation,
                              LocalizedRule3SpatialNodeResult.physicalUnitId]
                          rw [oldObservation]
                          by_cases excludedCase : excluded.contains identity.physicalUnitId
                          · have oldCase : excluded.contains
                                (input.localizedRule3ShortCircuitSpatialObservation
                                  { topology := topology
                                    leftEndpoint := leftEndpoint
                                    rightEndpoint := rightEndpoint
                                    unit := unit }).physicalUnitId := by
                              rw [← conditionEq]
                              exact excludedCase
                            rw [if_pos excludedCase, if_pos oldCase]
                            rfl
                          · have oldCase : ¬ excluded.contains
                                (input.localizedRule3ShortCircuitSpatialObservation
                                  { topology := topology
                                    leftEndpoint := leftEndpoint
                                    rightEndpoint := rightEndpoint
                                    unit := unit }).physicalUnitId := by
                              intro h
                              exact excludedCase (by rw [conditionEq]; exact h)
                            rw [if_neg excludedCase, if_neg oldCase]
                            simp [identityEq,
                              LocalizedRule3TerminalGuardedIdentity.observable,
                              LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable,
                              localizedRule3ShortCircuitSpatialObservation, geometry']

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalGuardedRule3Node
