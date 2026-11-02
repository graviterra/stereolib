import TetraStereo.OneCenter.LocalizedRule3PreflightDemand

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Mandatory Rule-3 callback demands

`LocalizedRule3EndpointCallbackDemand` and `LocalizedRule3PreflightDemand` prove *callback
locality*: agreement on the listed requests suffices to preserve the executable result.  This
module proves the strictly stronger operational statement needed for a mandatory-cycle argument:
the listed requests are **mandatory for success**.  If any listed request receives `none` from the
Rule-3 frame callback, the corresponding executable compiler returns `none` (outer `none` for the
node evaluator), independently of every other callback answer, view, target and exclusion list.

The development follows the actual evaluation order.

* `buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_eq_none_of_callback_none` is the eager
  full-endpoint fact: once both canonical reference cursors are known, the callback
  `[firstCursor, secondCursor]` is called before any key work, so a missing answer annihilates the
  compilation.
* `rule3EndpointCallbackRequests_eq_none_of_mem_callback_none` and
  `rule3ShortEndpointCallbackRequests_eq_none_of_mem_callback_none` are the two endpoint demand
  graphs.  The short graph retains its request exactly when the atomic root comparison is `eq` and
  the complete constitutional comparison is a tie or a refusal; in both cases the executable
  selector defers to the full compiler, which demands the callback.
* `rule3ShortSpatialCallbackRequests_eq_none_of_mem_callback_none` and
  `rule3ShortOddCallbackRequests_eq_none_of_mem_callback_none` lift the endpoint facts to the
  ordinary and odd-cumulene spatial compilers.  Both endpoints bind before any geometry is
  inspected, so a missing request on either endpoint forces the whole spatial unit to `none`.
* The original ordinary, odd and ring request graphs are treated the same way
  (`rule3OrdinaryCallbackRequests_eq_none_of_mem_callback_none`,
  `rule3OddCallbackRequests_eq_none_of_mem_callback_none`,
  `rule3RingCallbackRequests_eq_none_of_mem_callback_none`), and
  `rule3OriginalNodeCallbackRequests_eq_none_of_mem_callback_none` propagates mandatory demand
  through every branch of the original descriptor-bearing node evaluator.
* `rule3PreflightExtendedNodeCallbackRequests_eq_none_of_mem_callback_none` propagates mandatory
  demand through the actual extended node evaluator using the preflight-pruned request graph of
  `LocalizedRule3PreflightDemand`, covering both the odd and ordinary routes and the fallback to
  the original node demands.
* `rule3PreflightExtendedNodeCallbackRequests_isSome_of_success` and
  `rule3PreflightExtendedNodeCallbackRequests_all_isSome_of_success` are the success forms: a
  successful node computation (`= some observation`, where `observation` is itself an `Option`)
  forces every listed request to be answered with `some frame`.

Exclusions are applied only *after* the spatial computation succeeds, so they cannot turn a
callback failure into the successful outer result `some none`; a missing callback request always
produces the outer `none`.  No totality of the callback and no successful result are assumed:
every statement is either conditional on a successful computation or concludes a refusal.
-/

/-! ## The eager full endpoint compiler -/

/-- The executable parameterized endpoint compiler demands its Rule-3 frame callback at the two
canonical reference cursors as soon as both cursor lookups succeed.  If that request has no
answer, the compilation is `none`; the candidate check, the frame keys and the Rule-4a--5
sub-computations are never reached. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_eq_none_of_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (missing : callback [firstCursor, secondCursor] = none) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view callback endpoint partner endpointCursor = none := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
  rw [candidates]
  dsimp only
  simp only [bind, Option.bind_some, firstComputed, secondComputed]
  simp [missing]

/-- Every request listed by the eager full endpoint demand graph is mandatory for the executable
full endpoint compiler. -/
theorem rule3EndpointCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3EndpointCallbackRequests endpoint partner endpointCursor)
    (missing : callback request = none) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view callback endpoint partner endpointCursor = none := by
  unfold rule3EndpointCallbackRequests at present
  cases candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp [candidates] at present
  | cons first rest =>
    cases rest with
    | nil => simp [candidates] at present
    | cons second rest =>
      cases rest with
      | cons third rest' => simp [candidates] at present
      | nil =>
        simp only [candidates] at present
        cases firstComputed : input.localizedRule3ReferenceCursorExec?
            endpointCursor first with
        | none => simp [firstComputed] at present
        | some firstCursor =>
          cases secondComputed : input.localizedRule3ReferenceCursorExec?
              endpointCursor second with
          | none => simp [firstComputed, secondComputed] at present
          | some secondCursor =>
            have requested : request = [firstCursor, secondCursor] := by
              simpa [firstComputed, secondComputed] using present
            exact input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_eq_none_of_callback_none
              target view callback endpoint partner endpointCursor first second firstCursor
              secondCursor candidates firstComputed secondComputed (requested ▸ missing)

/-! ## The short-circuit endpoint selector -/

/-- Every request listed by the short-circuit endpoint demand graph is mandatory for the
executable short-circuit endpoint selector.  A listed request only occurs when the atomic root
comparison ties and the complete constitutional comparison ties or is refused, and precisely then
the selector defers to the full compiler that calls the callback at that request. -/
theorem rule3ShortEndpointCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor)
    (missing : callback request = none) :
    input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view callback endpoint partner endpointCursor = none := by
  unfold rule3ShortEndpointCallbackRequests at present
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  cases candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp [candidates] at present
  | cons first rest =>
    cases rest with
    | nil => simp [candidates] at present
    | cons second rest =>
      cases rest with
      | cons third rest' => simp [candidates] at present
      | nil =>
        simp only [candidates] at present ⊢
        cases firstComputed : input.localizedRule3ReferenceCursorExec?
            endpointCursor first with
        | none => simp [firstComputed] at present ⊢
        | some firstCursor =>
          cases secondComputed : input.localizedRule3ReferenceCursorExec?
              endpointCursor second with
          | none => simp [firstComputed, secondComputed] at present ⊢
          | some secondCursor =>
            simp [firstComputed, secondComputed] at present ⊢
            cases root : input.compareLocalizedRerootCursorConstitutionalRoot
                firstCursor secondCursor with
            | gt => simp [root] at present ⊢
            | lt => simp [root] at present ⊢
            | eq =>
              cases constitutional : input.compareLocalizedConstitutionalCursors?
                  firstCursor secondCursor with
              | none =>
                have requested : request = [firstCursor, secondCursor] := by
                  simpa [root, constitutional] using present
                have fullNone :=
                  input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_eq_none_of_callback_none
                    target view callback endpoint partner endpointCursor first second
                    firstCursor secondCursor candidates firstComputed secondComputed
                    (requested ▸ missing)
                simp [fullNone]
              | some order =>
                cases order with
                | gt => simp [root, constitutional] at present ⊢
                | lt => simp [root, constitutional] at present ⊢
                | eq =>
                  have requested : request = [firstCursor, secondCursor] := by
                    simpa [root, constitutional] using present
                  have fullNone :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_eq_none_of_callback_none
                      target view callback endpoint partner endpointCursor first second
                      firstCursor secondCursor candidates firstComputed secondComputed
                      (requested ▸ missing)
                  simp [fullNone]

/-! ## The ordinary and odd-cumulene short-circuit spatial compilers -/

/-- Every request listed by the ordinary short-circuit spatial demand graph is mandatory for the
executable ordinary spatial compiler.  Both endpoint results bind before the priority-keyed
geometry, so a missing request on either endpoint forces the whole unit to `none`. -/
theorem rule3ShortSpatialCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3ShortSpatialCallbackRequests occurrence)
    (missing : callback request = none) :
    input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view callback = none := by
  unfold rule3ShortSpatialCallbackRequests at present
  unfold localizedRule3ShortCircuitSpatialUnitWithExec?
  cases found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp [found] at present
  | some topology =>
    simp only [found] at present ⊢
    rw [List.mem_append] at present
    rcases present with leftPresent | rightPresent
    · have leftNone :=
        input.rule3ShortEndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.left topology.right topology.leftCursor request
          leftPresent missing
      simp [leftNone]
    · have rightNone :=
        input.rule3ShortEndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.right topology.left topology.rightCursor request
          rightPresent missing
      cases leftComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
          target view callback topology.left topology.right topology.leftCursor with
      | none => simp [leftComputed]
      | some leftEndpoint => simp [leftComputed, rightNone]

/-- Every request listed by the odd-cumulene short-circuit spatial demand graph is mandatory for
the executable odd spatial compiler.  The same bind-before-geometry argument applies, with the
initial left endpoint and the right partner endpoint of the cumulated-chain topology. -/
theorem rule3ShortOddCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3ShortOddCallbackRequests occurrence)
    (missing : callback request = none) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view callback = none := by
  unfold rule3ShortOddCallbackRequests at present
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
  cases found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [found] at present
  | some topology =>
    simp only [found] at present ⊢
    rw [List.mem_append] at present
    rcases present with leftPresent | rightPresent
    · have leftNone :=
        input.rule3ShortEndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.initial.left topology.initial.right
          topology.initial.leftCursor request leftPresent missing
      simp [leftNone]
    · have rightNone :=
        input.rule3ShortEndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.right topology.rightPartner topology.rightCursor
          request rightPresent missing
      cases leftComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
          target view callback topology.initial.left topology.initial.right
          topology.initial.leftCursor with
      | none => simp [leftComputed]
      | some leftEndpoint => simp [leftComputed, rightNone]

/-! ## The original (full-frame) route demands

The extended node evaluator falls back to the original descriptor-bearing node evaluator when
neither an odd nor an ordinary short-circuit route certificate applies.  The corresponding demand
graph is `rule3OriginalNodeCallbackRequests`, built from the eager `rule3EndpointCallbackRequests`
along the actual topology route.  The following lemmas establish mandatory propagation for every
route used by that fallback.
-/

/-- Every request listed by the original ordinary route demand is mandatory for the executable
eager ordinary spatial compiler. -/
theorem rule3OrdinaryCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3OrdinaryCallbackRequests occurrence)
    (missing : callback request = none) :
    input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
      target occurrence view callback = none := by
  unfold rule3OrdinaryCallbackRequests at present
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
  cases found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp [found] at present
  | some topology =>
    simp only [found] at present ⊢
    rw [List.mem_append] at present
    rcases present with leftPresent | rightPresent
    · have leftNone :=
        input.rule3EndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.left topology.right topology.leftCursor request
          leftPresent missing
      simp [leftNone]
    · have rightNone :=
        input.rule3EndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.right topology.left topology.rightCursor request
          rightPresent missing
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
          target view callback topology.left topology.right topology.leftCursor with
      | none => simp [leftComputed]
      | some leftCompilation => simp [leftComputed, rightNone]

/-- Every request listed by the original odd-cumulene route demand is mandatory for the
executable eager odd spatial compiler. -/
theorem rule3OddCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3OddCallbackRequests occurrence)
    (missing : callback request = none) :
    input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
      target occurrence view callback = none := by
  unfold rule3OddCallbackRequests at present
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
  cases found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [found] at present
  | some topology =>
    simp only [found] at present ⊢
    rw [List.mem_append] at present
    rcases present with leftPresent | rightPresent
    · have leftNone :=
        input.rule3EndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.initial.left topology.initial.right
          topology.initial.leftCursor request leftPresent missing
      simp [leftNone]
    · have rightNone :=
        input.rule3EndpointCallbackRequests_eq_none_of_mem_callback_none
          target view callback topology.right topology.rightPartner topology.rightCursor
          request rightPresent missing
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
          target view callback topology.initial.left topology.initial.right
          topology.initial.leftCursor with
      | none => simp [leftComputed]
      | some leftCompilation => simp [leftComputed, rightNone]

/-- Every request listed by the original ring-closure route demand is mandatory for the
executable required-monocyclic-E/Z compiler.  The `permanentlyOmit` policy lists no requests and
returns `none` independently of the callback. -/
theorem rule3RingCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3RingCallbackRequests occurrence)
    (missing : callback request = none) :
    input.localizedRule3RequiredMonocyclicEZWithExec?
      target occurrence view callback = none := by
  unfold rule3RingCallbackRequests at present
  unfold localizedRule3RequiredMonocyclicEZWithExec?
  cases route : input.localizedRule3CyclicAuthorityRouteExec? occurrence with
  | none => simp [route] at present
  | some value =>
    cases value with
    | fullyCyclicCumulene _ _ _ => simp [route] at present
    | ordinaryMonocyclicPolicyGap _ _ _ _ => simp [route] at present
    | ordinaryNonmonocyclic _ _ => simp [route] at present
    | ordinaryMonocyclicPolicy initial closure policy =>
      simp
      cases policyEq : policy.policy with
      | permanentlyOmit => simp [route, policyEq] at present ⊢
      | requireEZ =>
        simp only [route, policyEq] at present
        rw [List.mem_append] at present
        rcases present with leftPresent | rightPresent
        · have leftNone :=
            input.rule3EndpointCallbackRequests_eq_none_of_mem_callback_none
              target view callback initial.left initial.right initial.leftCursor request
              leftPresent missing
          simp [leftNone]
        · have rightNone :=
            input.rule3EndpointCallbackRequests_eq_none_of_mem_callback_none
              target view callback initial.right initial.left initial.rightCursor request
              rightPresent missing
          cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
              target view callback initial.left initial.right initial.leftCursor with
          | none => simp
          | some leftCompilation => simp [rightNone]

/-- Every request listed by the original node demand graph is mandatory for the executable
original descriptor-bearing node evaluator, on every topology branch.  A missing request yields
the outer `none`. Internal, even-cumulene, edge-free and omission branches list no requests.
An excluded observation can retain nonempty requests: exclusion occurs after successful spatial
computation and cannot turn callback failure into `some none`. -/
theorem rule3OriginalNodeCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3OriginalNodeCallbackRequests occurrence)
    (missing : callback request = none) :
    input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view callback excluded = none := by
  unfold rule3OriginalNodeCallbackRequests at present
  unfold localizedDescriptorBearingRule3NodeWithExec?
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp only [if_pos edge, dif_pos edge] at present ⊢
    cases entry : input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | none => simp [entry] at present ⊢
    | some value =>
      cases value with
      | internal => simp [entry] at present ⊢
      | branched =>
        simp only [entry] at present ⊢
        have ordinaryNone :=
          input.rule3OrdinaryCallbackRequests_eq_none_of_mem_callback_none
            target occurrence view callback request present missing
        simp [ordinaryNone]
      | ringClosure =>
        simp only [entry] at present ⊢
        have ringNone :=
          input.rule3RingCallbackRequests_eq_none_of_mem_callback_none
            target occurrence view callback request present missing
        simp only [ringNone] at ⊢
        cases route : input.localizedRule3CyclicAuthorityRouteExec? occurrence with
        | none => simp
        | some value =>
          cases value with
          | fullyCyclicCumulene _ _ _ => simp
          | ordinaryMonocyclicPolicyGap _ _ _ _ => simp
          | ordinaryNonmonocyclic _ _ => simp
          | ordinaryMonocyclicPolicy initial closure policy =>
            cases policyEq : policy.policy with
            | permanentlyOmit =>
              simp [rule3RingCallbackRequests, route, policyEq] at present
            | requireEZ => simp [policyEq]
      | terminalStart =>
        simp only [entry] at present ⊢
        cases axis : input.localizedRule3CumulatedEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
        | none => simp [axis] at present ⊢
        | some topology =>
          simp only [axis] at present ⊢
          by_cases ordinary : topology.doubleBondCount = 1
          · simp only [if_pos ordinary, dif_pos ordinary] at present ⊢
            have ordinaryNone :=
              input.rule3OrdinaryCallbackRequests_eq_none_of_mem_callback_none
                target occurrence view callback request present missing
            simp [ordinaryNone]
          · simp only [if_neg ordinary, dif_neg ordinary] at present ⊢
            by_cases odd : Odd topology.doubleBondCount
            · simp only [if_pos odd, dif_pos odd] at present ⊢
              have oddNone :=
                input.rule3OddCallbackRequests_eq_none_of_mem_callback_none
                  target occurrence view callback request present missing
              simp [oddNone]
            · simp only [if_neg odd, dif_neg odd] at present ⊢
              simp at present
  · rw [if_neg edge] at present
    exact absurd present (by simp)

/-! ## The extended node evaluator under the preflight-pruned demand -/

/-- If any request listed by the preflight-pruned extended node demand graph receives `none` from
the Rule-3 frame callback, the executable extended node evaluator returns the outer `none`.
Exclusions are applied only after the spatial computation has succeeded, so they cannot rescue the
missing callback. -/
theorem rule3PreflightExtendedNodeCallbackRequests_eq_none_of_mem_callback_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3PreflightExtendedNodeCallbackRequests occurrence)
    (missing : callback request = none) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = none := by
  unfold rule3PreflightExtendedNodeCallbackRequests at present
  unfold localizedRule3ExtendedShortCircuitNodeWithExec?
  cases odd : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
    simp only [odd] at present ⊢
    cases ready : input.oddPairReady occurrence with
    | false =>
      simp [rule3PreflightShortOddCallbackRequests, ready] at present
    | true =>
      have inShort : request ∈ input.rule3ShortOddCallbackRequests occurrence := by
        simpa only [rule3PreflightShortOddCallbackRequests, ready, if_true] using present
      have oddNone :=
        input.rule3ShortOddCallbackRequests_eq_none_of_mem_callback_none
          target occurrence view callback request inShort missing
      simp [oddNone]
  | none =>
    simp only [odd] at present ⊢
    cases ordinary : input.localizedRule3OrdinaryRouteCertificate? occurrence with
    | some certificate =>
      simp only [ordinary] at present ⊢
      cases ready : input.ordinaryPairReady occurrence with
      | false =>
        simp [rule3PreflightShortSpatialCallbackRequests, ready] at present
      | true =>
        have inShort : request ∈ input.rule3ShortSpatialCallbackRequests occurrence := by
          simpa only [rule3PreflightShortSpatialCallbackRequests, ready, if_true] using present
        have spatialNone :=
          input.rule3ShortSpatialCallbackRequests_eq_none_of_mem_callback_none
            target occurrence view callback request inShort missing
        simp [localizedRule3ShortCircuitNodeWithExec?, ordinary, spatialNone]
    | none =>
      simp only [ordinary] at present ⊢
      have inOriginal : request ∈ input.rule3OriginalNodeCallbackRequests occurrence := by
        simpa only [rule3NodeCallbackRequests, ordinary] using present
      have nodeNone :=
        input.rule3OriginalNodeCallbackRequests_eq_none_of_mem_callback_none
          target occurrence view callback excluded request inOriginal missing
      simp [localizedRule3ShortCircuitNodeWithExec?, ordinary, nodeNone]

/-- Success form of the mandatory demand: a successful extended node computation forces every
listed preflight-pruned request to be answered by the Rule-3 frame callback.  The result is
`some observation` with `observation : Option ...`; the distinction between the outer `none` and
the successful `some none` is exactly what makes this implication meaningful. -/
theorem rule3PreflightExtendedNodeCallbackRequests_isSome_of_success
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = some observation)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3PreflightExtendedNodeCallbackRequests occurrence) :
    (callback request).isSome := by
  cases answered : callback request with
  | none =>
    exfalso
    have refused :=
      input.rule3PreflightExtendedNodeCallbackRequests_eq_none_of_mem_callback_none
        target occurrence view callback excluded request present answered
    rw [refused] at computed
    cases computed
  | some frame => rfl

/-- Bundled success form: on a successful extended node computation, *every* request listed by
the preflight-pruned demand graph is answered by the Rule-3 frame callback. -/
theorem rule3PreflightExtendedNodeCallbackRequests_all_isSome_of_success
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = some observation) :
    ∀ request ∈ input.rule3PreflightExtendedNodeCallbackRequests occurrence,
      (callback request).isSome := by
  intro request present
  exact input.rule3PreflightExtendedNodeCallbackRequests_isSome_of_success
    target occurrence view callback excluded observation computed request present

/-- The successful but empty spatial observation `some none` does not weaken the demand: even
when the evaluator reports success with no retained observation, every listed callback request
must have been answered. -/
theorem rule3PreflightExtendedNodeCallbackRequests_isSome_of_some_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = some none)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (present : request ∈ input.rule3PreflightExtendedNodeCallbackRequests occurrence) :
    (callback request).isSome :=
  input.rule3PreflightExtendedNodeCallbackRequests_isSome_of_success
    target occurrence view callback excluded none computed request present

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
