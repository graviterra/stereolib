import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedRule3DemandRestrictedEndpoint
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Parametric label seam for the existing extended short-circuit Rule-3 recursion

`LocalizedRerootExtendedShortCircuitRule3Key` deploys the actual extended recursive key, the
two-pass physical-unit frame and the extended node reader.  The key at successor fuel calls the
*predecessor* frame; the frame at successor fuel performs both the raw and the rebuilt key passes at
the predecessor index with the actual coupled topology resolution and the excluded physical units
computed from that topology; and the extended node delegates to the ordinary short-circuit node or,
on a checked odd route, to the odd spatial wrapper.  All of those operational ingredients are
retained verbatim here.

The present module exposes exactly one new parameter: the **direct Rules-4/5 label reader** of the
underlying compound key builds.  Everything else is unchanged:

* the reference-cursor selection and the callback-first `Option` order of both endpoint selectors;
* the child enumeration, the constitutional/observation/priority assembly and the key sorting;
* the two-pass frame, the coupled topology resolution and the excluded physical-unit policy;
* the odd and ordinary spatial geometry, and the original/eager node fallback;
* every fail-closed `Option` refusal.

The original descriptor target `target` and the physical occurrence `occurrence` stay separate
parameters throughout.  Nothing here identifies them, relabels the original evaluator, replaces the
eager fallback by `none`, or claims reader locality.

## Main results

* `localizedRule3ShortCircuitOddSpatialUnitWithRead?` — the parametric odd spatial wrapper.  Its
  **unconditional** specialization
  `..._eq_...WithExec?_of_localizedDependencyLabel` reproduces the shipped odd wrapper exactly, and
  `..._congr_of_actualRequests` is a full `Option` congruence from callback agreement and reader
  agreement posed **only on the retained requests** `rule3ShortOddCallbackRequests`.  The request
  list is input-derived and callback-independent; the strict endpoint branches still suppress their
  requests entirely.
* `localizedRule3ShortCircuitNodeWithRead?` — the ordinary node seam.  Its non-ordinary branch is
  the actual original/eager evaluator `localizedDescriptorBearingRule3NodeWithExec?` (retained, not
  replaced), and its ordinary branch is the accepted
  `localizedRule3ShortCircuitSpatialUnitWithRead?` from `LocalizedRule3DemandRestrictedEndpoint`.
* `localizedRule3ExtendedShortCircuitNodeWithRead?` — the extended node seam, retaining the odd
  route check, the odd exclusion policy and the delegation to the ordinary node otherwise.
* `buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?`,
  `buildLocalizedExtendedShortCircuitRule3FrameWithRead?` and
  `localizedExtendedShortCircuitRule3NodeWithRead?` — the mutual key/frame/node recursion with only
  the reader parameterized.  Their exact recovery at the shipped restricted dependency reader is
  proved by induction on fuel in `recursive_compilers_withRead_eq`, generalizing the exclusion list
  at every index, and is exported as three unconditional specializations.

## What is not claimed

The callback-agreement hypotheses of the node wrapper lemmas are explicit and are **not** proved
here; discharging them for the actual mutual frame recursion is later work, as is any whole-state
reader locality statement.  No theorem below asserts an unconditional callback equality as a final
result.  The reader premise of the node congruence is a sufficient condition on the actual
`rule3ExtendedNodeCallbackRequests`; the original/eager branch is handled by the existing
`rule3OriginalNode_callback_local` and needs callback agreement only, not a reader.

## Kernel authority

Every exported declaration is guarded by `assert_kernel_only` at the end of the file.
-/

namespace TetraStereo.OneCenter

universe u

/-- The bind of a `some` value in the `Option` monad is definitionally the applied continuation.
This is the same private helper used by the accepted parametric endpoint modules. -/
private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

namespace CertifiedLocalizedCIPInput

/-! ## The parametric odd spatial wrapper -/

/-- The shipped odd spatial wrapper with only the direct Rules-4/5 label reader parameterized.
The odd cumulene topology lookup, both endpoint selectors, the descriptor-bearing geometry unit and
the `Option` order are the executable ones verbatim; the reader is demanded only inside the two
endpoint selectors, and therefore only on their completely tied branches. -/
noncomputable def localizedRule3ShortCircuitOddSpatialUnitWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3OddCumuleneEndpointCursorFrameExec?
    (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence
  let leftEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityWithRead?
    target view read rule3FrameOf topology.initial.left topology.initial.right
    topology.initial.leftCursor
  let rightEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityWithRead?
    target view read rule3FrameOf topology.right topology.rightPartner topology.rightCursor
  let unit ← input.localizedRule3ExtendedSpatialUnitOfPriorities?
    topology.initial.left topology.right leftEndpoint.priority rightEndpoint.priority
  some { topology, leftEndpoint, rightEndpoint, unit }

/-- **Unconditional specialization of the odd spatial wrapper.**  With the reader specialized to
the shipped restricted dependency reader the parametric odd wrapper is exactly the executable odd
wrapper, at every target, occurrence, view and Rule-3 callback, including every fail-closed `none`.
Only the two endpoint selectors are rewritten; the topology recovery and the geometry unit are
shared. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_localizedRule3ShortCircuitOddSpatialUnitWithExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithRead? target occurrence view
        (fun cursor => input.localizedDependencyLabel target view cursor) rule3FrameOf =
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view rule3FrameOf := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithRead?
    localizedRule3ShortCircuitOddSpatialUnitWithExec?
  simp only [
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_localizedDependencyLabel]

/-- **Request-local congruence of the odd spatial wrapper.**  Two parametric odd wrappers are
exactly equal, with full `Option` agreement, as soon as the two Rule-3 callbacks agree and the two
readers agree on the executable-reachable support of every cursor occurring in the retained odd
requests `rule3ShortOddCallbackRequests`.  The request list is computed from the actual odd
cumulene topology and the two endpoint references only; the strict atomic-root and strict
complete-constitutional branches contribute no request and therefore no read obligation. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithRead?_congr_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3ShortOddCallbackRequests occurrence) before after)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read1 read2
      (input.rule3ShortOddCallbackRequests occurrence)) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
        target occurrence view read1 before =
      input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
        target occurrence view read2 after := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithRead?
  cases found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp
  | some topology =>
      have leftCallback : input.Rule3CallbackAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.initial.left
            topology.initial.right topology.initial.leftCursor) before after := by
        intro cursors member
        exact callbackAgree cursors
          (by simp [rule3ShortOddCallbackRequests, found, member])
      have leftReaders : input.LocalizedRerootReadersAgreeOnRequests read1 read2
          (input.rule3ShortEndpointCallbackRequests topology.initial.left
            topology.initial.right topology.initial.leftCursor) := by
        intro cursors member cursor cursorMember
        exact readersAgree cursors
          (by simp [rule3ShortOddCallbackRequests, found, member]) cursor cursorMember
      have rightCallback : input.Rule3CallbackAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.right
            topology.rightPartner topology.rightCursor) before after := by
        intro cursors member
        exact callbackAgree cursors
          (by simp [rule3ShortOddCallbackRequests, found, member])
      have rightReaders : input.LocalizedRerootReadersAgreeOnRequests read1 read2
          (input.rule3ShortEndpointCallbackRequests topology.right
            topology.rightPartner topology.rightCursor) := by
        intro cursors member cursor cursorMember
        exact readersAgree cursors
          (by simp [rule3ShortOddCallbackRequests, found, member]) cursor cursorMember
      simp only [option_some_bind_apply,
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
          target view read1 read2 before after topology.initial.left topology.initial.right
          topology.initial.leftCursor leftCallback leftReaders,
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
          target view read1 read2 before after topology.right topology.rightPartner
          topology.rightCursor rightCallback rightReaders]

/-- A reader that agrees with the shipped restricted dependency reader only on the actual retained
odd requests produces exactly the executable odd wrapper, in every branch. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_localizedRule3ShortCircuitOddSpatialUnitWithExec?_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (input.rule3ShortOddCallbackRequests occurrence)) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
        target occurrence view read rule3FrameOf =
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view rule3FrameOf := by
  rw [input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_congr_of_actualRequests
    target occurrence view read (fun cursor => input.localizedDependencyLabel target view cursor)
    rule3FrameOf rule3FrameOf (by intro cursors _member; rfl) readersAgree]
  exact
    input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_localizedRule3ShortCircuitOddSpatialUnitWithExec?_of_localizedDependencyLabel
      target occurrence view rule3FrameOf

/-! ## The ordinary node seam and its original/eager fallback

The ordinary short-circuit node is the `none`-route branch of the executable node.  Its fallback is
the actual original evaluator `localizedDescriptorBearingRule3NodeWithExec?`, retained here without
weakening; only the ordinary route branch gains a reader. -/

/-- The shipped ordinary short-circuit node with only the direct Rules-4/5 label reader
parameterized.  On an ordinary-route certificate it runs the accepted parametric ordinary spatial
wrapper; otherwise it runs the actual original/eager descriptor-bearing evaluator on the same
callback and exclusion list.  No branch is replaced by `none`. -/
noncomputable def localizedRule3ShortCircuitNodeWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  match input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none =>
      input.localizedDescriptorBearingRule3NodeWithExec?
        target occurrence view callback excluded
  | some _ => do
      let result ← input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence view read callback
      let observation := input.localizedRule3ShortCircuitSpatialObservation result
      pure (if excluded.contains observation.physicalUnitId then none else some observation)

/-- **Unconditional specialization of the ordinary node seam.**  With the restricted dependency
reader the parametric ordinary node is exactly the executable ordinary node, for every callback and
exclusion list.  The original/eager fallback is shared syntactically and is not touched. -/
theorem localizedRule3ShortCircuitNodeWithRead?_eq_localizedRule3ShortCircuitNodeWithExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ShortCircuitNodeWithRead? target occurrence view
        (fun cursor => input.localizedDependencyLabel target view cursor) callback excluded =
      input.localizedRule3ShortCircuitNodeWithExec?
        target occurrence view callback excluded := by
  unfold localizedRule3ShortCircuitNodeWithRead?
    localizedRule3ShortCircuitNodeWithExec?
  cases route : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none => rfl
  | some certificate =>
      simp only [route, option_some_bind_apply,
        input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_localizedDependencyLabel]

/-- **Ordinary node congruence from a generic callback-agreement hypothesis.**  Two parametric
ordinary nodes agree as soon as the callbacks agree on `rule3NodeCallbackRequests` and the readers
agree on the executable-reachable support of every cursor occurring there.  On the original/eager
branch no reader is demanded at all (`rule3OriginalNode_callback_local`); on the ordinary branch the
accepted request-local spatial congruence is applied.  The callback premise is deliberately a
hypothesis here; it is not asserted as a final result. -/
theorem localizedRule3ShortCircuitNodeWithRead?_congr_of_callbackAgree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3NodeCallbackRequests occurrence) before after)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read1 read2
      (input.rule3NodeCallbackRequests occurrence))
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ShortCircuitNodeWithRead?
        target occurrence view read1 before excluded =
      input.localizedRule3ShortCircuitNodeWithRead?
        target occurrence view read2 after excluded := by
  unfold localizedRule3ShortCircuitNodeWithRead?
  cases route : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none =>
      exact input.rule3OriginalNode_callback_local target occurrence view before after
        (by simpa only [rule3NodeCallbackRequests, route] using callbackAgree) excluded
  | some certificate =>
      rw [input.localizedRule3ShortCircuitSpatialUnitWithRead?_congr_of_actualRequests
        target occurrence view read1 read2 before after
        (by simpa only [rule3NodeCallbackRequests, route] using callbackAgree)
        (by simpa only [rule3NodeCallbackRequests, route] using readersAgree)]

/-! ## The extended node seam -/

/-- The shipped extended short-circuit node with only the direct Rules-4/5 label reader
parameterized.  The odd route certificate is inspected first, exactly as in the executable node; a
checked odd route runs the parametric odd spatial wrapper and applies the actual physical-unit
exclusion policy, while every other route delegates to the ordinary node seam, which retains the
original/eager fallback. -/
noncomputable def localizedRule3ExtendedShortCircuitNodeWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      input.localizedRule3ShortCircuitNodeWithRead?
        target occurrence view read callback excluded
  | some _ => do
      let result ← input.localizedRule3ShortCircuitOddSpatialUnitWithRead?
        target occurrence view read callback
      let observation := input.localizedRule3ShortCircuitOddSpatialObservation result
      pure (if excluded.contains observation.physicalUnitId then none else some observation)

/-- **Unconditional specialization of the extended node seam.**  With the restricted dependency
reader the parametric extended node is exactly the executable extended node, for every callback and
exclusion list, including the odd exclusion policy and the original/eager fallback. -/
theorem localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead? target occurrence view
        (fun cursor => input.localizedDependencyLabel target view cursor) callback excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view callback excluded := by
  unfold localizedRule3ExtendedShortCircuitNodeWithRead?
    localizedRule3ExtendedShortCircuitNodeWithExec?
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      simp only [routed,
        input.localizedRule3ShortCircuitNodeWithRead?_eq_localizedRule3ShortCircuitNodeWithExec?_of_localizedDependencyLabel]
  | some certificate =>
      simp only [routed, option_some_bind_apply,
        input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_localizedRule3ShortCircuitOddSpatialUnitWithExec?_of_localizedDependencyLabel]

/-- **Extended node congruence from a generic callback-agreement hypothesis.**  Two parametric
extended nodes agree as soon as the callbacks agree on the actual extended node requests
`rule3ExtendedNodeCallbackRequests` and the readers agree on their executable-reachable support.
On the odd branch this is the request-local odd spatial congruence; on every other route it is the
ordinary node congruence, whose original/eager branch consumes only the callback premise. -/
theorem localizedRule3ExtendedShortCircuitNodeWithRead?_congr_of_callbackAgree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read1 read2
      (input.rule3ExtendedNodeCallbackRequests occurrence))
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead?
        target occurrence view read1 before excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithRead?
        target occurrence view read2 after excluded := by
  unfold localizedRule3ExtendedShortCircuitNodeWithRead?
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      exact
        input.localizedRule3ShortCircuitNodeWithRead?_congr_of_callbackAgree
          target occurrence view read1 read2 before after
          (by simpa only [rule3ExtendedNodeCallbackRequests, routed] using callbackAgree)
          (by simpa only [rule3ExtendedNodeCallbackRequests, routed] using readersAgree)
          excluded
  | some certificate =>
      rw [input.localizedRule3ShortCircuitOddSpatialUnitWithRead?_congr_of_actualRequests
        target occurrence view read1 read2 before after
        (by
          intro cursors member
          exact callbackAgree cursors
            (by simp [rule3ExtendedNodeCallbackRequests, routed, member]))
        (by
          intro cursors member cursor cursorMember
          exact readersAgree cursors
            (by simp [rule3ExtendedNodeCallbackRequests, routed, member])
            cursor cursorMember)]

/-! ## The mutual key/frame/node recursion over an arbitrary reader

The three definitions below are the shipped extended recursive key, frame and node with only the
direct Rules-4/5 label reader added.  The key at successor fuel calls the predecessor frame; the
frame at successor fuel performs both key passes at the predecessor index with the actual coupled
topology resolution and the actual excluded physical-unit computation; the node at successor fuel
calls the extended node reader with the predecessor frame.  Child enumeration, sorting, assembly,
exclusions and every `Option` refusal are unchanged. -/

mutual

  /-- Descriptor-bearing extended cumulative key over an arbitrary direct label reader.  Every
  recursive call uses the predecessor index. -/
  noncomputable def buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target)
      (read : input.LocalizedRerootCursor carrierFuel →
        Option LocalizedAuxiliaryLabel) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        input.LocalizedRerootCursor carrierFuel →
          Option input.LocalizedRerootRecursiveRule3SpatialKey
    | 0, _excluded, cursor => do
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← input.localizedRule3StructuralNodeExec
          cursor.occurrence
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else none
    | fuel + 1, excluded, cursor => do
        let children ← input.executableLocalizedRerootChildren? cursor
        let observation ← input.localizedRule3ExtendedShortCircuitNodeWithRead?
          target cursor.occurrence view read
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read fuel)
          excluded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
              target view read fuel excluded)
          let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
          some
            { constitutional := OfficialRuleMajorKey.assemble
                (input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node false)
                (sorted.map fun child => child.constitutional)
              observations := input.localizedRule3SpatialRootObservations observation ++
                input.mergeLocalizedRerootRule3ObservationChildren sorted
              rule3 := input.localizedRule3SpatialRootPriorities observation ++
                input.mergeLocalizedRerootRule3PriorityChildren sorted }

  /-- Two-pass physical-unit frame over an arbitrary direct label reader.  Both key passes use the
  predecessor index; the exhaustive coupled topology resolver and the excluded physical-unit policy
  are the executable ones. -/
  noncomputable def buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target)
      (read : input.LocalizedRerootCursor carrierFuel →
        Option LocalizedAuxiliaryLabel) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame
    | 0, _cursors => none
    | fuel + 1, cursors => do
        let rawKeys ← cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read fuel excluded)
        some { rawKeys, coupled, excluded, keys }

  /-- Node reader over an arbitrary direct label reader.  At zero it is structural; a successor
  delegates only to the predecessor frame. -/
  noncomputable def localizedExtendedShortCircuitRule3NodeWithRead?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target)
      (read : input.LocalizedRerootCursor carrierFuel →
        Option LocalizedAuxiliaryLabel) :
      Nat → List input.LocalizedRule3PhysicalUnitId →
        Option (Option input.LocalizedRule3SpatialNodeResult)
    | 0, _excluded =>
        input.localizedRule3StructuralNodeExec occurrence
    | fuel + 1, excluded =>
        input.localizedRule3ExtendedShortCircuitNodeWithRead?
          target occurrence view read
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read fuel)
          excluded

end

/-- The shared fuel index recovers the key and the frame exactly at the shipped restricted
dependency reader, generalizing the exclusion list at every index.  The proof is an induction on
fuel: at successor index the callback argument is replaced by the induction hypothesis for the
frame, the extended node seam is specialized by its unconditional theorem, and the child and
rebuild key passes are replaced by the induction hypothesis for the key. -/
private theorem recursive_compilers_withRead_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    (∀ excluded cursor,
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target view
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel excluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel
        excluded cursor) ∧
    (∀ cursors,
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro excluded cursor
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?,
          buildLocalizedRerootExtendedShortCircuitRule3KeyExec?]
      · intro cursors
        rfl
  | succ fuel ih =>
      obtain ⟨ihKey, ihFrame⟩ := ih
      have keysEq : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target view
            (fun cursor => input.localizedDependencyLabel target view cursor) fuel =
          input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel :=
        funext fun excluded => funext (ihKey excluded)
      have framesEq : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view
            (fun cursor => input.localizedDependencyLabel target view cursor) fuel =
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel :=
        funext ihFrame
      refine ⟨?_, ?_⟩
      · intro excluded cursor
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?,
          buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          framesEq,
          input.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel,
          keysEq]
      · intro cursors
        simp only [buildLocalizedExtendedShortCircuitRule3FrameWithRead?,
          buildLocalizedExtendedShortCircuitRule3FrameExec?, keysEq]

/-- **Unconditional exact recovery of the recursive key.**  At the shipped restricted dependency
reader the parametric extended key is exactly the executable extended key, at every fuel, exclusion
list and cursor, with full `Option` agreement. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_eq_buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target view
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel excluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel
        excluded cursor :=
  (recursive_compilers_withRead_eq input target view fuel).1 excluded cursor

/-- **Unconditional exact recovery of the two-pass frame.**  At the shipped restricted dependency
reader the parametric extended frame is exactly the executable extended frame, at every fuel and
cursor list, including the empty frame at zero. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameWithRead?_eq_buildLocalizedExtendedShortCircuitRule3FrameExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors :=
  (recursive_compilers_withRead_eq input target view fuel).2 cursors

/-- **Unconditional exact recovery of the node.**  At the shipped restricted dependency reader the
parametric extended node is exactly the executable extended node, for every occurrence, fuel and
exclusion list; the zero index is the structural reader on both sides, and the successor index uses
the recovered predecessor frame. -/
theorem localizedExtendedShortCircuitRule3NodeWithRead?_eq_localizedExtendedShortCircuitRule3NodeExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedExtendedShortCircuitRule3NodeWithRead? target occurrence view
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel excluded =
      input.localizedExtendedShortCircuitRule3NodeExec? target occurrence view fuel excluded := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have framesEq :
          input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view
            (fun cursor => input.localizedDependencyLabel target view cursor) fuel =
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel :=
        funext
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_eq_buildLocalizedExtendedShortCircuitRule3FrameExec?_of_localizedDependencyLabel
            target view fuel)
      simp only [localizedExtendedShortCircuitRule3NodeWithRead?,
        localizedExtendedShortCircuitRule3NodeExec?, framesEq,
        input.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the parametric odd spatial wrapper with its unconditional
specialization, its request-local congruence on the actual odd requests and its executable
corollary; the ordinary node seam with its unconditional specialization and callback-agreement
congruence; the extended node seam with its unconditional specialization and callback-agreement
congruence; and the mutual key/frame/node recursion with the three unconditional exact-recovery
theorems.  The callback-agreement hypotheses of the two node lemmas are hypotheses, not results. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_localizedRule3ShortCircuitOddSpatialUnitWithExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithRead?_congr_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithRead?_eq_localizedRule3ShortCircuitOddSpatialUnitWithExec?_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitNodeWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitNodeWithRead?_eq_localizedRule3ShortCircuitNodeWithExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitNodeWithRead?_congr_of_callbackAgree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_congr_of_callbackAgree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_eq_buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_eq_buildLocalizedExtendedShortCircuitRule3FrameExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?_eq_localizedExtendedShortCircuitRule3NodeExec?_of_localizedDependencyLabel
