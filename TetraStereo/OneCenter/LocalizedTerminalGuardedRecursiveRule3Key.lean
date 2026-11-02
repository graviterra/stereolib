import TetraStereo.OneCenter.LocalizedTerminalGuardedRule3Node
import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedMutualObservableCompletion
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TerminalGuardedRule3Node

/-!
# Terminal-guarded recursive localized Rule-3 key and frame compiler

This module integrates the terminal nonstereogenic guard of
`CertifiedLocalizedCIPInput.TerminalGuardedRule3Node` into the *actual* two-pass recursive key/frame
compiler of `LocalizedRerootExtendedShortCircuitRule3Key`.  No existing module is modified.  The new
definitions are twins of the old mutually recursive builders:

* `buildLocalizedTerminalGuardedRecursiveRule3KeyExec?` is the guarded recursive key builder.  Its
  successor branch runs the guarded ordinary-node evaluator before consulting any frame callback.
  On an accepted guard the node evaluator returns a direct nonstereogenic identity and never calls
  the callback; every other branch is literally the old extended-node computation, tagged
  `ordinary`.
* `buildLocalizedTerminalGuardedExtendedRule3FrameExec?` is the guarded two-pass frame.  It still
  performs the mandatory raw-key pass, the actual coupled-topology resolution, the excluded
  physical-unit computation on the actual raw keys, and the rebuilt-key pass.

The node evaluator is always handed the *old predecessor frame callback*
`buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel`.  This is deliberate:

1. the guard is executed before that callback is ever consulted, so accepted guard branches demand
   no callback at all (the reduced demand is `[]` there);
2. on every fallback branch the node computation is literally the old computation, so no old
   success is lost;
3. the reviewed agreement theorem
   `localizedRule3TerminalGuardedNodeWithExec?_agrees_with_extended` applies with the *same*
   callback on both sides, avoiding any two-sided frame-completeness assumption.

A directly accepted guard does not carry the opposite raw reference or the old diagnostic payload.
The key assembly therefore adapts it to a synthetic `LocalizedRule3SpatialNodeResult` whose endpoints
are the actual physical topology endpoints and whose geometry is `nonstereogenic`
(`LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation`).  The resulting key agrees with the
old key at the comparison-visible observable projection (Rules 1a, 1b, 2 and the Rule-3 priority
stream) and at physical-unit incidence, which is exactly
`LocalizedRule3SpatialKeyTopologyEquivalent`.  No raw diagnostic-reference equality is claimed.

The main results are
`buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_refines_old` and
`buildLocalizedTerminalGuardedExtendedRule3FrameExec?_refines_old`: every successful old evaluation
is preserved, with a topology-equivalent guarded key and a frame satisfying the reusable
`LocalizedRule3ExtendedFrameTopologyEquivalent` invariant (pointwise topology equivalence of raw and
rebuilt keys, equal coupled flag, and membership-equivalent exclusions).  These are proved by a
single mutual induction on fuel whose hypothesis is the recursive refinement statement itself, not a
desired output or a global node-refinement assumption.  The old and guarded node evaluations share
the old predecessor frame callback, because the guarded builder always falls back to the actual old
node computation off the accepted-guard branch.

Because the persisted guard leaf is a *finite carrier* leaf (which may arise from truncation at
`remaining = 0`), no claim is made here that the guard is universally chemically justified for every
molecular leaf; this module proves only the evaluator-level refinement above.

Every exported declaration is guarded by `assert_kernel_only`, so elaboration fails if any of them
depends on `sorryAx`, native evaluator trust, or a project axiom.  Only `propext`,
`Classical.choice` and `Quot.sound` are accepted.
-/

/-! ## Adapting a guarded node result to the spatial-node interface -/

/-- The spatial-node observation synthesized from a guarded node result.  An ordinary result is
returned untouched.  A directly accepted guard contributes a synthetic observation with the actual
physical endpoints and the nonstereogenic geometry; its raw reference fields are the topology
endpoints and carry no chemical claim. -/
def LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (result : LocalizedRule3TerminalGuardedNodeResult input carrierFuel) :
    input.LocalizedRule3SpatialNodeResult :=
  match result with
  | .ordinary observation => observation
  | .direct identity =>
      { left := identity.topology.left
        right := identity.topology.right
        unit :=
          { leftReference := identity.topology.left
            rightReference := identity.topology.right
            geometry := OfficialRule3Geometry.nonstereogenic } }

/-- The synthetic observation reproduces exactly the guarded result's common observable
projection.  This is the only property the recursive key assembly uses. -/
@[simp] theorem LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation_observable
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (result : LocalizedRule3TerminalGuardedNodeResult input carrierFuel) :
    LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable
        (LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation result) =
      result.observable := by
  cases result with
  | ordinary observation => rfl
  | direct identity => rfl

/-- Option-level adaptation of the guarded node observation used by the recursive key builder. -/
def localizedTerminalGuardedObservationAsSpatial
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (value : Option (LocalizedRule3TerminalGuardedNodeResult input carrierFuel)) :
    Option input.LocalizedRule3SpatialNodeResult :=
  Option.map LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation value

/-- Option-level adaptation of the guarded node evaluator's nested result. -/
def localizedTerminalGuardedNodeObservationAsSpatial
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (value : Option (Option (LocalizedRule3TerminalGuardedNodeResult input carrierFuel))) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  Option.map (Option.map LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation) value

/-- The adapted observation has exactly the guarded result's comparison-visible projection. -/
@[simp] theorem localizedTerminalGuardedObservationAsSpatial_observable
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (value : Option (LocalizedRule3TerminalGuardedNodeResult input carrierFuel)) :
    Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable
        (localizedTerminalGuardedObservationAsSpatial value) =
      Option.map LocalizedRule3TerminalGuardedNodeResult.observable value := by
  cases value with
  | none => rfl
  | some result =>
      simp [localizedTerminalGuardedObservationAsSpatial]

/-! ## Root data of a key: priorities and physical incidence from the observable projection -/

/-- Equal terminal-guarded projections give equal Rule-3 root priority layers.  The root priority
layer reads only the unit geometry, which is part of the projection. -/
theorem localizedRule3SpatialRootPriorities_eq_of_terminalProjection_eq
    {input : CertifiedLocalizedCIPInput}
    {left right : Option input.LocalizedRule3SpatialNodeResult}
    (projection :
      Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable left =
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable right) :
    input.localizedRule3SpatialRootPriorities left =
      input.localizedRule3SpatialRootPriorities right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          simp [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable] at projection
  | some left =>
      cases right with
      | none =>
          simp [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable] at projection
      | some right =>
          simp only [Option.map_some, Option.some.injEq] at projection
          have geometry :
              left.unit.geometry = right.unit.geometry :=
            congrArg LocalizedRule3TerminalGuardedObservable.geometry projection
          simp [localizedRule3SpatialRootPriorities, geometry]

/-- A leaf observation list contributes the physical unit of its unique entry. -/
theorem localizedRule3SpatialRootObservations_flatten_physicalUnit_mem_iff
    {input : CertifiedLocalizedCIPInput}
    {left right : Option input.LocalizedRule3SpatialNodeResult}
    (projection :
      Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable left =
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry, entry ∈ (input.localizedRule3SpatialRootObservations left).flatten ∧
        entry.2.physicalUnitId = unit) ↔
      ∃ entry, entry ∈ (input.localizedRule3SpatialRootObservations right).flatten ∧
        entry.2.physicalUnitId = unit := by
  cases left with
  | none =>
      cases right with
      | none => simp [localizedRule3SpatialRootObservations]
      | some right =>
          simp [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable] at projection
  | some left =>
      cases right with
      | none =>
          simp [LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable] at projection
      | some right =>
          simp only [Option.map_some, Option.some.injEq] at projection
          have leftEq : left.left = right.left :=
            congrArg LocalizedRule3TerminalGuardedObservable.left projection
          have rightEq : left.right = right.right :=
            congrArg LocalizedRule3TerminalGuardedObservable.right projection
          simp [localizedRule3SpatialRootObservations,
            LocalizedRule3SpatialNodeResult.physicalUnitId, leftEq, rightEq]

/-- Flattened layer membership is the same as membership in the addressed layers. -/
private theorem exists_layer_entry_iff_exists_flatten
    {α : Type*} (layers : List (List α)) (property : α → Prop) :
    (∃ layer ∈ layers, ∃ entry ∈ layer, property entry) ↔
      ∃ entry, entry ∈ layers.flatten ∧ property entry := by
  induction layers with
  | nil => simp
  | cons layer tail induction =>
      simp only [List.mem_cons, List.flatten_cons, List.mem_append]
      constructor
      · rintro ⟨found, rfl | foundMem, entry, entryMem, entryProperty⟩
        · exact ⟨entry, Or.inl entryMem, entryProperty⟩
        · obtain ⟨entry, entryMem, entryProperty⟩ :=
            induction.mp ⟨found, foundMem, entry, entryMem, entryProperty⟩
          exact ⟨entry, Or.inr entryMem, entryProperty⟩
      · rintro ⟨entry, entryMem | entryMem, entryProperty⟩
        · exact ⟨layer, Or.inl rfl, entry, entryMem, entryProperty⟩
        · obtain ⟨found, foundMem, entry, entryMem, entryProperty⟩ :=
            induction.mpr ⟨entry, entryMem, entryProperty⟩
          exact ⟨found, Or.inr foundMem, entry, entryMem, entryProperty⟩

/-- Equal terminal-guarded projections give equal root physical-unit incidence, for arbitrary
constitutional and Rule-3 priority payloads on the two sides.  Only the leaf observation layer is
read. -/
theorem localizedRule3SpatialRootPhysicalUnitIds_mem_iff_of_terminalProjection_eq
    (input : CertifiedLocalizedCIPInput)
    (constitutionalLeft constitutionalRight : OfficialRuleMajorKey input.Atom)
    (rule3Left rule3Right : List (List (OfficialSparseEntry Nat)))
    {left right : Option input.LocalizedRule3SpatialNodeResult}
    (projection :
      Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable left =
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional := constitutionalLeft
          observations := input.localizedRule3SpatialRootObservations left
          rule3 := rule3Left } ↔
      unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional := constitutionalRight
          observations := input.localizedRule3SpatialRootObservations right
          rule3 := rule3Right } := by
  rw [input.mem_localizedRule3PhysicalUnitIds_iff,
    input.mem_localizedRule3PhysicalUnitIds_iff,
    exists_layer_entry_iff_exists_flatten,
    exists_layer_entry_iff_exists_flatten]
  exact input.localizedRule3SpatialRootObservations_flatten_physicalUnit_mem_iff
    projection unit

/-! ## The executable guarded mutual core -/

mutual

  /-- Terminal-guarded recursive Rule-3 spatial key.  The zero branch is the old structural
  nonunit branch.  The successor branch runs the guarded ordinary-node evaluator first, adapts its
  result to the spatial-node interface, and then performs the old child recursion, sorting and
  parent assembly with the *guarded* child builder. -/
  def buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
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
        let guarded ← localizedRule3TerminalGuardedNodeWithExec?
          input target cursor.occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
          excluded
        let observation := localizedTerminalGuardedObservationAsSpatial guarded
        if children = [] then
          some
            { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
              observations := input.localizedRule3SpatialRootObservations observation
              rule3 := input.localizedRule3SpatialRootPriorities observation }
        else
          let childKeys ← children.mapM
            (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
              target view fuel excluded)
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

  /-- Terminal-guarded two-pass physical-unit frame.  The raw pass, the actual coupled-topology
  resolution, the excluded-unit computation and the rebuilt pass are all retained. -/
  def buildLocalizedTerminalGuardedExtendedRule3FrameExec?
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame
    | 0, _cursors => none
    | fuel + 1, cursors => do
        let rawKeys ← cursors.mapM
          (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
            target view fuel [])
        let topology ← input.localizedRule3CoupledTopologyResolutionExec? rawKeys
        let coupled := topology.isCoupled
        let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
        let keys ← cursors.mapM
          (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
            target view fuel excluded)
        some { rawKeys, coupled, excluded, keys }

end

/-! ## Smoke results: exact zero-fuel agreement and guard-branch callback independence -/

/-- At fuel zero the guarded key builder is literally the old structural key builder. -/
theorem buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_zero_eq_old
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
        target view 0 guardedExcluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view 0 excluded cursor := by
  simp [buildLocalizedTerminalGuardedRecursiveRule3KeyExec?,
    buildLocalizedRerootExtendedShortCircuitRule3KeyExec?]

/-- Every successful old zero-fuel key is reproduced by the guarded builder with a
topology-equivalent key. -/
theorem buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_zero_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed :
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view 0 excluded cursor = some key) :
    ∃ guardedKey : input.LocalizedRerootRecursiveRule3SpatialKey,
      input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
          target view 0 guardedExcluded cursor = some guardedKey ∧
        LocalizedRule3SpatialKeyTopologyEquivalent input key guardedKey := by
  refine ⟨key, ?_, LocalizedRule3SpatialKeyTopologyEquivalent.refl input key⟩
  rw [input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_zero_eq_old]
  exact computed

/-- At fuel zero the guarded frame builder refuses exactly as the old frame builder does. -/
theorem buildLocalizedTerminalGuardedExtendedRule3FrameExec?_zero
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.buildLocalizedTerminalGuardedExtendedRule3FrameExec?
        target view 0 cursors = none := by
  simp [buildLocalizedTerminalGuardedExtendedRule3FrameExec?]

/-- On the actual accepting branch of the guard, the adapted node observation used by the key
builder is independent of the predecessor frame callback.  This is the executable guard-first
property: the guard accepts before any callback value is inspected. -/
theorem localizedTerminalGuardedObservationAsSpatial_guard_branch_callback_independent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (witness : LocalizedRule3TerminalGuardWitness input target view topology)
    (firstCallback secondCallback :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (oddRoute : input.localizedRule3OddRouteCertificate? occurrence = none)
    {ordinaryCertificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence}
    (ordinaryRoute :
      input.localizedRule3OrdinaryRouteCertificate? occurrence = some ordinaryCertificate)
    (topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (guardComputed :
      localizedRule3TerminalGuard? input target view topology = some witness) :
    localizedTerminalGuardedNodeObservationAsSpatial
        (localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
          firstCallback excluded) =
      localizedTerminalGuardedNodeObservationAsSpatial
        (localizedRule3TerminalGuardedNodeWithExec? input target occurrence view
          secondCallback excluded) := by
  unfold localizedRule3TerminalGuardedNodeWithExec?
  simp only [oddRoute, ordinaryRoute, topologyComputed, guardComputed]

/-- The terminal-guarded node evaluator is extensional in the exclusion list: two lists with the
same physical-unit membership give the same nested option.  An accepted guard only performs the
physical-unit `contains` test; every fallback branch is the extended node, whose exclusion
extensionality is the imported theorem. -/
theorem localizedRule3TerminalGuardedNodeWithExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    localizedRule3TerminalGuardedNodeWithExec? input target occurrence view callback left =
      localizedRule3TerminalGuardedNodeWithExec? input target occurrence view callback right := by
  unfold localizedRule3TerminalGuardedNodeWithExec?
  have nodeEq :
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target occurrence view callback left =
        input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target occurrence view callback right :=
    input.localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional
      target occurrence view callback equivalent
  have containsEq : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      left.contains unit = right.contains unit :=
    fun unit => localizedRule3ExclusionEquivalent_contains input equivalent unit
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate => simp only [nodeEq]
  | none =>
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | none => simp only [nodeEq]
      | some certificate =>
          cases topologyComputed :
              input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none => simp only [nodeEq]
          | some topology =>
              cases guardComputed :
                  localizedRule3TerminalGuard? input target view topology with
              | some witness => simp only [guardComputed, containsEq]
              | none => simp only [guardComputed, nodeEq]

/-! ## Sort and parent transport used by the refinement induction -/

/-- Success of a `mapM` produces the pointwise computation relation. -/
private theorem forall₂_of_mapM_eq_some
    {α β : Type*} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results → List.Forall₂ R values results
  | [], results, computed => by
      cases results with
      | nil => exact List.Forall₂.nil
      | cons result rest => simp at computed
  | value :: values, results, computed => by
      cases first : f value with
      | none => simp [first] at computed
      | some result =>
          cases rest : values.mapM f with
          | none => simp [first, rest] at computed
          | some restResults =>
              simp [first, rest] at computed
              subst results
              exact List.Forall₂.cons (sound value result first)
                (forall₂_of_mapM_eq_some f R sound values restResults rest)

/-- Pointwise successful refinements lift to a successful refined `mapM`. -/
private theorem mapM_exists_of_forall₂
    {α β γ : Type*} (f : α → Option β) (R : α → γ → Prop) (S : γ → β → Prop)
    (complete : ∀ a c, R a c → ∃ b, f a = some b ∧ S c b) :
    ∀ (values : List α) (sources : List γ),
      List.Forall₂ R values sources →
        ∃ results, values.mapM f = some results ∧ List.Forall₂ S sources results
  | [], sources, related => by
      cases related
      exact ⟨[], rfl, List.Forall₂.nil⟩
  | value :: values, source :: sources, related => by
      cases related with
      | cons head tail =>
          rcases complete value source head with ⟨result, computed, resultRelated⟩
          rcases mapM_exists_of_forall₂ f R S complete values sources tail with
            ⟨results, computedTail, relatedTail⟩
          exact ⟨result :: results, by simp [computed, computedTail],
            List.Forall₂.cons resultRelated relatedTail⟩

/-- Insertion preserves pointwise topology equivalence.  The comparator reads only the observable
projection, so related keys compare against related keys identically. -/
private theorem insert_forall₂_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    (keyOld keyNew : input.LocalizedRerootRecursiveRule3SpatialKey) :
    ∀ keysOld keysNew,
      LocalizedRule3SpatialKeyTopologyEquivalent input keyOld keyNew →
        List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) keysOld keysNew →
          List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
            (input.insertLocalizedRerootRecursiveRule3SpatialKey keyOld keysOld)
            (input.insertLocalizedRerootRecursiveRule3SpatialKey keyNew keysNew)
  | [], [], keyRelated, _ => List.Forall₂.cons keyRelated List.Forall₂.nil
  | [], _ :: _, _, related => by cases related
  | _ :: _, [], _, related => by cases related
  | headOld :: tailOld, headNew :: tailNew, keyRelated, related => by
      cases related with
      | cons headRelated tailRelated =>
          have sameCompare :
              input.compareLocalizedRerootRecursiveRule3SpatialKeys keyOld headOld =
                input.compareLocalizedRerootRecursiveRule3SpatialKeys keyNew headNew := by
            rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable,
              input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable,
              keyRelated.1, headRelated.1]
          unfold insertLocalizedRerootRecursiveRule3SpatialKey
          rw [sameCompare]
          cases comparison :
              input.compareLocalizedRerootRecursiveRule3SpatialKeys keyNew headNew with
          | lt =>
              exact List.Forall₂.cons headRelated
                (insert_forall₂_topologyEquivalent input keyOld keyNew
                  tailOld tailNew keyRelated tailRelated)
          | eq =>
              exact List.Forall₂.cons keyRelated
                (List.Forall₂.cons headRelated tailRelated)
          | gt =>
              exact List.Forall₂.cons keyRelated
                (List.Forall₂.cons headRelated tailRelated)

/-- The structural descending sort preserves pointwise topology equivalence. -/
private theorem sort_forall₂_topologyEquivalent
    (input : CertifiedLocalizedCIPInput) :
    ∀ keysOld keysNew,
      List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) keysOld keysNew →
        List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
          (input.sortLocalizedRerootRecursiveRule3SpatialKeys keysOld)
          (input.sortLocalizedRerootRecursiveRule3SpatialKeys keysNew)
  | [], [], related => by cases related; exact List.Forall₂.nil
  | [], _ :: _, related => by cases related
  | _ :: _, [], related => by cases related
  | keyOld :: tailOld, keyNew :: tailNew, related => by
      cases related with
      | cons headRelated tailRelated =>
          exact insert_forall₂_topologyEquivalent input keyOld keyNew
            (input.sortLocalizedRerootRecursiveRule3SpatialKeys tailOld)
            (input.sortLocalizedRerootRecursiveRule3SpatialKeys tailNew)
            headRelated (sort_forall₂_topologyEquivalent input tailOld tailNew tailRelated)

/-- Equal constitutional and Rule-3 priority components give equal comparison-visible key
projections; the raw observation payload is deliberately not read. -/
private theorem localizedRerootRule3SpatialKeyObservable_eq_of_constitutional_rule3_eq
    (input : CertifiedLocalizedCIPInput)
    (constitutionalOld constitutionalNew : OfficialRuleMajorKey input.Atom)
    (observationsOld observationsNew :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rule3Old rule3New : List (List (OfficialSparseEntry Nat)))
    (constitutionalEq : constitutionalOld = constitutionalNew)
    (rule3Eq : rule3Old = rule3New) :
    input.localizedRerootRule3SpatialKeyObservable
        { constitutional := constitutionalOld
          observations := observationsOld
          rule3 := rule3Old } =
      input.localizedRerootRule3SpatialKeyObservable
        { constitutional := constitutionalNew
          observations := observationsNew
          rule3 := rule3New } := by
  subst constitutionalOld
  subst rule3Old
  rfl

/-- Physical-unit membership of an assembled parent is the union of the root and merged-child
contributions. -/
private theorem mem_localizedRule3PhysicalUnitIds_parent_iff
    (input : CertifiedLocalizedCIPInput)
    (constitutional : OfficialRuleMajorKey input.Atom)
    (rootObservations mergedObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rule3 : List (List (OfficialSparseEntry Nat)))
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional := constitutional
          observations := rootObservations ++ mergedObservations
          rule3 := rule3 } ↔
      (∃ entry, entry ∈ rootObservations.flatten ∧
          entry.2.physicalUnitId = unit) ∨
        ∃ entry, entry ∈ mergedObservations.flatten ∧
          entry.2.physicalUnitId = unit := by
  rw [input.mem_localizedRule3PhysicalUnitIds_iff,
    exists_layer_entry_iff_exists_flatten, List.flatten_append]
  constructor
  · rintro ⟨entry, entryMem, physical⟩
    rcases List.mem_append.mp entryMem with entryMem | entryMem
    · exact Or.inl ⟨entry, entryMem, physical⟩
    · exact Or.inr ⟨entry, entryMem, physical⟩
  · rintro (⟨entry, entryMem, physical⟩ | ⟨entry, entryMem, physical⟩)
    · exact ⟨entry, List.mem_append.mpr (Or.inl entryMem), physical⟩
    · exact ⟨entry, List.mem_append.mpr (Or.inr entryMem), physical⟩

/-- Assembled-parent transport with *related*, not identical, node-level root data.  The root
Rule-3 priorities must agree and the root physical-unit incidence must correspond; the root
observation payloads themselves need not be equal. -/
theorem assembledParent_topologyEquivalent_of_root_data
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservationsOld rootObservationsNew :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPrioritiesOld rootPrioritiesNew : List (List (OfficialSparseEntry Nat)))
    (childrenOld childrenNew : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (prioritiesEq : rootPrioritiesOld = rootPrioritiesNew)
    (rootUnits : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      (∃ entry, entry ∈ rootObservationsOld.flatten ∧
          entry.2.physicalUnitId = unit) ↔
        ∃ entry, entry ∈ rootObservationsNew.flatten ∧
          entry.2.physicalUnitId = unit)
    (observationsEq : childrenOld.map input.localizedRerootRule3SpatialKeyObservable =
      childrenNew.map input.localizedRerootRule3SpatialKeyObservable)
    (mergedUnits : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      (∃ entry, entry ∈
          (input.mergeLocalizedRerootRule3ObservationChildren childrenOld).flatten ∧
          entry.2.physicalUnitId = unit) ↔
        ∃ entry, entry ∈
          (input.mergeLocalizedRerootRule3ObservationChildren childrenNew).flatten ∧
          entry.2.physicalUnitId = unit) :
    LocalizedRule3SpatialKeyTopologyEquivalent input
      { constitutional := OfficialRuleMajorKey.assemble root
          (childrenOld.map fun child => child.constitutional)
        observations := rootObservationsOld ++
          input.mergeLocalizedRerootRule3ObservationChildren childrenOld
        rule3 := rootPrioritiesOld ++
          input.mergeLocalizedRerootRule3PriorityChildren childrenOld }
      { constitutional := OfficialRuleMajorKey.assemble root
          (childrenNew.map fun child => child.constitutional)
        observations := rootObservationsNew ++
          input.mergeLocalizedRerootRule3ObservationChildren childrenNew
        rule3 := rootPrioritiesNew ++
          input.mergeLocalizedRerootRule3PriorityChildren childrenNew } := by
  constructor
  · have step := input.assembledParent_observable_eq_of_map_eq root
      rootObservationsOld rootPrioritiesOld childrenOld childrenNew observationsEq
    have second : input.localizedRerootRule3SpatialKeyObservable
        { constitutional := OfficialRuleMajorKey.assemble root
            (childrenNew.map fun child => child.constitutional)
          observations := rootObservationsOld ++
            input.mergeLocalizedRerootRule3ObservationChildren childrenNew
          rule3 := rootPrioritiesOld ++
            input.mergeLocalizedRerootRule3PriorityChildren childrenNew } =
      input.localizedRerootRule3SpatialKeyObservable
        { constitutional := OfficialRuleMajorKey.assemble root
            (childrenNew.map fun child => child.constitutional)
          observations := rootObservationsNew ++
            input.mergeLocalizedRerootRule3ObservationChildren childrenNew
          rule3 := rootPrioritiesNew ++
            input.mergeLocalizedRerootRule3PriorityChildren childrenNew } := by
      refine localizedRerootRule3SpatialKeyObservable_eq_of_constitutional_rule3_eq
        input _ _ _ _ _ _ rfl ?_
      rw [prioritiesEq]
    exact step.trans second
  · intro unit
    rw [mem_localizedRule3PhysicalUnitIds_parent_iff input _ rootObservationsOld
          (input.mergeLocalizedRerootRule3ObservationChildren childrenOld)
          (rootPrioritiesOld ++
            input.mergeLocalizedRerootRule3PriorityChildren childrenOld) unit,
      mem_localizedRule3PhysicalUnitIds_parent_iff input _ rootObservationsNew
          (input.mergeLocalizedRerootRule3ObservationChildren childrenNew)
          (rootPrioritiesNew ++
            input.mergeLocalizedRerootRule3PriorityChildren childrenNew) unit]
    constructor
    · rintro (rootMem | mergedMem)
      · exact Or.inl ((rootUnits unit).mp rootMem)
      · exact Or.inr ((mergedUnits unit).mp mergedMem)
    · rintro (rootMem | mergedMem)
      · exact Or.inl ((rootUnits unit).mpr rootMem)
      · exact Or.inr ((mergedUnits unit).mpr mergedMem)

/-- A root key with fixed physical-node key and related terminal-guarded root projections is
topology-equivalent. -/
theorem localizedRule3RootKey_topologyEquivalent_of_terminalProjection_eq
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom)
    {left right : Option input.LocalizedRule3SpatialNodeResult}
    (projection :
      Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable left =
        Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable right) :
    LocalizedRule3SpatialKeyTopologyEquivalent input
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey node true
        observations := input.localizedRule3SpatialRootObservations left
        rule3 := input.localizedRule3SpatialRootPriorities left }
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey node true
        observations := input.localizedRule3SpatialRootObservations right
        rule3 := input.localizedRule3SpatialRootPriorities right } := by
  constructor
  · refine localizedRerootRule3SpatialKeyObservable_eq_of_constitutional_rule3_eq
      input _ _ _ _ _ _ rfl ?_
    exact localizedRule3SpatialRootPriorities_eq_of_terminalProjection_eq projection
  · intro unit
    exact input.localizedRule3SpatialRootPhysicalUnitIds_mem_iff_of_terminalProjection_eq
      (input.moleculeGraph.officialRuleMajorRootKey node true)
      (input.moleculeGraph.officialRuleMajorRootKey node true)
      (input.localizedRule3SpatialRootPriorities left)
      (input.localizedRule3SpatialRootPriorities right) projection unit

/-! ## The mutual refinement induction -/

/-- A successful old key has a successful guarded key at the same fuel under any
membership-equivalent exclusion list, and the two keys are topology-equivalent. -/
def LocalizedTerminalGuardedKeyRefines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) : Prop :=
  ∀ (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId),
    LocalizedRule3ExclusionEquivalent input excluded guardedExcluded →
      ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
        (oldKey : input.LocalizedRerootRecursiveRule3SpatialKey),
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel excluded cursor = some oldKey →
          ∃ guardedKey : input.LocalizedRerootRecursiveRule3SpatialKey,
            input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
                target view fuel guardedExcluded cursor = some guardedKey ∧
              LocalizedRule3SpatialKeyTopologyEquivalent input oldKey guardedKey

/-- A successful old two-pass frame has a successful guarded frame at the same fuel carrying the
frame topology invariant. -/
def LocalizedTerminalGuardedFrameRefines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) : Prop :=
  ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (oldFrame : input.LocalizedRule3CanonicalKeyFrame),
    input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view fuel cursors = some oldFrame →
      ∃ guardedFrame : input.LocalizedRule3CanonicalKeyFrame,
        input.buildLocalizedTerminalGuardedExtendedRule3FrameExec?
            target view fuel cursors = some guardedFrame ∧
          LocalizedRule3ExtendedFrameTopologyEquivalent input oldFrame guardedFrame

/-- Successor key refinement.  The old node evaluation is compared with the guarded node
evaluation under the *same* old predecessor frame callback; the reviewed node agreement theorem
supplies the guarded observation and its projection equality. -/
private theorem localizedTerminalGuardedKey_succ_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (keyInduction : LocalizedTerminalGuardedKeyRefines input target view fuel)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded guardedExcluded)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (oldKey : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed :
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view (fuel + 1) excluded cursor = some oldKey) :
    ∃ guardedKey : input.LocalizedRerootRecursiveRule3SpatialKey,
      input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
          target view (fuel + 1) guardedExcluded cursor = some guardedKey ∧
        LocalizedRule3SpatialKeyTopologyEquivalent input oldKey guardedKey := by
  cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
  | none =>
      simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
        childrenComputed] at computed
  | some children =>
      cases nodeComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
          target cursor.occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
          excluded with
      | none =>
          simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
            childrenComputed, nodeComputed] at computed
      | some observation =>
          rcases localizedRule3TerminalGuardedNodeWithExec?_agrees_with_extended
            input target cursor.occurrence view fuel excluded observation nodeComputed with
            ⟨guardedResult, guardedComputed, projection⟩
          let guardedObservation : Option input.LocalizedRule3SpatialNodeResult :=
            localizedTerminalGuardedObservationAsSpatial guardedResult
          have guardedProjection :
              Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable
                  guardedObservation =
                Option.map LocalizedRule3SpatialNodeResult.toTerminalGuardedObservable
                  observation := by
            exact (localizedTerminalGuardedObservationAsSpatial_observable
              guardedResult).trans projection
          have guardedComputedAtGuarded :
              localizedRule3TerminalGuardedNodeWithExec? input target cursor.occurrence view
                  (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
                  guardedExcluded = some guardedResult := by
            rw [← localizedRule3TerminalGuardedNodeWithExec?_exclusion_extensional
              input target cursor.occurrence view
              (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
              (left := excluded) (right := guardedExcluded) equivalence]
            exact guardedComputed
          by_cases empty : children = []
          · have oldComputedRoot :
                input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                    target view (fuel + 1) excluded cursor =
                  some
                    { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                        cursor.occurrence.1.node true
                      observations := input.localizedRule3SpatialRootObservations observation
                      rule3 := input.localizedRule3SpatialRootPriorities observation } := by
              simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
                childrenComputed, nodeComputed, empty]
            rw [oldComputedRoot] at computed
            have keyEq : oldKey =
                { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                    cursor.occurrence.1.node true
                  observations := input.localizedRule3SpatialRootObservations observation
                  rule3 := input.localizedRule3SpatialRootPriorities observation } :=
              (Option.some.inj computed).symm
            subst oldKey
            refine ⟨
              { constitutional := input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node true
                observations := input.localizedRule3SpatialRootObservations guardedObservation
                rule3 := input.localizedRule3SpatialRootPriorities guardedObservation },
              ?_, ?_⟩
            · simp [buildLocalizedTerminalGuardedRecursiveRule3KeyExec?,
                childrenComputed, guardedComputedAtGuarded, empty]
              exact ⟨rfl, rfl⟩
            · exact input.localizedRule3RootKey_topologyEquivalent_of_terminalProjection_eq
                cursor.occurrence.1.node guardedProjection.symm
          · cases childComputed : children.mapM
                (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                  target view fuel excluded) with
            | none =>
                simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
                  childrenComputed, nodeComputed, empty, childComputed] at computed
            | some childKeys =>
                have oldComputedParent :
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view (fuel + 1) excluded cursor =
                      some
                        { constitutional := OfficialRuleMajorKey.assemble
                            (input.moleculeGraph.officialRuleMajorRootKey
                              cursor.occurrence.1.node false)
                            ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                              childKeys).map fun child => child.constitutional)
                          observations :=
                            input.localizedRule3SpatialRootObservations observation ++
                              input.mergeLocalizedRerootRule3ObservationChildren
                                (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                  childKeys)
                          rule3 :=
                            input.localizedRule3SpatialRootPriorities observation ++
                              input.mergeLocalizedRerootRule3PriorityChildren
                                (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                  childKeys) } := by
                  simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
                    childrenComputed, nodeComputed, empty, childComputed]
                rw [oldComputedParent] at computed
                have keyEq : oldKey =
                    { constitutional := OfficialRuleMajorKey.assemble
                        (input.moleculeGraph.officialRuleMajorRootKey
                          cursor.occurrence.1.node false)
                        ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                          childKeys).map fun child => child.constitutional)
                      observations :=
                        input.localizedRule3SpatialRootObservations observation ++
                          input.mergeLocalizedRerootRule3ObservationChildren
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                              childKeys)
                      rule3 :=
                        input.localizedRule3SpatialRootPriorities observation ++
                          input.mergeLocalizedRerootRule3PriorityChildren
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                              childKeys) } :=
                  (Option.some.inj computed).symm
                subst oldKey
                have childRelations : List.Forall₂
                    (fun child childKey =>
                      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                          target view fuel excluded child = some childKey)
                    children childKeys :=
                  forall₂_of_mapM_eq_some _ _ (fun _ _ old => old)
                    children childKeys childComputed
                rcases mapM_exists_of_forall₂
                  (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
                    target view fuel guardedExcluded)
                  (fun child childKey =>
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel excluded child = some childKey)
                  (LocalizedRule3SpatialKeyTopologyEquivalent input)
                  (fun child childKey childDerived =>
                    keyInduction excluded guardedExcluded equivalence
                      child childKey childDerived)
                  children childKeys childRelations with
                  ⟨guardedChildKeys, guardedChildComputed, guardedChildRelations⟩
                refine ⟨
                  { constitutional := OfficialRuleMajorKey.assemble
                      (input.moleculeGraph.officialRuleMajorRootKey
                        cursor.occurrence.1.node false)
                      ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                        guardedChildKeys).map fun child => child.constitutional)
                    observations :=
                      input.localizedRule3SpatialRootObservations guardedObservation ++
                        input.mergeLocalizedRerootRule3ObservationChildren
                          (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                            guardedChildKeys)
                    rule3 :=
                      input.localizedRule3SpatialRootPriorities guardedObservation ++
                        input.mergeLocalizedRerootRule3PriorityChildren
                          (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                            guardedChildKeys) },
                  ?_, ?_⟩
                · simp [buildLocalizedTerminalGuardedRecursiveRule3KeyExec?,
                    childrenComputed, guardedComputedAtGuarded, empty, guardedChildComputed]
                  exact ⟨rfl, rfl⟩
                · exact input.assembledParent_topologyEquivalent_of_root_data
                    (input.moleculeGraph.officialRuleMajorRootKey
                      cursor.occurrence.1.node false)
                    (input.localizedRule3SpatialRootObservations observation)
                    (input.localizedRule3SpatialRootObservations guardedObservation)
                    (input.localizedRule3SpatialRootPriorities observation)
                    (input.localizedRule3SpatialRootPriorities guardedObservation)
                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys)
                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                      guardedChildKeys)
                    (localizedRule3SpatialRootPriorities_eq_of_terminalProjection_eq
                      guardedProjection.symm)
                    (localizedRule3SpatialRootObservations_flatten_physicalUnit_mem_iff
                      guardedProjection.symm)
                    (input.map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂_of_perm_of_descending
                      childKeys guardedChildKeys
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys)
                      guardedChildRelations
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys)
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending
                        childKeys))
                    (fun unit =>
                      input.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_of_perm
                        childKeys guardedChildKeys
                        (input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys)
                        guardedChildRelations
                        (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys)
                        unit)

/-- Successor frame refinement.  Both passes are preserved: the raw keys are refined at empty
exclusions, the actual coupled topology is transported, the exclusion set is transported by
membership on the actual raw keys, and the rebuilt keys are refined under the transported
exclusions. -/
private theorem localizedTerminalGuardedFrame_succ_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (keyInduction : LocalizedTerminalGuardedKeyRefines input target view fuel)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (oldFrame : input.LocalizedRule3CanonicalKeyFrame)
    (computed :
      input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view (fuel + 1) cursors = some oldFrame) :
    ∃ guardedFrame : input.LocalizedRule3CanonicalKeyFrame,
      input.buildLocalizedTerminalGuardedExtendedRule3FrameExec?
          target view (fuel + 1) cursors = some guardedFrame ∧
        LocalizedRule3ExtendedFrameTopologyEquivalent input oldFrame guardedFrame := by
  cases rawComputed : cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view fuel []) with
  | none =>
      simp [buildLocalizedExtendedShortCircuitRule3FrameExec?, rawComputed] at computed
  | some rawKeys =>
      cases topologyComputed :
          input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
      | none =>
          simp [buildLocalizedExtendedShortCircuitRule3FrameExec?,
            rawComputed, topologyComputed] at computed
      | some topology =>
          cases rebuiltComputed : cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                target view fuel
                (input.localizedRule3CoupledExcludedPhysicalUnits
                  rawKeys topology)) with
          | none =>
              simp [buildLocalizedExtendedShortCircuitRule3FrameExec?,
                rawComputed, topologyComputed, rebuiltComputed] at computed
          | some rebuiltKeys =>
              have frameEq : oldFrame =
                  { rawKeys := rawKeys
                    coupled := topology.isCoupled
                    excluded :=
                      input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
                    keys := rebuiltKeys } :=
                (Option.some.inj (by
                  simpa [buildLocalizedExtendedShortCircuitRule3FrameExec?,
                    rawComputed, topologyComputed, rebuiltComputed] using computed)).symm
              subst oldFrame
              have rawRelations : List.Forall₂
                  (fun cursor key =>
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel [] cursor = some key)
                  cursors rawKeys :=
                forall₂_of_mapM_eq_some _ _ (fun _ _ old => old)
                  cursors rawKeys rawComputed
              rcases mapM_exists_of_forall₂
                (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
                  target view fuel [])
                (fun cursor key =>
                  input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                      target view fuel [] cursor = some key)
                (LocalizedRule3SpatialKeyTopologyEquivalent input)
                (fun cursor key oldComputed =>
                  keyInduction [] [] (input.localizedRule3ExclusionEquivalent_refl [])
                    cursor key oldComputed)
                cursors rawKeys rawRelations with
                ⟨guardedRawKeys, guardedRawComputed, guardedRawRelations⟩
              have resolutionEq :=
                input.localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂
                  rawKeys guardedRawKeys guardedRawRelations
              have guardedTopologyComputed :
                  input.localizedRule3CoupledTopologyResolutionExec?
                      guardedRawKeys = some topology := by
                rw [← resolutionEq]
                exact topologyComputed
              have excludedIff : ∀ unit : input.LocalizedRule3PhysicalUnitId,
                  unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits
                      rawKeys topology ↔
                    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits
                      guardedRawKeys topology :=
                fun unit =>
                  input.mem_localizedRule3CoupledExcludedPhysicalUnits_congruence
                    rawKeys guardedRawKeys guardedRawRelations topology topology
                    topologyComputed guardedTopologyComputed unit
              have excludedEquivalent : LocalizedRule3ExclusionEquivalent input
                  (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology)
                  (input.localizedRule3CoupledExcludedPhysicalUnits
                    guardedRawKeys topology) :=
                fun unit => excludedIff unit
              have rebuiltRelations : List.Forall₂
                  (fun cursor key =>
                    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel
                        (input.localizedRule3CoupledExcludedPhysicalUnits
                          rawKeys topology) cursor = some key)
                  cursors rebuiltKeys :=
                forall₂_of_mapM_eq_some _ _ (fun _ _ old => old)
                  cursors rebuiltKeys rebuiltComputed
              rcases mapM_exists_of_forall₂
                (input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
                  target view fuel
                  (input.localizedRule3CoupledExcludedPhysicalUnits
                    guardedRawKeys topology))
                (fun cursor key =>
                  input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                      target view fuel
                      (input.localizedRule3CoupledExcludedPhysicalUnits
                        rawKeys topology) cursor = some key)
                (LocalizedRule3SpatialKeyTopologyEquivalent input)
                (fun cursor key oldComputed =>
                  keyInduction
                    (input.localizedRule3CoupledExcludedPhysicalUnits
                      rawKeys topology)
                    (input.localizedRule3CoupledExcludedPhysicalUnits
                      guardedRawKeys topology)
                    excludedEquivalent cursor key oldComputed)
                cursors rebuiltKeys rebuiltRelations with
                ⟨guardedRebuiltKeys, guardedRebuiltComputed, guardedRebuiltRelations⟩
              refine ⟨
                { rawKeys := guardedRawKeys
                  coupled := topology.isCoupled
                  excluded :=
                    input.localizedRule3CoupledExcludedPhysicalUnits
                      guardedRawKeys topology
                  keys := guardedRebuiltKeys },
                ?_, ?_⟩
              · simp [buildLocalizedTerminalGuardedExtendedRule3FrameExec?,
                  guardedRawComputed, guardedTopologyComputed, guardedRebuiltComputed]
              · exact ⟨guardedRawRelations, guardedRebuiltRelations, rfl,
                  fun unit => excludedIff unit⟩

/-- Mutual refinement of the guarded key and frame compilers.  The induction hypothesis is a
real recursive statement about successful old evaluations, not a desired output or a global
node-refinement assumption. -/
theorem localizedTerminalGuardedRecursiveRule3_mutual_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel : Nat,
      LocalizedTerminalGuardedKeyRefines input target view fuel ∧
        LocalizedTerminalGuardedFrameRefines input target view fuel
  | 0 => by
      constructor
      · intro excluded guardedExcluded _equivalence cursor oldKey computed
        exact input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_zero_refines
          target view excluded guardedExcluded cursor oldKey computed
      · intro cursors oldFrame computed
        simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at computed
  | fuel + 1 => by
      have prior := input.localizedTerminalGuardedRecursiveRule3_mutual_refines
        target view fuel
      exact ⟨
        fun excluded guardedExcluded equivalence cursor oldKey computed =>
          localizedTerminalGuardedKey_succ_refines input target view fuel prior.1
            excluded guardedExcluded equivalence cursor oldKey computed,
        fun cursors oldFrame computed =>
          localizedTerminalGuardedFrame_succ_refines input target view fuel prior.1
            cursors oldFrame computed⟩

/-! ## Public refinement theorems -/

/-- Every successful old key evaluation is preserved by the guarded recursive builder at the same
fuel, under any membership-equivalent exclusion list, with a topology-equivalent guarded key. -/
theorem buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_refines_old
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    LocalizedTerminalGuardedKeyRefines input target view fuel :=
  (input.localizedTerminalGuardedRecursiveRule3_mutual_refines target view fuel).1

/-- Every successful old frame evaluation is preserved by the guarded two-pass frame at the same
fuel, with pointwise topology-equivalent raw and rebuilt keys, the same coupled flag and the same
exclusion membership. -/
theorem buildLocalizedTerminalGuardedExtendedRule3FrameExec?_refines_old
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    LocalizedTerminalGuardedFrameRefines input target view fuel :=
  (input.localizedTerminalGuardedRecursiveRule3_mutual_refines target view fuel).2

/-- Topology-equivalent keys have equal cumulative Rules-1a--3 comparators.  This is the comparator
form of the refinement guarantee. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_eq_of_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3SpatialKeyTopologyEquivalent input left right) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys left right = Ordering.eq := by
  rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable,
    compareLocalizedRerootRule3SpatialKeyObservable_eq_iff]
  exact related.1

/-- Comparator corollary of key refinement. -/
theorem buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_old_key_compare_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (excluded guardedExcluded : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded guardedExcluded)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (oldKey guardedKey : input.LocalizedRerootRecursiveRule3SpatialKey)
    (oldComputed :
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view fuel excluded cursor = some oldKey)
    (guardedComputed :
      input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
        target view fuel guardedExcluded cursor = some guardedKey) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys oldKey guardedKey =
      Ordering.eq := by
  rcases input.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_refines_old
    target view fuel excluded guardedExcluded equivalence cursor oldKey oldComputed with
    ⟨refinedKey, refinedComputed, related⟩
  rw [guardedComputed] at refinedComputed
  have same : guardedKey = refinedKey := Option.some.inj refinedComputed
  subst guardedKey
  exact input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_of_topologyEquivalent
    related






assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3TerminalGuardedNodeResult.toSpatialObservation_observable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedTerminalGuardedObservationAsSpatial
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedTerminalGuardedObservationAsSpatial_observable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedTerminalGuardedNodeObservationAsSpatial
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialRootPriorities_eq_of_terminalProjection_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialRootObservations_flatten_physicalUnit_mem_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialRootPhysicalUnitIds_mem_iff_of_terminalProjection_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedExtendedRule3FrameExec?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_zero_eq_old
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_zero_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedExtendedRule3FrameExec?_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedTerminalGuardedObservationAsSpatial_guard_branch_callback_independent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3TerminalGuardedNodeWithExec?_exclusion_extensional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.assembledParent_topologyEquivalent_of_root_data
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3RootKey_topologyEquivalent_of_terminalProjection_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedTerminalGuardedKeyRefines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedTerminalGuardedFrameRefines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedTerminalGuardedRecursiveRule3_mutual_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_refines_old
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedExtendedRule3FrameExec?_refines_old
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_of_topologyEquivalent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedTerminalGuardedRecursiveRule3KeyExec?_old_key_compare_eq

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
