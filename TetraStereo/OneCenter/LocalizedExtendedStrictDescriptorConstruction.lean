import TetraStereo.OneCenter.LocalizedShortCircuitReadiness
import TetraStereo.OneCenter.LocalizedShortCircuitStrictOrder
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitBoundedDescriptor

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Strict-order descriptor construction for the extended (demand-driven) Rule 3 evaluator

The ordinary strict construction (`LocalizedShortCircuitStrictCompleteness`) derives its complete
Rule 3 frame from a callback-free carrier certificate plus independent topology resolution, and
then transfers the strict priority ranking, the production tracked order, and the final descriptor
to every auxiliary dependency view.  This module performs the same transfer for the
descriptor-bearing extended evaluator whose Rule 3 reader is
`buildLocalizedRerootExtendedShortCircuitRule3KeyExec?`.

The absence of recursive requests alone does not guarantee successful node evaluation.  We
therefore isolate the stronger input-derived fact used by this construction.
A `LocalizedExtendedRule3ReadyNodeCertificate` records,
for one occurrence, a single observation together with a proof that the extended node reader
returns exactly that observation for every target occurrence, dependency view, recursive frame
callback, and physical-unit exclusion list.  The certificate also records the empty request list
that the bounded-descriptor stability argument needs.  The certificate is constructed by finite
inspection of the molecule:

* structurally terminal occurrences and occurrences on an ordinary or omission route reuse the
  existing `localizedRule3CallbackFreeNodeCertificate?`;
* nonordinary odd-cumulene routes are compiled from the executable odd topology, two strict
  constitutional endpoint certificates, and the executable exact-rational spatial unit.

No completed key, comparison frame, priority order, descriptor, or auxiliary assignment is
supplied to the constructor.  From a carrier-wide ready certificate, the complete recursive keys
exist at the linear structural bound uniformly in target, view, and exclusion list; the two-pass
frame and production descriptor are then constructed using the readiness hypotheses below.
The all-views theorem requires topology resolvability, a strict full-Rule-3 ranking, a descending
ligand permutation, coordinates, and independent rational geometry.  The executable certificate
constructor checks these ingredients for one supplied view; it does not produce the all-views
readiness package.

## Residual obligations

The ready node certificate is a sufficient structural class.  It does not cover occurrences whose
endpoint priority genuinely depends on the auxiliary view (equal first-sphere and equal
constitutional keys, so that the deferred complete endpoint compiler is demanded), nor geometric
nodes on cyclic, even-cumulene, or interacting routes that the existing callback-free constructor
refuses.  Those cases require a view-parametric demand-rank completeness argument; nothing in this
module assumes them away silently.
-/

/-! ## Input-derived extended node readiness -/

/-- Local evidence that the extended node reader is total, view-independent, and callback-free for
one occurrence.  It quantifies over the real production callback (the predecessor Rule 3 frame), so
it is strictly stronger than listing the requests. -/
structure LocalizedExtendedRule3ReadyNodeCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) where
  observation : List input.LocalizedRule3PhysicalUnitId →
    Option input.LocalizedRule3SpatialNodeResult
  computed : ∀ (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId),
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = some (observation excluded)
  empty : input.rule3ExtendedNodeCallbackRequests occurrence = []

/-- Finite constructor.  Odd-cumulene routes use strict constitutional endpoint comparisons, so
their observation is independent of the auxiliary view exactly as on ordinary routes.  A route
with neither a ready odd certificate nor an existing callback-free node certificate is refused. -/
def localizedExtendedRule3ReadyNodeCertificate?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedExtendedRule3ReadyNodeCertificate occurrence) :=
  if emptyCheck : (input.rule3ExtendedNodeCallbackRequests occurrence).isEmpty = true then
    match odd : input.localizedRule3OddRouteCertificate? occurrence with
    | none =>
        match input.localizedRule3CallbackFreeNodeCertificate? occurrence with
        | none => none
        | some certificate =>
            some
              { observation := certificate.observation
                computed := by
                  intro target view callback excluded
                  simpa [localizedRule3ExtendedShortCircuitNodeWithExec?, odd]
                    using certificate.computed target view callback excluded
                empty := by
                  simpa using emptyCheck }
    | some _ =>
        match topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
        | none => none
        | some topology =>
            match leftComputed : input.localizedRule3StrictEndpointCertificate?
                topology.initial.left topology.initial.right topology.initial.leftCursor with
            | none => none
            | some left =>
                match rightComputed : input.localizedRule3StrictEndpointCertificate?
                    topology.right topology.rightPartner topology.rightCursor with
                | none => none
                | some right =>
                    match unitComputed : input.localizedRule3ExtendedSpatialUnitOfPriorities?
                        topology.initial.left topology.right
                        left.result.priority right.result.priority with
                    | none => none
                    | some unit =>
                        let spatial : input.LocalizedRule3ShortCircuitOddSpatialResult fuel :=
                          { topology, leftEndpoint := left.result,
                            rightEndpoint := right.result, unit }
                        let observed :=
                          input.localizedRule3ShortCircuitOddSpatialObservation spatial
                        some
                          { observation := fun excluded =>
                              if excluded.contains observed.physicalUnitId
                                then none else some observed
                            computed := by
                              intro target view callback excluded
                              simp [localizedRule3ExtendedShortCircuitNodeWithExec?, odd,
                                localizedRule3ShortCircuitOddSpatialUnitWithExec?,
                                topologyComputed, left.computed target view callback,
                                right.computed target view callback, unitComputed,
                                spatial, observed]
                            empty := by
                              simpa using emptyCheck }
  else none

/-- A carrier-wide ready certificate.  Every occurrence of the finite carrier is inspected by the
executable constructor above; no recursive result is assumed. -/
structure LocalizedExtendedRule3ReadyCarrierCertificate
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) : Type where
  ready : ∀ occurrence : input.LocalizedCIPOccurrence fuel,
    ∃ certificate, input.localizedExtendedRule3ReadyNodeCertificate? occurrence = some certificate

def localizedExtendedRule3ReadyCarrierCertificate?
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    Option (input.LocalizedExtendedRule3ReadyCarrierCertificate fuel) :=
  if tested : (input.localizedOccurrenceCarrier fuel).all (fun occurrence =>
      (input.localizedExtendedRule3ReadyNodeCertificate? occurrence).isSome) = true then
    some
      { ready := by
          intro occurrence
          have has := (List.all_eq_true.mp tested) occurrence
            (input.localizedOccurrenceCarrier_complete fuel occurrence)
          cases computed : input.localizedExtendedRule3ReadyNodeCertificate? occurrence with
          | none => simp [computed] at has
          | some certificate => exact ⟨certificate, rfl⟩ }
  else none

/-- The ready certificate supplies the empty-request certificate used by bounded-descriptor
stability. -/
def LocalizedExtendedRule3ReadyCarrierCertificate.toNoCallback
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (ready : input.LocalizedExtendedRule3ReadyCarrierCertificate fuel) :
    input.LocalizedExtendedRule3NoCallbackCertificate fuel :=
  { empty := fun occurrence => by
      obtain ⟨certificate, _⟩ := ready.ready occurrence
      exact certificate.empty }

/-! ## Structural completeness of extended Rule 3 keys -/

private theorem mapM_exists_of_total {α β : Type} (f : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, ∃ result, f value = some result) →
      ∃ results, values.mapM f = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, total => by
      obtain ⟨result, head⟩ := total value (by simp)
      obtain ⟨results, tail⟩ := mapM_exists_of_total f values
        (fun value present => total value (by simp [present]))
      exact ⟨result :: results, by simp [head, tail]⟩

private theorem mapM_total_length {α β : Type} (f : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM f = some results → results.length = values.length
  | [], results, computed => by
      simp at computed
      subst results
      rfl
  | value :: values, results, computed => by
      cases head : f value with
      | none => simp [head] at computed
      | some result =>
          cases tail : values.mapM f with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst results
              simp [mapM_total_length f values rest tail]

private theorem mapM_forall₂_of_sound {α β : Type} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ values results, values.mapM f = some results → List.Forall₂ R values results
  | [], results, computed => by
      simp at computed
      subst results
      exact .nil
  | value :: values, results, computed => by
      cases head : f value with
      | none => simp [head] at computed
      | some result =>
          cases tail : values.mapM f with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst results
              exact .cons (sound value result head)
                (mapM_forall₂_of_sound f R sound values rest tail)

/-- Every ready occurrence yields a complete extended Rule 3 key beyond its structural cursor
budget, uniformly in the target occurrence, the dependency view, and the exclusion list. -/
theorem exists_extendedShortCircuitRule3Key_of_budget_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedExtendedRule3ReadyCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor < fuel →
      ∃ key, input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view fuel excluded cursor = some key
  | 0, _, _, covered => by omega
  | fuel + 1, cursor, valid, covered => by
      let children := input.executableLocalizedRerootChildren cursor
      have childrenComputed : input.executableLocalizedRerootChildren? cursor = some children := rfl
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      obtain ⟨certificate, _⟩ := ready.ready cursor.occurrence
      let observation := certificate.observation excluded
      have nodeComputed := certificate.computed target view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel) excluded
      by_cases empty : children = []
      · refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }, ?_⟩
        simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?, childrenComputed,
          nodeComputed, empty, observation]
      · have childComplete : ∀ child ∈ children, ∃ key,
            input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel excluded child = some key := by
          intro child present
          have childValid := input.localizedRerootChild_valid
            cursor child children derived present
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid derived present
          exact input.exists_extendedShortCircuitRule3Key_of_budget_lt
            ready target view excluded fuel child childValid (by omega)
        obtain ⟨childKeys, childKeysComputed⟩ := mapM_exists_of_total
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel excluded)
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
        simp [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?, childrenComputed,
          nodeComputed, empty, childKeysComputed, observation, sorted]

/-- The certified structural class needs only the linear Rule 3 key budget. -/
theorem exists_extendedShortCircuitRule3Key_at_linear_bound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedExtendedRule3ReadyCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view (2 * (carrierFuel + 1) + 1) excluded cursor = some key := by
  apply input.exists_extendedShortCircuitRule3Key_of_budget_lt
    ready target view excluded _ cursor valid
  have bounded := input.localizedRerootCursorBudget_le_twice cursor
  omega

/-- At the linear frame budget both extended key passes are guaranteed.  The only remaining frame
failure is the original coupled-topology ambiguity check, which stays explicit.  The returned
frame is produced by the executable, not supplied by the caller. -/
theorem extendedShortCircuitRule3Frame_exists_at_linear_bound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (ready : input.LocalizedExtendedRule3ReadyCarrierCertificate carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (length : cursors.length = 4)
    (valid : ∀ cursor ∈ cursors, input.LocalizedRerootCursorValid cursor)
    (unambiguous : ∀ rawKeys,
      List.Forall₂ (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
        target view (2 * (carrierFuel + 1) + 1) []) cursors rawKeys →
      ∃ topology, input.DeclarativeLocalizedRule3CoupledTopologyResolution rawKeys topology) :
    ∃ frame, input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view (2 * (carrierFuel + 1) + 2) cursors = some frame ∧
      frame.keys.length = 4 := by
  obtain ⟨rawKeys, rawComputed⟩ := mapM_exists_of_total
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view (2 * (carrierFuel + 1) + 1) []) cursors
    (fun cursor present => input.exists_extendedShortCircuitRule3Key_at_linear_bound
      ready target view [] cursor (valid cursor present))
  have rawDerived : List.Forall₂
      (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
        target view (2 * (carrierFuel + 1) + 1) []) cursors rawKeys :=
    mapM_forall₂_of_sound
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view (2 * (carrierFuel + 1) + 1) [])
      (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
        target view (2 * (carrierFuel + 1) + 1) [])
      (fun cursor key computed =>
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_sound
          target view (2 * (carrierFuel + 1) + 1) [] cursor key computed)
      cursors rawKeys rawComputed
  obtain ⟨topology, topologyDerived⟩ := unambiguous rawKeys rawDerived
  have topologyComputed : input.localizedRule3CoupledTopologyResolutionExec? rawKeys =
      some topology := by
    rw [input.localizedRule3CoupledTopologyResolutionExec?_eq_original]
    exact (input.localizedRule3CoupledTopologyResolution?_eq_some_iff
      rawKeys topology).mpr topologyDerived
  let excluded := input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
  obtain ⟨keys, keysComputed⟩ := mapM_exists_of_total
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view (2 * (carrierFuel + 1) + 1) excluded) cursors
    (fun cursor present => input.exists_extendedShortCircuitRule3Key_at_linear_bound
      ready target view excluded cursor (valid cursor present))
  let frame : input.LocalizedRule3CanonicalKeyFrame :=
    { rawKeys, coupled := topology.isCoupled, excluded, keys }
  refine ⟨frame, ?_, ?_⟩
  · have step : 2 * (carrierFuel + 1) + 2 = (2 * (carrierFuel + 1) + 1) + 1 := by omega
    rw [step, buildLocalizedExtendedShortCircuitRule3FrameExec?, rawComputed]
    simp [topologyComputed, keysComputed, frame, excluded]
  · have computedLength := mapM_total_length
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view (2 * (carrierFuel + 1) + 1) excluded) cursors keys keysComputed
    exact computedLength.trans length

/-! ## Strict readiness and universal descriptor completeness -/

/-- Independent sufficient conditions for a tetrahedral center whose complete extended Rule 3
order is settled by strict full-Rule-3 priorities at every auxiliary view.  The ready carrier
certificate is input-derived; topology resolution is quantified over independently derived first
passes; the priority, its injectivity, and the geometric evidence are the only non-computational
facts.  No frame, tracked order, or descriptor is supplied. -/
structure LocalizedExtendedStrictRule3TetrahedralReadiness
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (raw : RS) where
  carrierReady : input.LocalizedExtendedRule3ReadyCarrierCertificate carrierFuel
  center : input.TetrahedralCenter
  centerMeaning : input.RealTetrahedralCenterNode target.1.node center
  base : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base
  unambiguous : ∀ (view : input.LocalizedDependencyView target) rawKeys,
    List.Forall₂ (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
      target view (2 * (carrierFuel + 1) + 1) []) base.cursors rawKeys →
    ∃ topology, input.DeclarativeLocalizedRule3CoupledTopologyResolution rawKeys topology
  priority : Fin 4 → Nat
  priorityInjective : Function.Injective priority
  ranked : ∀ (view : input.LocalizedDependencyView target)
      (frame : input.LocalizedRule3CanonicalKeyFrame)
      (length : frame.keys.length = 4),
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view
      (2 * (carrierFuel + 1) + 2) base.cursors frame →
    ∀ left right : Fin 4, left ≠ right →
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (frame.keys.get (Fin.cast length.symm left))
        (frame.keys.get (Fin.cast length.symm right)) =
          compare (priority left) (priority right)
  order : List (Fin 4)
  permutation : order.Perm (List.finRange 4)
  descending : order.Pairwise (fun left right => priority right < priority left)
  points : List CartesianPoint3
  pointsMeaning : List.Forall₂
    (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
      (base.cursorAt index) point) order points
  geometry : RationalTetrahedralDescriptor points raw

private theorem extended_spatial_map_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points, List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (base.cursorAt index) point) order points →
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
        (base.cursorAt index)) = some points
  | [], [], .nil => rfl
  | index :: order, point :: points, .cons head tail => by
      have computed := (input.localizedRerootCursorSpatialPoint?_eq_some_iff
        (base.cursorAt index) point).mpr head
      simp [computed, input.extended_spatial_map_complete base order points tail]

private theorem extended_spatial_map_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points, (order : List (Fin 4)).mapM
      (fun index => input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) =
        some points →
      List.Forall₂ (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (base.cursorAt index) point) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact .nil
  | index :: order, points, computed => by
      cases head : input.localizedRerootCursorSpatialPoint? (base.cursorAt index) with
      | none => simp [head] at computed
      | some point =>
          cases tail : order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
              (base.cursorAt index)) with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst points
              exact .cons ((input.localizedRerootCursorSpatialPoint?_eq_some_iff
                (base.cursorAt index) point).mp head)
                (input.extended_spatial_map_sound base order rest tail)

/-- The strict extended construction: for every auxiliary dependency view, the production
descriptor evaluator emits the readiness package's geometrically specified descriptor.  The
complete two-pass Rule 3 frame, the four Rule 45 keys, and the production tracked order are
constructed from the supplied ranking, descending permutation, coordinates, and rational
orientation. -/
theorem extendedStrictRule3_descriptor_total_all_views
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (raw : RS)
    (ready : input.LocalizedExtendedStrictRule3TetrahedralReadiness target raw) :
    ∀ view : input.LocalizedDependencyView target,
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view =
        some (.chiral raw) := by
  have valid : ∀ cursor ∈ ready.base.cursors, input.LocalizedRerootCursorValid cursor := by
    intro cursor present
    exact input.localizedRerootChild_valid { occurrence := target, previous? := none }
      cursor ready.base.cursors ready.baseMeaning.1 present
  intro view
  obtain ⟨frame, frameComputed, frameLength⟩ :=
    input.extendedShortCircuitRule3Frame_exists_at_linear_bound
      ready.carrierReady target view ready.base.cursors ready.base.length_eq valid
      (ready.unambiguous view)
  have frameDerived := input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound
    target view (2 * (carrierFuel + 1) + 2) ready.base.cursors frame frameComputed
  have productionFrame : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      ready.base.cursors = some frame := by
    rw [input.extendedShortCircuitRule3Frame_stable_above_linear_bound
      ready.carrierReady.toNoCallback target view ready.base.cursors valid
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      (2 * (carrierFuel + 1) + 2)
      (localizedExtendedLinearFuel_le_production carrierFuel) (Nat.le_refl _)]
    exact frameComputed
  obtain ⟨rule45Keys, rule45Computed⟩ := mapM_exists_of_total
    (input.buildLocalizedRerootCompoundRule45KeyExec? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) ready.base.cursors (by
        intro cursor present
        obtain ⟨key, computed⟩ := input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor present)
        refine ⟨key, ?_⟩
        rw [← buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
        exact computed)
  have rule45Length : rule45Keys.length = ready.base.cursors.length :=
    mapM_total_length _ _ _ rule45Computed
  have rule45Four : rule45Keys.length = 4 := rule45Length.trans ready.base.length_eq
  let keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel :=
    { rule3Frame := frame, rule3Length := frameLength, rule45Keys, rule45Length := rule45Four }
  have keysComputed : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view ready.base = some keys := by
    simp [buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?,
      productionFrame, frameLength, rule45Computed, rule45Four, keys]
  have ranked : ∀ left right : Fin 4, left ≠ right →
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (keys.keyAt left).rule3 (keys.keyAt right).rule3 =
          compare (ready.priority left) (ready.priority right) :=
    ready.ranked view frame frameLength frameDerived
  have trackedComputed := input.trackedOrder_total_of_strictRule3 keys ready.priority
    ready.priorityInjective ranked ready.order ready.permutation ready.descending
  have centerComputed := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target ready.center).mpr ready.centerMeaning
  have baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some ready.base := by
    rw [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target ready.base).mpr
      ready.baseMeaning
  have pointsComputed := input.extended_spatial_map_complete ready.base ready.order
    ready.points ready.pointsMeaning
  let evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel :=
    { center := ready.center, base := ready.base, keys,
      tracked := { highestFirst := ready.order, pseudoComparisons := 0 }, points := ready.points }
  have evidenceComputed : input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
      target view = some evidence := by
    simp [localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?, centerComputed,
      baseComputed, keysComputed, trackedComputed, pointsComputed, evidence]
  have geometryComputed :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff ready.points raw).mpr ready.geometry
  simp [localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?, evidenceComputed,
    evidence, geometryComputed]

/-! ## Executable per-view certificate -/

/-- Finite evidence for a strict descriptor at one dependency view.  Every field is produced by
`localizedExtendedStrictRule3DescriptorCertificate?`; the frame is the actual extended linear
frame and the priority is computed by counting smaller Rule 3 keys. -/
structure LocalizedExtendedStrictRule3DescriptorCertificate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (raw : RS) where
  carrierReady : input.LocalizedExtendedRule3ReadyCarrierCertificate carrierFuel
  center : input.TetrahedralCenter
  centerMeaning : input.RealTetrahedralCenterNode target.1.node center
  base : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  baseMeaning : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base
  frame : input.LocalizedRule3CanonicalKeyFrame
  frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
    (2 * (carrierFuel + 1) + 2) base.cursors = some frame
  frameLength : frame.keys.length = 4
  priority : Fin 4 → Nat
  priorityInjective : Function.Injective priority
  ranked : ∀ left right : Fin 4, left ≠ right →
    input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keys.get (Fin.cast frameLength.symm left))
      (frame.keys.get (Fin.cast frameLength.symm right)) =
        compare (priority left) (priority right)
  order : List (Fin 4)
  permutation : order.Perm (List.finRange 4)
  descending : order.Pairwise (fun left right => priority right < priority left)
  points : List CartesianPoint3
  pointsMeaning : List.Forall₂
    (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
      (base.cursorAt index) point) order points
  geometry : RationalTetrahedralDescriptor points raw

/-- A constructed per-view certificate forces the production descriptor for that view.  The
production frame is obtained from the linear frame by the proved extended stability bound, and the
remaining rules are constructed exactly as in the ordinary strict certificate. -/
theorem LocalizedExtendedStrictRule3DescriptorCertificate.total
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target} {raw : RS}
    (ready : input.LocalizedExtendedStrictRule3DescriptorCertificate target view raw) :
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view =
      some (.chiral raw) := by
  have valid : ∀ cursor ∈ ready.base.cursors, input.LocalizedRerootCursorValid cursor := by
    intro cursor present
    exact input.localizedRerootChild_valid { occurrence := target, previous? := none }
      cursor ready.base.cursors ready.baseMeaning.1 present
  have productionFrame : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      ready.base.cursors = some ready.frame := by
    rw [input.extendedShortCircuitRule3Frame_stable_above_linear_bound
      ready.carrierReady.toNoCallback target view ready.base.cursors valid
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      (2 * (carrierFuel + 1) + 2)
      (localizedExtendedLinearFuel_le_production carrierFuel) (Nat.le_refl _)]
    exact ready.frameComputed
  obtain ⟨rule45Keys, rule45Computed⟩ := mapM_exists_of_total
    (input.buildLocalizedRerootCompoundRule45KeyExec? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) ready.base.cursors (by
        intro cursor present
        obtain ⟨key, computed⟩ := input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor present)
        refine ⟨key, ?_⟩
        rw [← buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
        exact computed)
  have rule45Length : rule45Keys.length = ready.base.cursors.length :=
    mapM_total_length _ _ _ rule45Computed
  have rule45Four : rule45Keys.length = 4 := rule45Length.trans ready.base.length_eq
  let keys : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel :=
    { rule3Frame := ready.frame, rule3Length := ready.frameLength,
      rule45Keys, rule45Length := rule45Four }
  have keysComputed : input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
      target view ready.base = some keys := by
    simp [buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?,
      productionFrame, ready.frameLength, rule45Computed, rule45Four, keys]
  have ranked : ∀ left right : Fin 4, left ≠ right →
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (keys.keyAt left).rule3 (keys.keyAt right).rule3 =
          compare (ready.priority left) (ready.priority right) :=
    ready.ranked
  have trackedComputed := input.trackedOrder_total_of_strictRule3 keys ready.priority
    ready.priorityInjective ranked ready.order ready.permutation ready.descending
  have centerComputed := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target ready.center).mpr ready.centerMeaning
  have baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some ready.base := by
    rw [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target ready.base).mpr
      ready.baseMeaning
  have pointsComputed := input.extended_spatial_map_complete ready.base ready.order
    ready.points ready.pointsMeaning
  let evidence : input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel :=
    { center := ready.center, base := ready.base, keys,
      tracked := { highestFirst := ready.order, pseudoComparisons := 0 }, points := ready.points }
  have evidenceComputed : input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
      target view = some evidence := by
    simp [localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?, centerComputed,
      baseComputed, keysComputed, trackedComputed, pointsComputed, evidence]
  have geometryComputed :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff ready.points raw).mpr ready.geometry
  simp [localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?, evidenceComputed,
    evidence, geometryComputed]

/-- Count smaller extended Rule 3 keys to propose a finite rank.  The constructor checks
injectivity and all distinct-pair comparisons, so no unproved comparator law is trusted. -/
def localizedExtendedRule3FrameRank
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3CanonicalKeyFrame) (length : frame.keys.length = 4)
    (slot : Fin 4) : Nat :=
  ((List.finRange 4).filter fun other =>
    input.compareLocalizedRerootRecursiveRule3SpatialKeys
      (frame.keys.get (Fin.cast length.symm slot))
      (frame.keys.get (Fin.cast length.symm other)) == Ordering.gt).length

/-- Automatically construct a strict extended descriptor certificate at one view.  The ready
carrier scan, the extended linear frame, the strict rank, the tracked permutation, the exact
spatial points, and the rational descriptor are all computed; the caller supplies only the
molecule and the dependency view.  Refusal means this sufficient strict class was not certified at
this view, not that the extended evaluator refuses. -/
def localizedExtendedStrictRule3DescriptorCertificate?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (Sigma fun raw : RS =>
      input.LocalizedExtendedStrictRule3DescriptorCertificate target view raw) :=
  match input.localizedExtendedRule3ReadyCarrierCertificate? carrierFuel with
  | none => none
  | some carrierReady =>
    match centerComputed : input.localizedOccurrenceDescriptorCenter? target with
    | none => none
    | some center =>
      match baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => none
      | some base =>
        match frameComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
            (2 * (carrierFuel + 1) + 2) base.cursors with
        | none => none
        | some frame =>
          if frameLength : frame.keys.length = 4 then
            let priority := input.localizedExtendedRule3FrameRank frame frameLength
            if injective : Function.Injective priority then
              if ranked : ∀ left right : Fin 4, left ≠ right →
                  input.compareLocalizedRerootRecursiveRule3SpatialKeys
                    (frame.keys.get (Fin.cast frameLength.symm left))
                    (frame.keys.get (Fin.cast frameLength.symm right)) =
                      compare (priority left) (priority right) then
                match sorted : sortFourLocalizedLigandsTracked
                    (strictRankComparison priority) with
                | none => none
                | some tracked =>
                  match pointsComputed : tracked.highestFirst.mapM (fun index =>
                      input.localizedRerootCursorSpatialPoint? (base.cursorAt index)) with
                  | none => none
                  | some points =>
                    match geometryComputed : descriptorOfPriorityOrderedPoints? points with
                    | none => none
                    | some raw =>
                      some ⟨raw, {
                        carrierReady := carrierReady, center,
                        centerMeaning := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
                          target center).mp centerComputed
                        base
                        baseMeaning := (input.localizedOccurrenceFourLigandFrame?_eq_some_iff
                          target base).mp (by
                            rwa [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
                              at baseComputed)
                        frame, frameComputed, frameLength, priority,
                        priorityInjective := injective, ranked
                        order := tracked.highestFirst
                        permutation := by
                          obtain ⟨result, computed, perm, _, _⟩ :=
                            sortFourLocalizedLigandsTracked_strictRank_total priority injective
                          have same := Option.some.inj (sorted.symm.trans computed)
                          simpa [same] using perm
                        descending := by
                          obtain ⟨result, computed, _, descending, _⟩ :=
                            sortFourLocalizedLigandsTracked_strictRank_total priority injective
                          have same := Option.some.inj (sorted.symm.trans computed)
                          simpa [same] using descending
                        points
                        pointsMeaning := input.extended_spatial_map_sound
                          base tracked.highestFirst points pointsComputed
                        geometry :=
                          (descriptorOfPriorityOrderedPoints?_eq_some_iff points raw).mp
                            geometryComputed
                      }⟩
              else none
            else none
          else none

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
