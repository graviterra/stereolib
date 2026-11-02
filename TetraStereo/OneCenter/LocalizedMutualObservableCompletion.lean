import TetraStereo.OneCenter.LocalizedRule3SortedParentTransport
import TetraStereo.OneCenter.LocalizedRule3ExclusionExtensionality

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput









































/-! ## Reusable frame equivalence

This module owns the frame-level equivalence relation used by the converse.  It is the exact
invariant transported by the two frame passes: pointwise topology equivalence of the raw and the
rebuilt key lists, agreement of the coupled flag, and membership (not list) equivalence of the
exclusion payloads. -/

/-- The frame invariant carried by the mutual converse.  `derived` is the independent declarative
frame and `compiled` is the executable frame: raw and rebuilt keys are pointwise
topology-equivalent, the coupled flag agrees, and the two exclusion lists have exactly the same
membership (their order and multiplicity are deliberately unconstrained). -/
def LocalizedRule3ExtendedFrameTopologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    (derived compiled : input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
      derived.rawKeys compiled.rawKeys ∧
    List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
      derived.keys compiled.keys ∧
    compiled.coupled = derived.coupled ∧
    ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ derived.excluded ↔ unit ∈ compiled.excluded

/-! ## Completeness statements and the node-completion interface -/

/-- Frame completeness at one fuel: every independent frame derivation has an executable frame at
the same fuel carrying the frame invariant. -/
def LocalizedExtendedShortCircuitRule3FrameCompleteAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) : Prop :=
  ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame),
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame
        target view fuel cursors frame →
    ∃ compiledFrame : input.LocalizedRule3CanonicalKeyFrame,
      input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view fuel cursors = some compiledFrame ∧
        LocalizedRule3ExtendedFrameTopologyEquivalent input frame compiledFrame

/-- Node completeness at one fuel: an independent extended-node derivation produces the same
`Option` observation from the executable extended node reader, for membership-equivalent exclusion
lists and the concrete predecessor-frame callback. -/
def LocalizedRule3ExtendedShortCircuitNodeCompleteAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (frameFuel : Nat)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  ∀ (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excluded compiledExcluded : List input.LocalizedRule3PhysicalUnitId),
    LocalizedRule3ExclusionEquivalent input excluded compiledExcluded →
    ∀ observation : Option input.LocalizedRule3SpatialNodeResult,
      input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
        target view
        (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
        excluded occurrence observation →
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        compiledExcluded = some observation




def LocalizedRule3ExtendedShortCircuitNodeComplete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  ∀ frameFuel,
    LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view frameFuel →
      LocalizedRule3ExtendedShortCircuitNodeCompleteAt input frameFuel target view

/-- Key completeness at one fuel: an independent key derivation under `excluded` has an executable
key at the same fuel under any membership-equivalent `compiledExcluded` list, topology-equivalent
to the derived key. -/
def LocalizedRerootExtendedShortCircuitRule3KeyCompleteAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) : Prop :=
  ∀ (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey),
    input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
        target view fuel excluded cursor key →
    ∀ (compiledExcluded : List input.LocalizedRule3PhysicalUnitId),
      LocalizedRule3ExclusionEquivalent input excluded compiledExcluded →
      ∃ compiledKey : input.LocalizedRerootRecursiveRule3SpatialKey,
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel compiledExcluded cursor = some compiledKey ∧
          LocalizedRule3SpatialKeyTopologyEquivalent input key compiledKey

/-! ## Existential `List.mapM` construction along `Forall₂` -/

/-- If every related source value has a related executable result, the whole optional `mapM`
succeeds with a pointwise-related result list. -/
private theorem mapM_complete_exists_of_forall₂
    {α β γ : Type*} (f : α → Option β) (R : α → γ → Prop) (S : γ → β → Prop)
    (complete : ∀ a c, R a c → ∃ b, f a = some b ∧ S c b) :
    ∀ as cs, List.Forall₂ R as cs → ∃ bs, as.mapM f = some bs ∧ List.Forall₂ S cs bs
  | [], cs, forall₂ => by
      cases forall₂
      exact ⟨[], rfl, List.Forall₂.nil⟩
  | a :: as, c :: cs, forall₂ => by
      cases forall₂ with
      | cons head tail =>
          rcases complete a c head with ⟨b, computed, related⟩
          rcases mapM_complete_exists_of_forall₂ f R S complete as cs tail with
            ⟨bs, computedTail, relatedTail⟩
          exact ⟨b :: bs, by simp [computed, computedTail], List.Forall₂.cons related relatedTail⟩

/-! ## The shared mutual semantic converse -/

/-- The simultaneous key and frame converse induction, conditional on the one-step node-completion
interface.  `nodeComplete` is a genuine lower-level premise; this theorem does not claim an
unconditional whole-frame/key completeness. -/
theorem localizedExtendedShortCircuitRule3_mutual_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (nodeComplete : LocalizedRule3ExtendedShortCircuitNodeComplete input target view) :
    ∀ fuel,
      LocalizedRerootExtendedShortCircuitRule3KeyCompleteAt input target view fuel ∧
        LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view fuel
  | 0 => by
      constructor
      · intro excluded cursor key derived compiledExcluded _equiv
        unfold DeclarativeLocalizedRerootExtendedShortCircuitRule3Key at derived
        rcases derived with ⟨children, childrenDerived, empty, notEdge, keyEq⟩
        have childrenComputed : input.executableLocalizedRerootChildren? cursor = some children :=
          input.executableLocalizedRerootChildren?_complete cursor children childrenDerived
        have observationComputed :
            input.localizedRule3StructuralNodeExec cursor.occurrence = some none :=
          input.localizedRule3StructuralNodeExec_complete cursor.occurrence notEdge
        subst key
        refine ⟨
          ({ constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
             observations := []
             rule3 := [] } : input.LocalizedRerootRecursiveRule3SpatialKey),
          ?_, ?_⟩
        · unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
          simp [childrenComputed, observationComputed, empty,
            localizedRule3SpatialRootObservations, localizedRule3SpatialRootPriorities]
        · exact LocalizedRule3SpatialKeyTopologyEquivalent.refl input _
      · intro cursors frame derived
        unfold DeclarativeLocalizedExtendedShortCircuitRule3Frame at derived
        exact False.elim derived
  | fuel + 1 => by
      have prior := input.localizedExtendedShortCircuitRule3_mutual_complete
        target view nodeComplete fuel
      constructor
      · intro excluded cursor key derived compiledExcluded equiv
        unfold DeclarativeLocalizedRerootExtendedShortCircuitRule3Key at derived
        rcases derived with ⟨children, observation, childrenDerived, nodeDerived, shape⟩
        have childrenComputed : input.executableLocalizedRerootChildren? cursor = some children :=
          input.executableLocalizedRerootChildren?_complete cursor children childrenDerived
        have nodeComputed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
            target cursor.occurrence view
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
            compiledExcluded = some observation :=
          nodeComplete fuel prior.2 cursor.occurrence excluded compiledExcluded
            equiv observation nodeDerived
        rcases shape with terminal | branch
        · rcases terminal with ⟨empty, keyEq⟩
          subst key
          refine ⟨
            ({ constitutional := input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node true
               observations := input.localizedRule3SpatialRootObservations observation
               rule3 := input.localizedRule3SpatialRootPriorities observation } :
              input.LocalizedRerootRecursiveRule3SpatialKey),
            ?_, ?_⟩
          · unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            simp [childrenComputed, nodeComputed, empty]
          · exact LocalizedRule3SpatialKeyTopologyEquivalent.refl input _
        · rcases branch with ⟨childKeys, sorted, nonempty, childDerived, permutation,
            descending, keyEq⟩
          subst key
          have compiledChildren : ∃ compiledChildKeys,
              children.mapM (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                target view fuel compiledExcluded) = some compiledChildKeys ∧
              List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
                childKeys compiledChildKeys :=
            mapM_complete_exists_of_forall₂
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                target view fuel compiledExcluded)
              (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
                target view fuel excluded)
              (LocalizedRule3SpatialKeyTopologyEquivalent input)
              (fun child childKey childKeyDerived =>
                prior.1 excluded child childKey childKeyDerived compiledExcluded equiv)
              children childKeys childDerived
          rcases compiledChildren with ⟨compiledChildKeys, childMapComputed, childRelated⟩
          let compiledSorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildKeys
          refine ⟨
            ({ constitutional := OfficialRuleMajorKey.assemble
                (input.moleculeGraph.officialRuleMajorRootKey
                  cursor.occurrence.1.node false)
                (compiledSorted.map fun child => child.constitutional)
               observations := input.localizedRule3SpatialRootObservations observation ++
                 input.mergeLocalizedRerootRule3ObservationChildren compiledSorted
               rule3 := input.localizedRule3SpatialRootPriorities observation ++
                 input.mergeLocalizedRerootRule3PriorityChildren compiledSorted } :
              input.LocalizedRerootRecursiveRule3SpatialKey),
            ?_, ?_⟩
          · unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            simp [childrenComputed, nodeComputed, childMapComputed, nonempty, compiledSorted]
          · exact input.assembledParent_topologyEquivalent_of_forall₂_of_perm_of_descending_node
              (cursor.occurrence.1.node) observation childKeys compiledChildKeys sorted
              childRelated permutation descending
      · intro cursors frame derived
        unfold DeclarativeLocalizedExtendedShortCircuitRule3Frame at derived
        rcases derived with ⟨rawDerived, topology, topologyDerived, policyDerived, keysDerived⟩
        have rawKeysComplete : ∃ compiledRawKeys,
            cursors.mapM (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel []) = some compiledRawKeys ∧
            List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
              frame.rawKeys compiledRawKeys :=
          mapM_complete_exists_of_forall₂
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view fuel [])
            (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key target view fuel [])
            (LocalizedRule3SpatialKeyTopologyEquivalent input)
            (fun cursor key keyDerived =>
              prior.1 [] cursor key keyDerived []
                (input.localizedRule3ExclusionEquivalent_refl []))
            cursors frame.rawKeys rawDerived
        rcases rawKeysComplete with ⟨compiledRawKeys, rawComputed, rawRelated⟩
        have topologyDerivedExec :
            input.localizedRule3CoupledTopologyResolutionExec? frame.rawKeys = some topology :=
          (input.localizedRule3CoupledTopologyResolutionExec?_complete_iff
            frame.rawKeys topology).mpr topologyDerived
        have topologyComputed :
            input.localizedRule3CoupledTopologyResolutionExec? compiledRawKeys = some topology :=
          (input.localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂
            frame.rawKeys compiledRawKeys rawRelated).symm.trans topologyDerivedExec
        have policyDetermined :=
          input.DeclarativeLocalizedRule3CoupledFramePolicy_determines
            frame.rawKeys topology frame.coupled frame.excluded policyDerived
        have excludedMembership : ∀ unit : input.LocalizedRule3PhysicalUnitId,
            unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits frame.rawKeys topology ↔
              unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits compiledRawKeys topology :=
          fun unit => input.mem_localizedRule3CoupledExcludedPhysicalUnits_congruence
            frame.rawKeys compiledRawKeys rawRelated topology topology
            topologyDerivedExec topologyComputed unit
        have compiledExcludedEquivalent :
            LocalizedRule3ExclusionEquivalent input frame.excluded
              (input.localizedRule3CoupledExcludedPhysicalUnits compiledRawKeys topology) := by
          intro unit
          rw [policyDetermined.2]
          exact excludedMembership unit
        have keysComplete : ∃ compiledKeys,
            cursors.mapM (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel
              (input.localizedRule3CoupledExcludedPhysicalUnits compiledRawKeys topology)) =
              some compiledKeys ∧
            List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
              frame.keys compiledKeys :=
          mapM_complete_exists_of_forall₂
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel
              (input.localizedRule3CoupledExcludedPhysicalUnits compiledRawKeys topology))
            (input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
              target view fuel frame.excluded)
            (LocalizedRule3SpatialKeyTopologyEquivalent input)
            (fun cursor key keyDerived =>
              prior.1 frame.excluded cursor key keyDerived
                (input.localizedRule3CoupledExcludedPhysicalUnits compiledRawKeys topology)
                compiledExcludedEquivalent)
            cursors frame.keys keysDerived
        rcases keysComplete with ⟨compiledKeys, keysComputed, keysRelated⟩
        refine ⟨
          { rawKeys := compiledRawKeys
            coupled := topology.isCoupled
            excluded := input.localizedRule3CoupledExcludedPhysicalUnits compiledRawKeys topology
            keys := compiledKeys },
          ?_, ?_⟩
        · unfold buildLocalizedExtendedShortCircuitRule3FrameExec?
          simp [rawComputed, topologyComputed, keysComputed]
        · exact ⟨rawRelated, keysRelated, policyDetermined.1.symm,
            fun unit => by rw [policyDetermined.2]; exact excludedMembership unit⟩

/-! ## Public completeness theorems -/

/-- Public key completeness: a derived key has an actual executable key at the same fuel,
topology-equivalent, for every membership-equivalent exclusion list.  Conditional on the
node-completion interface. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (nodeComplete : LocalizedRule3ExtendedShortCircuitNodeComplete input target view)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (derived : input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
      target view fuel excluded cursor key)
    (compiledExcluded : List input.LocalizedRule3PhysicalUnitId)
    (equiv : LocalizedRule3ExclusionEquivalent input excluded compiledExcluded) :
    ∃ compiledKey : input.LocalizedRerootRecursiveRule3SpatialKey,
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
          target view fuel compiledExcluded cursor = some compiledKey ∧
        LocalizedRule3SpatialKeyTopologyEquivalent input key compiledKey :=
  (input.localizedExtendedShortCircuitRule3_mutual_complete target view nodeComplete fuel).1
    excluded cursor key derived compiledExcluded equiv

/-- Public frame completeness: a derived frame has an actual executable frame at the same fuel
carrying the frame invariant.  Conditional on the node-completion interface. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (nodeComplete : LocalizedRule3ExtendedShortCircuitNodeComplete input target view)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (derived : input.DeclarativeLocalizedExtendedShortCircuitRule3Frame
      target view fuel cursors frame) :
    ∃ compiledFrame : input.LocalizedRule3CanonicalKeyFrame,
      input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view fuel cursors = some compiledFrame ∧
        LocalizedRule3ExtendedFrameTopologyEquivalent input frame compiledFrame :=
  (input.localizedExtendedShortCircuitRule3_mutual_complete target view nodeComplete fuel).2
    cursors frame derived

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
