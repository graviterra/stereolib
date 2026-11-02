import TetraStereo.OneCenter.LocalizedObservedCumulativeRule45Key
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.OfficialCanonicalComparisonFrameTransport

set_option autoImplicit false

namespace TetraStereo.OneCenter

















































































namespace CertifiedLocalizedCIPInput

/-! ## Actual structural completeness of the canonical reroot expansion -/






theorem localizedRerootExpansionCompleteWithin_of_budget_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ fuel →
      input.LocalizedRerootExpansionCompleteWithin fuel cursor
  | 0, cursor, valid, covered => by
      change input.localizedRerootChildrenOf cursor = []
      by_contra nonempty
      obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil
        (input.localizedRerootChildrenOf cursor) nonempty
      have derived := input.localizedRerootChildren?_sound cursor
        (input.localizedRerootChildrenOf cursor)
        (input.localizedRerootChildrenOf_spec cursor)
      have decreases := input.localizedRerootChild_budget_lt cursor child
        (input.localizedRerootChildrenOf cursor) valid derived present
      omega
  | fuel + 1, cursor, valid, covered => by
      change ∀ child, child ∈ input.localizedRerootChildrenOf cursor →
        input.LocalizedRerootExpansionCompleteWithin fuel child
      intro child present
      have derived := input.localizedRerootChildren?_sound cursor
        (input.localizedRerootChildrenOf cursor)
        (input.localizedRerootChildrenOf_spec cursor)
      have childValid := input.localizedRerootChild_valid cursor child
        (input.localizedRerootChildrenOf cursor) derived present
      have decreases := input.localizedRerootChild_budget_lt cursor child
        (input.localizedRerootChildrenOf cursor) valid derived present
      exact localizedRerootExpansionCompleteWithin_of_budget_le
        input fuel child childValid (by omega)

/-- **Numeric structural expansion bound.**  Twice the carrier depth is sufficient for the actual
canonical reroot expansion from every path-valid cursor.  This is the structural premise consumed
by the observed cumulative builder; it is proved here, not assumed. -/
theorem localizedRerootExpansionCompleteWithin_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    input.LocalizedRerootExpansionCompleteWithin (2 * (carrierFuel + 1)) cursor :=
  input.localizedRerootExpansionCompleteWithin_of_budget_le
    (2 * (carrierFuel + 1)) cursor valid
    (input.localizedRerootCursorBudget_le_twice cursor)

/-- Structural completeness is monotone in the fuel bound by one step. -/
theorem localizedRerootExpansionCompleteWithin_succ
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootExpansionCompleteWithin fuel cursor →
      input.LocalizedRerootExpansionCompleteWithin (fuel + 1) cursor
  | 0, cursor, complete => by
      change input.localizedRerootChildrenOf cursor = [] at complete
      change ∀ child, child ∈ input.localizedRerootChildrenOf cursor →
        input.LocalizedRerootExpansionCompleteWithin 0 child
      intro child present
      rw [complete] at present
      simp at present
  | fuel + 1, cursor, complete => by
      change ∀ child, child ∈ input.localizedRerootChildrenOf cursor →
        input.LocalizedRerootExpansionCompleteWithin fuel child at complete
      change ∀ child, child ∈ input.localizedRerootChildrenOf cursor →
        input.LocalizedRerootExpansionCompleteWithin (fuel + 1) child
      intro child present
      exact localizedRerootExpansionCompleteWithin_succ input fuel child
        (complete child present)

/-- Structural completeness is monotone in the fuel bound. -/
theorem localizedRerootExpansionCompleteWithin_mono
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {fuel bound : Nat} (le : fuel ≤ bound)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (complete : input.LocalizedRerootExpansionCompleteWithin fuel cursor) :
    input.LocalizedRerootExpansionCompleteWithin bound cursor :=
  Nat.le_induction complete
    (fun previous _ ih =>
      input.localizedRerootExpansionCompleteWithin_succ previous cursor ih)
    bound le

/-! ## Availability of the observed cumulative builder at the proved bound -/

/-- **Generic observed availability at twice the carrier depth.**  For an arbitrary observer and an
arbitrary label reader, a path-valid cursor whose reached nodes are all observed admits a key at the
numeric structural bound.  The expansion-completeness premise is derived from the actual reroot
structure by `localizedRerootExpansionCompleteWithin_at_twice`; only observer definedness on the
reached nodes remains as an explicit hypothesis. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_of_available_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (available : ∀ node,
      node ∈ input.LocalizedRerootReachedNodes (2 * (carrierFuel + 1)) cursor →
      (observe node).isSome = true) :
    ∃ key, input.buildLocalizedObservedCumulativeRule45Key? stage observe read
      (2 * (carrierFuel + 1)) cursor = some key :=
  input.buildLocalizedObservedCumulativeRule45Key?_exists_of_available
    stage observe read (2 * (carrierFuel + 1)) cursor
    (input.localizedRerootExpansionCompleteWithin_at_twice cursor valid)
    available

/-- A pointwise total observer removes the reached-node availability premise entirely. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (total : ∀ node, (observe node).isSome = true) :
    ∃ key, input.buildLocalizedObservedCumulativeRule45Key? stage observe read
      (2 * (carrierFuel + 1)) cursor = some key :=
  input.buildLocalizedObservedCumulativeRule45Key?_exists_of_available_at_twice
    stage observe read cursor valid (fun node _ => total node)

/-- **Legacy total observer.**  The shipped total observation `some ∘ rule1bRootDistance` is
pointwise available by definition, so the observed cumulative builder returns a key at the numeric
structural bound for every path-valid cursor and every label reader. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_legacy_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedObservedCumulativeRule45Key? stage
      (fun node => some node.rule1bRootDistance) read
      (2 * (carrierFuel + 1)) cursor = some key :=
  input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
    stage (fun node => some node.rule1bRootDistance) read cursor valid
    (fun _ => rfl)

/-- **Shipped cumulative builder existence, reconstructed from the observed route.**  Specializing
the observer to `some ∘ rule1bRootDistance` and the reader to the restricted dependency read, the
observed build is exactly the shipped build; hence the shipped builder returns a key at the numeric
structural bound for every path-valid cursor and every view.  The existence is derived from the
observed-builder structural theorem, not assumed. -/
theorem buildLocalizedRerootCumulativeRule45Key?_exists_at_twice_via_observed
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCumulativeRule45Key? stage target view
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨key, computed⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_exists_legacy_at_twice
      stage (fun cursor => input.localizedDependencyLabel target view cursor) cursor valid
  refine ⟨key, ?_⟩
  rw [← input.buildLocalizedObservedCumulativeRule45Key?_eq_legacy stage target view
    (2 * (carrierFuel + 1)) cursor]
  exact computed

/-! ## Necessity of the root observation -/

/-- **Root observation necessity.**  Every successful observed build observes the cursor's own
node: the root Rule-1b scalar is required in both the terminal and the branching case. -/
theorem buildLocalizedObservedCumulativeRule45Key?_root_observation_available
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor =
        some key →
      (observe cursor.occurrence.1.node).isSome = true
  | 0, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none => simp [rootComputed] at computed
            | some constitutional =>
                cases obs : observe cursor.occurrence.1.node with
                | none =>
                    simp [MoleculeGraph.observedRuleMajorRootKey?, obs] at rootComputed
                | some scalar => simp
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none => simp [rootComputed] at computed
            | some constitutional =>
                cases obs : observe cursor.occurrence.1.node with
                | none =>
                    simp [MoleculeGraph.observedRuleMajorRootKey?, obs] at rootComputed
                | some scalar => simp
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedObservedCumulativeRule45Key?
                  stage observe read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                    observe cursor.occurrence.1.node false with
                | none =>
                    simp [childrenComputed, terminal, rootComputed] at computed
                | some constitutional =>
                    cases obs : observe cursor.occurrence.1.node with
                    | none =>
                        simp [MoleculeGraph.observedRuleMajorRootKey?, obs] at rootComputed
                    | some scalar => simp

/-- **Fail-closed boundary.**  If the observer refuses the cursor's root node, no observed build
can succeed at any fuel.  This is the contrapositive of root observation necessity and does not
identify `none` with any chemical fact. -/
theorem buildLocalizedObservedCumulativeRule45Key?_none_of_root_unavailable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (unavailable : (observe cursor.occurrence.1.node).isSome = false) :
    input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor = none := by
  cases computed : input.buildLocalizedObservedCumulativeRule45Key?
      stage observe read fuel cursor with
  | none => rfl
  | some key =>
      have available :=
        input.buildLocalizedObservedCumulativeRule45Key?_root_observation_available
          stage observe read fuel cursor key computed
      rw [unavailable] at available
      simp at available

/-! ## Supported official framed observer

The official observer `observeOfficialAtTarget?` is `Option`-valued and refuses placeholders and
out-of-bound duplicate coordinates.  Its definedness is therefore stated as an *actual profile*
over provenance and history, not assumed globally. -/

/-- Actual-data profile under which the official observer is defined at a node: a real atom, or a
ring/multiple-bond duplicate whose stored rootward coordinate lies within the actual history bound.
Placeholders are outside the profile and force `none`. -/
def OfficialObservationProfile (input : CertifiedLocalizedCIPInput)
    (toRaw : input.Atom → Nat) (node : OfficialCIPNode input.Atom) : Prop :=
  match node.provenance with
  | .realAtom => True
  | .multipleBondDuplicate stored =>
      OfficialCanonicalComparisonFrameTransport.officialDuplicateBound toRaw node stored
  | .ringDuplicate stored =>
      OfficialCanonicalComparisonFrameTransport.officialDuplicateBound toRaw node stored
  | .placeholder _ _ => False

/-- A real atom satisfies the official observation profile. -/
theorem OfficialObservationProfile_of_real
    (input : CertifiedLocalizedCIPInput)
    (toRaw : input.Atom → Nat) (node : OfficialCIPNode input.Atom)
    (real : node.provenance = .realAtom) :
    input.OfficialObservationProfile toRaw node := by
  unfold OfficialObservationProfile
  rw [real]
  trivial

/-- The official observation profile implies pointwise definedness of the actual official
observer.  Each provenance class is destructed; duplicate coordinates use the actual history bound
carried by the profile, and placeholders are excluded. -/
theorem officialObservationProfile_isSome
    (input : CertifiedLocalizedCIPInput)
    (toRaw : input.Atom → Nat) (target node : OfficialCIPNode input.Atom)
    (profile : input.OfficialObservationProfile toRaw node) :
    (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
      toRaw target node).isSome = true := by
  unfold OfficialObservationProfile at profile
  cases provenance : node.provenance with
  | realAtom =>
      simp [OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?,
        OfficialCanonicalComparisonFrameTransport.observeOfficialWith?,
        OfficialCanonicalComparisonFrameTransport.observeOfficialProvenance?, provenance]
  | multipleBondDuplicate stored =>
      simp only [provenance] at profile
      simp only [OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?,
        OfficialCanonicalComparisonFrameTransport.observeOfficialWith?,
        OfficialCanonicalComparisonFrameTransport.observeOfficialProvenance?,
        OfficialCanonicalComparisonFrameTransport.officialDuplicateObservationOfHistory?,
        provenance]
      rw [if_pos profile]
      rfl
  | ringDuplicate stored =>
      simp only [provenance] at profile
      simp only [OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?,
        OfficialCanonicalComparisonFrameTransport.observeOfficialWith?,
        OfficialCanonicalComparisonFrameTransport.observeOfficialProvenance?,
        OfficialCanonicalComparisonFrameTransport.officialDuplicateObservationOfHistory?,
        provenance]
      rw [if_pos profile]
      rfl
  | placeholder kind stored =>
      simp only [provenance] at profile

/-- **Official observer, explicit reached-node availability.**  For an arbitrary actual target node
and atom-code map, the official observer yields a key at the numeric structural bound whenever it is
defined at every reached node. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_of_official_available_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (toRaw : input.Atom → Nat)
    (target : OfficialCIPNode input.Atom)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (available : ∀ node,
      node ∈ input.LocalizedRerootReachedNodes (2 * (carrierFuel + 1)) cursor →
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
        toRaw target node).isSome = true) :
    ∃ key, input.buildLocalizedObservedCumulativeRule45Key? stage
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
      read (2 * (carrierFuel + 1)) cursor = some key :=
  input.buildLocalizedObservedCumulativeRule45Key?_exists_of_available_at_twice
    stage (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
    read cursor valid available

/-- **Official observer, actual provenance/history profile.**  If every reached node satisfies the
actual official observation profile (real atom, or duplicate coordinate within the actual history
bound), the official observer is defined there and the observed build succeeds at the numeric
structural bound.  No observation value is assumed. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_of_official_profile_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (toRaw : input.Atom → Nat)
    (target : OfficialCIPNode input.Atom)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (profile : ∀ node,
      node ∈ input.LocalizedRerootReachedNodes (2 * (carrierFuel + 1)) cursor →
      input.OfficialObservationProfile toRaw node) :
    ∃ key, input.buildLocalizedObservedCumulativeRule45Key? stage
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
      read (2 * (carrierFuel + 1)) cursor = some key :=
  input.buildLocalizedObservedCumulativeRule45Key?_exists_of_official_available_at_twice
    stage toRaw target read cursor valid
    (fun node present =>
      input.officialObservationProfile_isSome toRaw target node (profile node present))

/-- **Official observer, all-real-atom actual profile.**  The common concrete profile: every
reached node is a real atom.  Availability is then derived, never assumed. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_of_official_real_profile_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (toRaw : input.Atom → Nat)
    (target : OfficialCIPNode input.Atom)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (realProfile : ∀ node,
      node ∈ input.LocalizedRerootReachedNodes (2 * (carrierFuel + 1)) cursor →
      node.provenance = .realAtom) :
    ∃ key, input.buildLocalizedObservedCumulativeRule45Key? stage
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
      read (2 * (carrierFuel + 1)) cursor = some key :=
  input.buildLocalizedObservedCumulativeRule45Key?_exists_of_official_profile_at_twice
    stage toRaw target read cursor valid
    (fun node present =>
      input.OfficialObservationProfile_of_real toRaw node (realProfile node present))

/-- **Refusal at a placeholder root.**  If the cursor's root node is an explicit placeholder, the
actual official observer refuses it and the observed build is `none` at every fuel. -/
theorem buildLocalizedObservedCumulativeRule45Key?_none_of_official_root_placeholder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (toRaw : input.Atom → Nat)
    (target : OfficialCIPNode input.Atom)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (kind : OfficialPhantomNodeKind) (stored : Nat)
    (placeholder : cursor.occurrence.1.node.provenance = .placeholder kind stored) :
    input.buildLocalizedObservedCumulativeRule45Key? stage
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
      read fuel cursor = none := by
  have refusal : OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
      toRaw target cursor.occurrence.1.node = none := by
    unfold OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
    exact OfficialCanonicalComparisonFrameTransport.observeOfficialWith?_placeholder
      toRaw ⟨target.history.map toRaw⟩ cursor.occurrence.1.node kind stored placeholder
  have unavailable : (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
      toRaw target cursor.occurrence.1.node).isSome = false := by
    rw [refusal]
    rfl
  exact input.buildLocalizedObservedCumulativeRule45Key?_none_of_root_unavailable
    stage (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
    read fuel cursor unavailable

/-- **Refusal at an out-of-bound multiple-bond duplicate root.** -/
theorem buildLocalizedObservedCumulativeRule45Key?_none_of_official_root_multipleBond_invalid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (toRaw : input.Atom → Nat)
    (target : OfficialCIPNode input.Atom)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (stored : Nat)
    (provenance : cursor.occurrence.1.node.provenance = .multipleBondDuplicate stored)
    (invalid : ¬ OfficialCanonicalComparisonFrameTransport.officialDuplicateBound toRaw
      cursor.occurrence.1.node stored) :
    input.buildLocalizedObservedCumulativeRule45Key? stage
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
      read fuel cursor = none := by
  have refusal : OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
      toRaw target cursor.occurrence.1.node = none := by
    unfold OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
    exact
      OfficialCanonicalComparisonFrameTransport.observeOfficialWith?_multipleBondDuplicate_refusal
        toRaw ⟨target.history.map toRaw⟩ cursor.occurrence.1.node stored provenance invalid
  have unavailable : (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
      toRaw target cursor.occurrence.1.node).isSome = false := by
    rw [refusal]
    rfl
  exact input.buildLocalizedObservedCumulativeRule45Key?_none_of_root_unavailable
    stage (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
    read fuel cursor unavailable

/-- **Refusal at an out-of-bound ring duplicate root.** -/
theorem buildLocalizedObservedCumulativeRule45Key?_none_of_official_root_ring_invalid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (toRaw : input.Atom → Nat)
    (target : OfficialCIPNode input.Atom)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (stored : Nat)
    (provenance : cursor.occurrence.1.node.provenance = .ringDuplicate stored)
    (invalid : ¬ OfficialCanonicalComparisonFrameTransport.officialDuplicateBound toRaw
      cursor.occurrence.1.node stored) :
    input.buildLocalizedObservedCumulativeRule45Key? stage
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
      read fuel cursor = none := by
  have refusal : OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
      toRaw target cursor.occurrence.1.node = none := by
    unfold OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
    exact
      OfficialCanonicalComparisonFrameTransport.observeOfficialWith?_ringDuplicate_refusal
        toRaw ⟨target.history.map toRaw⟩ cursor.occurrence.1.node stored provenance invalid
  have unavailable : (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?
      toRaw target cursor.occurrence.1.node).isSome = false := by
    rw [refusal]
    rfl
  exact input.buildLocalizedObservedCumulativeRule45Key?_none_of_root_unavailable
    stage (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
    read fuel cursor unavailable

/-! ## Canonical framed observer through the existing transport -/

/-- **Canonical framed observer, transported availability.**  Given actual node correspondence to
canonical branch nodes and canonical observation definedness on the corresponding reached nodes, the
official observer agrees with `CanonicalComparisonFrame.observeNode` by
`observeOfficialAtTarget?_eq_observeNode` and the observed build returns a key at the numeric
structural bound.  The correspondence and the canonical availability are explicit actual data. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_of_canonical_available_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (toRaw : input.Atom → Nat)
    (target : OfficialCIPNode input.Atom)
    (targetCanonical : RawMolecule.CanonicalBranchNode)
    (canonicalOf : OfficialCIPNode input.Atom → RawMolecule.CanonicalBranchNode)
    (targetCorresponds :
      RawLocalizedChildNodeTransport.NodeCorresponds toRaw target targetCanonical)
    (nodeCorresponds : ∀ node,
      RawLocalizedChildNodeTransport.NodeCorresponds toRaw node (canonicalOf node))
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (canonicalAvailable : ∀ node,
      node ∈ input.LocalizedRerootReachedNodes (2 * (carrierFuel + 1)) cursor →
      (CanonicalComparisonFrame.observeNode ⟨targetCanonical.history⟩
        (canonicalOf node)).isSome = true) :
    ∃ key, input.buildLocalizedObservedCumulativeRule45Key? stage
      (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
      read (2 * (carrierFuel + 1)) cursor = some key := by
  apply input.buildLocalizedObservedCumulativeRule45Key?_exists_of_available_at_twice
    stage (OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget? toRaw target)
    read cursor valid
  intro node present
  rw [OfficialCanonicalComparisonFrameTransport.observeOfficialAtTarget?_eq_observeNode
    toRaw targetCorresponds (nodeCorresponds node)]
  exact canonicalAvailable node present

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

Every new scientific export is guarded.  `assert_kernel_only` permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and native/compiler
trust.  The structural theorems legitimately use `Classical.choice` through the canonical child
selection `localizedRerootChildrenOf`. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootExpansionCompleteWithin_of_budget_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootExpansionCompleteWithin_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootExpansionCompleteWithin_succ
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootExpansionCompleteWithin_mono
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_of_available_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_legacy_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_exists_at_twice_via_observed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_root_observation_available
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_none_of_root_unavailable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OfficialObservationProfile
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OfficialObservationProfile_of_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.officialObservationProfile_isSome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_of_official_available_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_of_official_profile_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_of_official_real_profile_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_none_of_official_root_placeholder
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_none_of_official_root_multipleBond_invalid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_none_of_official_root_ring_invalid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_of_canonical_available_at_twice
