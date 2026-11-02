import TetraStereo.OneCenter.LocalizedParametricRule3ConstitutionalProjection
import TetraStereo.OneCenter.LocalizedRule3PhysicalIncidence
import TetraStereo.OneCenter.LocalizedRule3CoupledTopologyExecutable
import TetraStereo.OneCenter.LocalizedRule3PhysicalTopologyCongruence
import TetraStereo.OneCenter.LocalizedRule3ExclusionExtensionality
import TetraStereo.OneCenter.LocalizedRule3NodeCallbackDemand
import TetraStereo.OneCenter.LocalizedExtendedActualRequestLocality
import TetraStereo.OneCenter.LocalizedExtendedNodePhysicalProjection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false








































































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Physical/constitutional correspondence and its `Option` liftings -/

/-- Bundled correspondence of two recursively ranked spatial keys: the same physical-unit incidence,
as required by assembled-parent transport, together with equal constitutional observables.  The
second component is exactly what the coupled-topology search inspects; it carries no priority,
provenance or E/Z information. -/
abbrev LocalizedRule3KeyPhysicalConstitutionalCorrespondence
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  input.LocalizedRule3PhysicalIncidenceEquivalent left right ∧
    constitutionalObservable left.constitutional =
      constitutionalObservable right.constitutional

namespace LocalizedRule3KeyPhysicalConstitutionalCorrespondence

/-- The bundled correspondence is reflexive. -/
theorem refl
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    LocalizedRule3KeyPhysicalConstitutionalCorrespondence input key key :=
  ⟨LocalizedRule3PhysicalIncidenceEquivalent.refl input key, rfl⟩

/-- The bundled correspondence is symmetric. -/
theorem symm
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3KeyPhysicalConstitutionalCorrespondence input left right) :
    LocalizedRule3KeyPhysicalConstitutionalCorrespondence input right left :=
  ⟨LocalizedRule3PhysicalIncidenceEquivalent.symm input related.1,
    related.2.symm⟩

/-- The physical-incidence component. -/
theorem physical
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3KeyPhysicalConstitutionalCorrespondence input left right) :
    input.LocalizedRule3PhysicalIncidenceEquivalent left right :=
  related.1

/-- The constitutional-observable component. -/
theorem observable
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3KeyPhysicalConstitutionalCorrespondence input left right) :
    constitutionalObservable left.constitutional =
      constitutionalObservable right.constitutional :=
  related.2

end LocalizedRule3KeyPhysicalConstitutionalCorrespondence

/-- `Option` lifting of the bundled key correspondence.  Structural absence is related only to
structural absence; two retained keys are related by the bundled correspondence.  This is the exact
relation established by the mutual key induction, including refusal synchronization. -/
abbrev LocalizedRule3KeyOptionPhysicalCorrespondence
    (input : CertifiedLocalizedCIPInput) :
    Option input.LocalizedRerootRecursiveRule3SpatialKey →
      Option input.LocalizedRerootRecursiveRule3SpatialKey → Prop
  | none, none => True
  | some left, some right =>
      LocalizedRule3KeyPhysicalConstitutionalCorrespondence input left right
  | _, _ => False

/-- `Option` lifting over a whole list, used for both `mapM` key passes of the frame. -/
abbrev LocalizedRule3KeyListOptionPhysicalCorrespondence
    (input : CertifiedLocalizedCIPInput) :
    Option (List input.LocalizedRerootRecursiveRule3SpatialKey) →
      Option (List input.LocalizedRerootRecursiveRule3SpatialKey) → Prop
  | none, none => True
  | some left, some right =>
      List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input) left right
  | _, _ => False

/-- Unpack the list relation at a successful pair of `mapM` results. -/
theorem keyListOption_some_some_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related :
      LocalizedRule3KeyListOptionPhysicalCorrespondence input (some left) (some right)) :
    List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
      left right :=
  related

/-- Pack the list relation at a successful pair of `mapM` results. -/
theorem keyListOption_some_some_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related :
      List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
        left right) :
    LocalizedRule3KeyListOptionPhysicalCorrespondence input (some left) (some right) :=
  related

/-- The node projection relation: outer refusal only with outer refusal, inner absence only with
inner absence, and a retained observation only with a retained observation carrying the same physical
unit identity.  The remaining fields of a retained spatial node result (E/Z geometry, priorities,
reference pair) are deliberately unconstrained. -/
abbrev LocalizedRule3NodeOptionPhysicalCorrespondence
    (input : CertifiedLocalizedCIPInput) :
    Option (Option input.LocalizedRule3SpatialNodeResult) →
      Option (Option input.LocalizedRule3SpatialNodeResult) → Prop
  | none, none => True
  | some none, some none => True
  | some (some left), some (some right) => left.physicalUnitId = right.physicalUnitId
  | _, _ => False

/-- Frame correspondence: pointwise-incident and constitutionally equal raw keys, pointwise-incident
and constitutionally equal rebuilt keys, equal coupled flag, and membership-equivalent exclusion
payloads.  List order is retained positionally; it is the *sorts inside each key* that may differ. -/
abbrev LocalizedRule3FramePhysicalConstitutionalCorrespondence
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
      left.rawKeys right.rawKeys ∧
    List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
      left.keys right.keys ∧
    left.coupled = right.coupled ∧
    (∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ left.excluded ↔ unit ∈ right.excluded)

/-- `Option` lifting of the frame correspondence. -/
abbrev LocalizedRule3FrameOptionPhysicalCorrespondence
    (input : CertifiedLocalizedCIPInput) :
    Option input.LocalizedRule3CanonicalKeyFrame →
      Option input.LocalizedRule3CanonicalKeyFrame → Prop
  | none, none => True
  | some left, some right =>
      LocalizedRule3FramePhysicalConstitutionalCorrespondence input left right
  | _, _ => False

/-- The topology interface relation.  Refusal only with refusal; success on both sides preserves the
coupled/ordinary flag and the membership of the induced exclusion list.  The actual key lists are
carried so that the excluded physical units are those of the actual frame. -/
abbrev LocalizedRule3TopologyResolutionPhysicalSupport
    (input : CertifiedLocalizedCIPInput)
    (leftKeys rightKeys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    Option input.LocalizedRule3CoupledTopologyResolution →
      Option input.LocalizedRule3CoupledTopologyResolution → Prop
  | none, none => True
  | some left, some right =>
      left.isCoupled = right.isCoupled ∧
        (∀ unit : input.LocalizedRule3PhysicalUnitId,
          unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits leftKeys left ↔
            unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits rightKeys right)
  | _, _ => False






/-- Node projection interface for the actual recursive extended node reader.  For every predecessor
frame index, occurrence and membership-equivalent pair of exclusion lists, the two actual node
readers are related by the node projection relation.  This is the sibling
`LocalizedExtendedNodePhysicalProjection` result. -/
def LocalizedRule3ExtendedNodePhysicalProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) : Prop :=
  ∀ (frameFuel : Nat) (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
    LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
      LocalizedRule3NodeOptionPhysicalCorrespondence input
        (input.localizedRule3ExtendedShortCircuitNodeWithRead? target occurrence view read1
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 frameFuel) excluded1)
        (input.localizedRule3ExtendedShortCircuitNodeWithRead? target occurrence view read2
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 frameFuel) excluded2)

/-- **Noncircular node-step interface.**  The node correspondence is required only for the
predecessor frame index, and only under the frame correspondence that the mutual induction has
already established at that same predecessor index.  This is exactly the premise shape the node
projection sibling can discharge from the actual geometry domain: the callback `isSome` agreement
follows from the predecessor-frame correspondence, and the conditional two-key shape follows from the
successful-frame length theorem.  It does not assert any node, callback or frame success. -/
def LocalizedRule3ExtendedNodeStepPhysicalProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) : Prop :=
  ∀ (frameFuel : Nat),
    (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      LocalizedRule3FrameOptionPhysicalCorrespondence input
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read1 frameFuel cursors)
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read2 frameFuel cursors)) →
      ∀ (occurrence : input.LocalizedCIPOccurrence carrierFuel)
        (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
        LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
          LocalizedRule3NodeOptionPhysicalCorrespondence input
            (input.localizedRule3ExtendedShortCircuitNodeWithRead?
              target occurrence view read1
              (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
                target view read1 frameFuel) excluded1)
            (input.localizedRule3ExtendedShortCircuitNodeWithRead?
              target occurrence view read2
              (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
                target view read2 frameFuel) excluded2)

/-- The global node projection interface is stronger than the node-step interface: the step law
simply ignores the predecessor-frame correspondence. -/
theorem nodeStep_of_globalProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2) :
    LocalizedRule3ExtendedNodeStepPhysicalProjection input target view read1 read2 := by
  intro frameFuel _frameCorrespondence occurrence excluded1 excluded2 equivalence
  exact projection frameFuel occurrence excluded1 excluded2 equivalence

/-- Topology interface for the actual executable coupled resolution.  This is the sibling
`LocalizedRule3PhysicalTopologyCongruence` result. -/
def LocalizedRule3CoupledTopologyPhysicalSupport
    (input : CertifiedLocalizedCIPInput) : Prop :=
  ∀ (leftKeys rightKeys : List input.LocalizedRerootRecursiveRule3SpatialKey),
    List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
        leftKeys rightKeys →
      LocalizedRule3TopologyResolutionPhysicalSupport input leftKeys rightKeys
        (input.localizedRule3CoupledTopologyResolutionExec? leftKeys)
        (input.localizedRule3CoupledTopologyResolutionExec? rightKeys)

/-- The bundled correspondence is exactly the sibling topology-congruence relation, with the two
components reordered. -/
theorem forall₂_physicalTopologyCongruent_of_forall₂_correspondence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related :
      List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
        left right) :
    List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right :=
  List.Forall₂.imp (fun leftKey rightKey related => ⟨related.2, related.1⟩) related

/-- The topology interface is *proved* from the sibling executable congruence: the actual coupled
dispatcher returns the same `Option` resolution on pointwise corresponding raw key lists, and the
excluded physical-unit membership agrees.  This instantiates the interface rather than assuming it. -/
theorem coupledTopologyPhysicalSupport
    (input : CertifiedLocalizedCIPInput) :
    LocalizedRule3CoupledTopologyPhysicalSupport input := by
  intro leftKeys rightKeys related
  have congruent :=
    forall₂_physicalTopologyCongruent_of_forall₂_correspondence input
      leftKeys rightKeys related
  have computed :=
    LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂
      input leftKeys rightKeys congruent
  cases leftComputed : input.localizedRule3CoupledTopologyResolutionExec? leftKeys with
  | none =>
      have rightComputed :
          input.localizedRule3CoupledTopologyResolutionExec? rightKeys = none := by
        rw [← computed]
        exact leftComputed
      rw [rightComputed]
      simp [LocalizedRule3TopologyResolutionPhysicalSupport]
  | some leftResolution =>
      have rightComputed :
          input.localizedRule3CoupledTopologyResolutionExec? rightKeys =
            some leftResolution := by
        rw [← computed]
        exact leftComputed
      rw [rightComputed]
      refine ⟨rfl, ?_⟩
      intro unit
      exact
        LocalizedRule3PhysicalTopology.mem_localizedRule3CoupledExcludedPhysicalUnits_congruence
          input leftKeys rightKeys congruent leftResolution leftResolution
          leftComputed rightComputed unit

/-! ## Small transport lemmas -/

/-- Membership in a key's physical-unit projection is membership in the flattened observations. -/
theorem mem_localizedRule3PhysicalUnitIds_flatten_iff
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds key ↔
      ∃ entry, entry ∈ key.observations.flatten ∧
        entry.2.physicalUnitId = unit := by
  rw [input.mem_localizedRule3PhysicalUnitIds_iff]
  simp only [List.mem_flatten]
  constructor
  · rintro ⟨layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨entry, ⟨layer, layerPresent, entryPresent⟩, identity⟩
  · rintro ⟨entry, ⟨layer, layerPresent, entryPresent⟩, identity⟩
    exact ⟨layer, layerPresent, entry, entryPresent, identity⟩

/-- Two keys with the same physical-unit identity in their retained root observation have the same
physical incidence when their observations are exactly the two root-observation layers.  The
constitutional component and the Rule-3 priority stream are irrelevant to incidence and may differ. -/
theorem localizedRule3PhysicalIncidenceEquivalent_rootObservations
    (input : CertifiedLocalizedCIPInput)
    (leftRoot rightRoot : OfficialRuleMajorKey input.Atom)
    (leftPriorities rightPriorities : List (List (OfficialSparseEntry Nat)))
    (leftObservation rightObservation : Option input.LocalizedRule3SpatialNodeResult)
    (related :
      input.LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent
        leftObservation rightObservation) :
    input.LocalizedRule3PhysicalIncidenceEquivalent
      { constitutional := leftRoot
        observations := input.localizedRule3SpatialRootObservations leftObservation
        rule3 := leftPriorities }
      { constitutional := rightRoot
        observations := input.localizedRule3SpatialRootObservations rightObservation
        rule3 := rightPriorities } := by
  intro unit
  rw [input.mem_localizedRule3PhysicalUnitIds_flatten_iff,
    input.mem_localizedRule3PhysicalUnitIds_flatten_iff]
  exact
    input.mem_localizedRule3SpatialRootObservations_physicalUnitId_iff_of_physicalIncidence
      related unit

/-- The node projection relation at a successful outer option is exactly the root-observation
physical-incidence relation of the two inner options. -/
theorem nodeOption_some_some_iff_rootObservation
    (input : CertifiedLocalizedCIPInput)
    (left right : Option input.LocalizedRule3SpatialNodeResult) :
    LocalizedRule3NodeOptionPhysicalCorrespondence input (some left) (some right) ↔
      input.LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent left right := by
  cases left with
  | none =>
      cases right with
      | none =>
          simp [LocalizedRule3NodeOptionPhysicalCorrespondence,
            LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent]
      | some rightResult =>
          simp [LocalizedRule3NodeOptionPhysicalCorrespondence,
            LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent]
  | some leftResult =>
      cases right with
      | none =>
          simp [LocalizedRule3NodeOptionPhysicalCorrespondence,
            LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent]
      | some rightResult =>
          simp [LocalizedRule3NodeOptionPhysicalCorrespondence,
            LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent]

/-- A related pair of optional keys is absent on the left exactly when it is absent on the right. -/
theorem keyOption_none_iff_none
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3KeyOptionPhysicalCorrespondence input left right) :
    left = none ↔ right = none := by
  cases left with
  | none =>
      cases right with
      | none => simp
      | some rightKey =>
          simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at related
  | some leftKey =>
      cases right with
      | none =>
          simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at related
      | some rightKey => simp

/-- A related pair of optional keys has matching `isSome`. -/
theorem keyOption_isSome_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3KeyOptionPhysicalCorrespondence input left right) :
    left.isSome = right.isSome := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightKey =>
          simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at related
  | some leftKey =>
      cases right with
      | none =>
          simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at related
      | some rightKey => rfl

/-- Left inversion of the optional key relation: a successful left key determines the right key and
the bundled correspondence. -/
theorem keyOption_exists_right_of_some
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3KeyOptionPhysicalCorrespondence input left right)
    {leftKey : input.LocalizedRerootRecursiveRule3SpatialKey}
    (computed : left = some leftKey) :
    ∃ rightKey, right = some rightKey ∧
      LocalizedRule3KeyPhysicalConstitutionalCorrespondence input leftKey rightKey := by
  subst computed
  cases right with
  | none =>
      simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at related
  | some rightKey => exact ⟨rightKey, rfl, related⟩

/-- Right inversion of the optional key relation. -/
theorem keyOption_exists_left_of_some
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3KeyOptionPhysicalCorrespondence input left right)
    {rightKey : input.LocalizedRerootRecursiveRule3SpatialKey}
    (computed : right = some rightKey) :
    ∃ leftKey, left = some leftKey ∧
      LocalizedRule3KeyPhysicalConstitutionalCorrespondence input leftKey rightKey := by
  subst computed
  cases left with
  | none =>
      simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at related
  | some leftKey => exact ⟨leftKey, rfl, related⟩

/-- Refusal synchronization of the optional frame relation. -/
theorem frameOption_none_iff_none
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRule3CanonicalKeyFrame}
    (related : LocalizedRule3FrameOptionPhysicalCorrespondence input left right) :
    left = none ↔ right = none := by
  cases left with
  | none =>
      cases right with
      | none => simp
      | some rightFrame =>
          simp [LocalizedRule3FrameOptionPhysicalCorrespondence] at related
  | some leftFrame =>
      cases right with
      | none =>
          simp [LocalizedRule3FrameOptionPhysicalCorrespondence] at related
      | some rightFrame => simp

/-- A related pair of optional frames has matching `isSome`.  This is the form consumed when a
downstream node projection only knows that the two readers agree on the callback frame and needs to
transfer success of that frame from one side to the other. -/
theorem frameOption_isSome_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRule3CanonicalKeyFrame}
    (related : LocalizedRule3FrameOptionPhysicalCorrespondence input left right) :
    left.isSome = right.isSome := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some rightFrame =>
          simp [LocalizedRule3FrameOptionPhysicalCorrespondence] at related
  | some leftFrame =>
      cases right with
      | none =>
          simp [LocalizedRule3FrameOptionPhysicalCorrespondence] at related
      | some rightFrame => rfl

/-- Left inversion of the optional frame relation. -/
theorem frameOption_exists_right_of_some
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRule3CanonicalKeyFrame}
    (related : LocalizedRule3FrameOptionPhysicalCorrespondence input left right)
    {leftFrame : input.LocalizedRule3CanonicalKeyFrame}
    (computed : left = some leftFrame) :
    ∃ rightFrame, right = some rightFrame ∧
      LocalizedRule3FramePhysicalConstitutionalCorrespondence input leftFrame rightFrame := by
  subst computed
  cases right with
  | none =>
      simp [LocalizedRule3FrameOptionPhysicalCorrespondence] at related
  | some rightFrame => exact ⟨rightFrame, rfl, related⟩

/-- Right inversion of the optional frame relation. -/
theorem frameOption_exists_left_of_some
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRule3CanonicalKeyFrame}
    (related : LocalizedRule3FrameOptionPhysicalCorrespondence input left right)
    {rightFrame : input.LocalizedRule3CanonicalKeyFrame}
    (computed : right = some rightFrame) :
    ∃ leftFrame, left = some leftFrame ∧
      LocalizedRule3FramePhysicalConstitutionalCorrespondence input leftFrame rightFrame := by
  subst computed
  cases left with
  | none =>
      simp [LocalizedRule3FrameOptionPhysicalCorrespondence] at related
  | some leftFrame => exact ⟨leftFrame, rfl, related⟩

/-! ## Pointwise `mapM` lifting -/

/-- A pointwise related family of optional key computations lifts to a relation on their `mapM`
results over any cursor list.  This is the shared engine of both frame passes. -/
theorem keyListOption_mapM_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootRecursiveRule3SpatialKey)
    (pointwise : ∀ cursor,
      LocalizedRule3KeyOptionPhysicalCorrespondence input (first cursor) (second cursor)) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      LocalizedRule3KeyListOptionPhysicalCorrespondence input
        (cursors.mapM first) (cursors.mapM second)
  | [] => by
      simp [LocalizedRule3KeyListOptionPhysicalCorrespondence]
  | cursor :: cursors => by
      have headRelated := pointwise cursor
      have tailRelated :=
        keyListOption_mapM_physical input first second pointwise cursors
      cases firstComputed : first cursor with
      | none =>
          cases secondComputed : second cursor with
          | none =>
              cases tailFirst : cursors.mapM first with
              | none =>
                  cases tailSecond : cursors.mapM second with
                  | none =>
                      simp [List.mapM_cons, firstComputed, secondComputed,
                        tailFirst, tailSecond,
                        LocalizedRule3KeyListOptionPhysicalCorrespondence]
                  | some tail =>
                      rw [tailFirst] at tailRelated
                      rw [tailSecond] at tailRelated
                      simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at tailRelated
              | some tailFirstKeys =>
                  rw [tailFirst] at tailRelated
                  cases tailSecond : cursors.mapM second with
                  | none =>
                      rw [tailSecond] at tailRelated
                      simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at tailRelated
                  | some tailSecondKeys =>
                      rw [tailSecond] at tailRelated
                      simp [List.mapM_cons, firstComputed, secondComputed,
                        tailFirst, tailSecond,
                        LocalizedRule3KeyListOptionPhysicalCorrespondence]
          | some secondKey =>
              rw [firstComputed, secondComputed] at headRelated
              simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at headRelated
      | some firstKey =>
          cases secondComputed : second cursor with
          | none =>
              rw [firstComputed, secondComputed] at headRelated
              simp [LocalizedRule3KeyOptionPhysicalCorrespondence] at headRelated
          | some secondKey =>
              rw [firstComputed, secondComputed] at headRelated
              cases tailFirst : cursors.mapM first with
              | none =>
                  rw [tailFirst] at tailRelated
                  cases tailSecond : cursors.mapM second with
                  | none =>
                      simp [List.mapM_cons, firstComputed, secondComputed,
                        tailFirst, tailSecond,
                        LocalizedRule3KeyListOptionPhysicalCorrespondence]
                  | some tailSecondKeys =>
                      rw [tailSecond] at tailRelated
                      simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at tailRelated
              | some tailFirstKeys =>
                  rw [tailFirst] at tailRelated
                  cases tailSecond : cursors.mapM second with
                  | none =>
                      rw [tailSecond] at tailRelated
                      simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at tailRelated
                  | some tailSecondKeys =>
                      rw [tailSecond] at tailRelated
                      simp only [List.mapM_cons, firstComputed, secondComputed,
                        tailFirst, tailSecond]
                      exact List.Forall₂.cons
                        (show LocalizedRule3KeyPhysicalConstitutionalCorrespondence
                            input firstKey secondKey from headRelated)
                        (keyListOption_some_some_forall₂ input
                          tailFirstKeys tailSecondKeys tailRelated)

/-! ## The single key step -/

/-- One successor step of the key induction.  The node projection interface is consumed at the
actual predecessor frame and the actual exclusion lists; the recursive child pass is consumed at the
predecessor fuel.  No success or priority agreement is assumed. -/
theorem keyWithRead_succ_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat)
    (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (nodeCorr : LocalizedRule3NodeOptionPhysicalCorrespondence input
      (input.localizedRule3ExtendedShortCircuitNodeWithRead? target cursor.occurrence view read1
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read1 fuel) excluded1)
      (input.localizedRule3ExtendedShortCircuitNodeWithRead? target cursor.occurrence view read2
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read2 fuel) excluded2))
    (childCorr : ∀ child : input.LocalizedRerootCursor carrierFuel,
      LocalizedRule3KeyOptionPhysicalCorrespondence input
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target view read1 fuel excluded1 child)
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target view read2 fuel excluded2 child)) :
    LocalizedRule3KeyOptionPhysicalCorrespondence input
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read1 (fuel + 1) excluded1 cursor)
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read2 (fuel + 1) excluded2 cursor) := by
  unfold buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
  cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
  | none =>
      simp [childrenComputed, LocalizedRule3KeyOptionPhysicalCorrespondence]
  | some children =>
      cases node1 : input.localizedRule3ExtendedShortCircuitNodeWithRead?
          target cursor.occurrence view read1
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 fuel) excluded1 with
      | none =>
          cases node2 : input.localizedRule3ExtendedShortCircuitNodeWithRead?
              target cursor.occurrence view read2
              (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
                target view read2 fuel) excluded2 with
          | none =>
              simp [childrenComputed, node1, node2,
                LocalizedRule3KeyOptionPhysicalCorrespondence]
          | some observation2 =>
              rw [node1, node2] at nodeCorr
              simp [LocalizedRule3NodeOptionPhysicalCorrespondence] at nodeCorr
      | some observation1 =>
          cases node2 : input.localizedRule3ExtendedShortCircuitNodeWithRead?
              target cursor.occurrence view read2
              (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
                target view read2 fuel) excluded2 with
          | none =>
              rw [node1, node2] at nodeCorr
              simp [LocalizedRule3NodeOptionPhysicalCorrespondence] at nodeCorr
          | some observation2 =>
              rw [node1, node2] at nodeCorr
              have rootRelated :
                  input.LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent
                    observation1 observation2 :=
                (nodeOption_some_some_iff_rootObservation input
                  observation1 observation2).mp nodeCorr
              by_cases terminal : children = []
              · simp [childrenComputed, node1, node2, terminal,
                  LocalizedRule3KeyOptionPhysicalCorrespondence]
                exact ⟨
                  input.localizedRule3PhysicalIncidenceEquivalent_rootObservations
                    (input.moleculeGraph.officialRuleMajorRootKey
                      cursor.occurrence.1.node true)
                    (input.moleculeGraph.officialRuleMajorRootKey
                      cursor.occurrence.1.node true)
                    (input.localizedRule3SpatialRootPriorities observation1)
                    (input.localizedRule3SpatialRootPriorities observation2)
                    observation1 observation2 rootRelated,
                  rfl⟩
              · simp [childrenComputed, node1, node2, terminal,
                  LocalizedRule3KeyOptionPhysicalCorrespondence]
                cases childKeys1Computed : children.mapM
                    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                      target view read1 fuel excluded1) with
                | none =>
                    have listCorr := keyListOption_mapM_physical input
                      (fun child =>
                        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                          target view read1 fuel excluded1 child)
                      (fun child =>
                        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                          target view read2 fuel excluded2 child)
                      childCorr children
                    rw [childKeys1Computed] at listCorr
                    cases childKeys2Computed : children.mapM
                        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                          target view read2 fuel excluded2) with
                    | none =>
                        simp [childrenComputed, node1, node2, terminal,
                          childKeys1Computed, childKeys2Computed,
                          LocalizedRule3KeyOptionPhysicalCorrespondence]
                    | some childKeys2 =>
                        rw [childKeys2Computed] at listCorr
                        simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at listCorr
                | some childKeys1 =>
                    have listCorr := keyListOption_mapM_physical input
                      (fun child =>
                        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                          target view read1 fuel excluded1 child)
                      (fun child =>
                        input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                          target view read2 fuel excluded2 child)
                      childCorr children
                    rw [childKeys1Computed] at listCorr
                    cases childKeys2Computed : children.mapM
                        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                          target view read2 fuel excluded2) with
                    | none =>
                        rw [childKeys2Computed] at listCorr
                        simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at listCorr
                    | some childKeys2 =>
                        rw [childKeys2Computed] at listCorr
                        simp [childrenComputed, node1, node2, terminal,
                          childKeys1Computed, childKeys2Computed,
                          LocalizedRule3KeyOptionPhysicalCorrespondence]
                        refine ⟨
                          (fun unit =>
                            input.assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_perm_node
                              cursor.occurrence.1.node observation1 observation2
                              rootRelated childKeys1 childKeys2
                              (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                childKeys1)
                              (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                childKeys2)
                              (List.Forall₂.imp
                                (fun left right related => related.1) listCorr)
                              (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                                childKeys1)
                              (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                                childKeys2)
                              unit),
                          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_observable_eq
                            target view read1 read2 (fuel + 1) (fuel + 1)
                            excluded1 excluded2 cursor
                            { constitutional :=
                                OfficialRuleMajorKey.assemble
                                  (input.moleculeGraph.officialRuleMajorRootKey
                                    cursor.occurrence.1.node false)
                                  ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                      childKeys1).map
                                    fun child => child.constitutional)
                              observations :=
                                input.localizedRule3SpatialRootObservations observation1 ++
                                  input.mergeLocalizedRerootRule3ObservationChildren
                                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                      childKeys1)
                              rule3 :=
                                input.localizedRule3SpatialRootPriorities observation1 ++
                                  input.mergeLocalizedRerootRule3PriorityChildren
                                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                      childKeys1) }
                            { constitutional :=
                                OfficialRuleMajorKey.assemble
                                  (input.moleculeGraph.officialRuleMajorRootKey
                                    cursor.occurrence.1.node false)
                                  ((input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                      childKeys2).map
                                    fun child => child.constitutional)
                              observations :=
                                input.localizedRule3SpatialRootObservations observation2 ++
                                  input.mergeLocalizedRerootRule3ObservationChildren
                                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                      childKeys2)
                              rule3 :=
                                input.localizedRule3SpatialRootPriorities observation2 ++
                                  input.mergeLocalizedRerootRule3PriorityChildren
                                    (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                                      childKeys2) }
                            (by
                              unfold buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                              simp [childrenComputed, node1, node2, terminal,
                                childKeys1Computed])
                            (by
                              unfold buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                              simp [childrenComputed, node1, node2, terminal,
                                childKeys2Computed]))⟩

/-! ## The frame step -/

/-- One successor step of the frame induction.  Both actual passes are present: the raw pass under
the empty exclusion list and the rebuilt pass under the two independently computed coupled
exclusions.  The raw pass yields the pointwise key relation that feeds the topology interface; the
topology outcome then supplies the membership equivalence needed to run the rebuilt pass. -/
theorem frameWithRead_succ_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (topologySupport : LocalizedRule3CoupledTopologyPhysicalSupport input)
    (rawCorr : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      LocalizedRule3KeyOptionPhysicalCorrespondence input
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target view read1 fuel [] cursor)
        (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target view read2 fuel [] cursor))
    (rebuildCorr : ∀ excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId,
      LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
        ∀ cursor : input.LocalizedRerootCursor carrierFuel,
          LocalizedRule3KeyOptionPhysicalCorrespondence input
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
              target view read1 fuel excluded1 cursor)
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
              target view read2 fuel excluded2 cursor)) :
    LocalizedRule3FrameOptionPhysicalCorrespondence input
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 (fuel + 1) cursors)
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 (fuel + 1) cursors) := by
  unfold buildLocalizedExtendedShortCircuitRule3FrameWithRead?
  have rawListCorr := keyListOption_mapM_physical input
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view read1 fuel [])
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view read2 fuel [])
    rawCorr cursors
  cases rawComputed1 : cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read1 fuel []) with
  | none =>
      rw [rawComputed1] at rawListCorr
      cases rawComputed2 : cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read2 fuel []) with
      | none =>
          simp [rawComputed1, rawComputed2,
            LocalizedRule3FrameOptionPhysicalCorrespondence]
      | some rawKeys2 =>
          rw [rawComputed2] at rawListCorr
          simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at rawListCorr
  | some rawKeys1 =>
      rw [rawComputed1] at rawListCorr
      cases rawComputed2 : cursors.mapM
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read2 fuel []) with
      | none =>
          rw [rawComputed2] at rawListCorr
          simp [LocalizedRule3KeyListOptionPhysicalCorrespondence] at rawListCorr
      | some rawKeys2 =>
          rw [rawComputed2] at rawListCorr
          have rawRelated :
              List.Forall₂ (LocalizedRule3KeyPhysicalConstitutionalCorrespondence input)
                rawKeys1 rawKeys2 :=
            keyListOption_some_some_forall₂ input rawKeys1 rawKeys2 rawListCorr
          have topologyCorr := topologySupport rawKeys1 rawKeys2 rawRelated
          cases topologyComputed1 :
              input.localizedRule3CoupledTopologyResolutionExec? rawKeys1 with
          | none =>
              cases topologyComputed2 :
                  input.localizedRule3CoupledTopologyResolutionExec? rawKeys2 with
              | none =>
                  simp [rawComputed1, rawComputed2,
                    topologyComputed1, topologyComputed2,
                    LocalizedRule3FrameOptionPhysicalCorrespondence]
              | some topology2 =>
                  rw [topologyComputed1, topologyComputed2] at topologyCorr
                  simp [LocalizedRule3TopologyResolutionPhysicalSupport] at topologyCorr
          | some topology1 =>
              cases topologyComputed2 :
                  input.localizedRule3CoupledTopologyResolutionExec? rawKeys2 with
              | none =>
                  rw [topologyComputed1, topologyComputed2] at topologyCorr
                  simp [LocalizedRule3TopologyResolutionPhysicalSupport] at topologyCorr
              | some topology2 =>
                  rw [topologyComputed1, topologyComputed2] at topologyCorr
                  obtain ⟨coupledEq, excludedIff⟩ := topologyCorr
                  have rebuiltListCorr := keyListOption_mapM_physical input
                    (fun cursor =>
                      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                        target view read1 fuel
                        (input.localizedRule3CoupledExcludedPhysicalUnits
                          rawKeys1 topology1) cursor)
                    (fun cursor =>
                      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                        target view read2 fuel
                        (input.localizedRule3CoupledExcludedPhysicalUnits
                          rawKeys2 topology2) cursor)
                    (rebuildCorr
                      (input.localizedRule3CoupledExcludedPhysicalUnits
                        rawKeys1 topology1)
                      (input.localizedRule3CoupledExcludedPhysicalUnits
                        rawKeys2 topology2)
                      excludedIff)
                    cursors
                  cases rebuiltComputed1 : cursors.mapM
                      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                        target view read1 fuel
                        (input.localizedRule3CoupledExcludedPhysicalUnits
                          rawKeys1 topology1)) with
                  | none =>
                      rw [rebuiltComputed1] at rebuiltListCorr
                      cases rebuiltComputed2 : cursors.mapM
                          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                            target view read2 fuel
                            (input.localizedRule3CoupledExcludedPhysicalUnits
                              rawKeys2 topology2)) with
                      | none =>
                          simp [rawComputed1, rawComputed2,
                            topologyComputed1, topologyComputed2,
                            rebuiltComputed1, rebuiltComputed2,
                            LocalizedRule3FrameOptionPhysicalCorrespondence]
                      | some rebuiltKeys2 =>
                          rw [rebuiltComputed2] at rebuiltListCorr
                          simp [LocalizedRule3KeyListOptionPhysicalCorrespondence]
                            at rebuiltListCorr
                  | some rebuiltKeys1 =>
                      rw [rebuiltComputed1] at rebuiltListCorr
                      cases rebuiltComputed2 : cursors.mapM
                          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                            target view read2 fuel
                            (input.localizedRule3CoupledExcludedPhysicalUnits
                              rawKeys2 topology2)) with
                      | none =>
                          rw [rebuiltComputed2] at rebuiltListCorr
                          simp [LocalizedRule3KeyListOptionPhysicalCorrespondence]
                            at rebuiltListCorr
                      | some rebuiltKeys2 =>
                          rw [rebuiltComputed2] at rebuiltListCorr
                          simp [rawComputed1, rawComputed2,
                            topologyComputed1, topologyComputed2,
                            rebuiltComputed1, rebuiltComputed2,
                            LocalizedRule3FrameOptionPhysicalCorrespondence]
                          exact ⟨rawRelated,
                            keyListOption_some_some_forall₂ input
                              rebuiltKeys1 rebuiltKeys2 rebuiltListCorr,
                            coupledEq, excludedIff⟩

/-! ## Mutual fuel induction -/

/-- **Mutual physical-support induction over the actual `WithRead` compiler, driven by the
noncircular node step.**

For two arbitrary direct readers, equal-membership exclusion lists, and every cursor, the actual
extended key compiler refuses on one side exactly when it refuses on the other, and successful keys
have the same physical-unit incidence and the same constitutional observable.  Simultaneously, for
every cursor list, the actual two-pass frame compiler refuses on one side exactly when it refuses on
the other, and successful frames have pointwise-corresponding raw and rebuilt keys, equal coupled
flags, and membership-equivalent exclusions.

At the successor index, the key step consumes the node-step law instantiated with the *predecessor
frame induction hypothesis* `frameInduction`, not with a global node correspondence axiom.  Refusal
synchronization in every branch is derived from that step and the recursive key induction.  No branch
assumes that the node reader, the child map, or the frame succeeds, and no desired key or priority
agreement is assumed. -/
theorem localizedExtendedWithRead_mutualPhysicalSupport_of_nodeStep
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeStep :
      LocalizedRule3ExtendedNodeStepPhysicalProjection input target view read1 read2) :
    ∀ fuel : Nat,
      (∀ (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
        LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
          ∀ cursor : input.LocalizedRerootCursor carrierFuel,
            LocalizedRule3KeyOptionPhysicalCorrespondence input
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read1 fuel excluded1 cursor)
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read2 fuel excluded2 cursor)) ∧
      (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
        LocalizedRule3FrameOptionPhysicalCorrespondence input
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 fuel cursors)
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 fuel cursors)) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro excluded1 excluded2 _equivalence cursor
        have same :
            input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read1 0 excluded1 cursor =
              input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read2 0 excluded2 cursor := by
          simp [buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?]
        rw [same]
        cases computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read2 0 excluded2 cursor with
        | none => simp [LocalizedRule3KeyOptionPhysicalCorrespondence]
        | some key =>
            exact ⟨LocalizedRule3PhysicalIncidenceEquivalent.refl input key, rfl⟩
      · intro cursors
        simp [buildLocalizedExtendedShortCircuitRule3FrameWithRead?,
          LocalizedRule3FrameOptionPhysicalCorrespondence]
  | succ fuel induction =>
      obtain ⟨keyInduction, frameInduction⟩ := induction
      refine ⟨?_, ?_⟩
      · intro excluded1 excluded2 equivalence cursor
        exact keyWithRead_succ_physical input target view read1 read2 fuel
          excluded1 excluded2 cursor
          (nodeStep fuel frameInduction cursor.occurrence excluded1 excluded2 equivalence)
          (fun child => keyInduction excluded1 excluded2 equivalence child)
      · intro cursors
        exact frameWithRead_succ_physical input target view read1 read2 fuel cursors
          (coupledTopologyPhysicalSupport input)
          (fun cursor =>
            keyInduction [] [] (input.localizedRule3ExclusionEquivalent_refl []) cursor)
          (fun excluded1 excluded2 equivalence cursor =>
            keyInduction excluded1 excluded2 equivalence cursor)

/-- The global-projection form of the mutual induction, retained as a helper for consumers that
already hold the stronger unconditional node interface.  It is an immediate corollary of the
IH-driven node-step theorem; the latter is the genuine recursion closure. -/
theorem localizedExtendedWithRead_mutualPhysicalSupport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeProjection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2) :
    ∀ fuel : Nat,
      (∀ (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
        LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
          ∀ cursor : input.LocalizedRerootCursor carrierFuel,
            LocalizedRule3KeyOptionPhysicalCorrespondence input
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read1 fuel excluded1 cursor)
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read2 fuel excluded2 cursor)) ∧
      (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
        LocalizedRule3FrameOptionPhysicalCorrespondence input
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 fuel cursors)
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 fuel cursors)) :=
  localizedExtendedWithRead_mutualPhysicalSupport_of_nodeStep input target view read1 read2
    (nodeStep_of_globalProjection input target view read1 read2 nodeProjection)

/-! ## Key and frame `Option` lifting corollaries -/

/-- Refusal synchronization of the actual key compiler at every fuel, for equal-membership exclusion
lists and an arbitrary cursor. -/
theorem keyWithRead_none_iff_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeProjection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2)
    (fuel : Nat)
    (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded1 excluded2)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read1 fuel excluded1 cursor = none ↔
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read2 fuel excluded2 cursor = none :=
  keyOption_none_iff_none input
    ((localizedExtendedWithRead_mutualPhysicalSupport input target view read1 read2
      nodeProjection fuel).1 excluded1 excluded2 equivalence cursor)

/-- A successful left key determines a successful right key at every fuel, together with physical
incidence and constitutional-observable equality. -/
theorem keyWithRead_some_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeProjection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2)
    (fuel : Nat)
    (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded1 excluded2)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {leftKey : input.LocalizedRerootRecursiveRule3SpatialKey}
    (computed :
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read1 fuel excluded1 cursor = some leftKey) :
    ∃ rightKey : input.LocalizedRerootRecursiveRule3SpatialKey,
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target view read2 fuel excluded2 cursor = some rightKey ∧
        LocalizedRule3KeyPhysicalConstitutionalCorrespondence input leftKey rightKey :=
  keyOption_exists_right_of_some input
    ((localizedExtendedWithRead_mutualPhysicalSupport input target view read1 read2
      nodeProjection fuel).1 excluded1 excluded2 equivalence cursor) computed

/-- Refusal synchronization of the actual two-pass frame compiler at every fuel. -/
theorem frameWithRead_none_iff_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeProjection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = none ↔
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = none :=
  frameOption_none_iff_none input
    ((localizedExtendedWithRead_mutualPhysicalSupport input target view read1 read2
      nodeProjection fuel).2 cursors)

/-- A successful left frame determines a successful right frame at every fuel, together with both
pointwise key relations, the coupled flag and exclusion membership. -/
theorem frameWithRead_some_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeProjection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {leftFrame : input.LocalizedRule3CanonicalKeyFrame}
    (computed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = some leftFrame) :
    ∃ rightFrame : input.LocalizedRule3CanonicalKeyFrame,
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read2 fuel cursors = some rightFrame ∧
        LocalizedRule3FramePhysicalConstitutionalCorrespondence
          input leftFrame rightFrame :=
  frameOption_exists_right_of_some input
    ((localizedExtendedWithRead_mutualPhysicalSupport input target view read1 read2
      nodeProjection fuel).2 cursors) computed

/-! ## Per-index incidence across both actual frame passes -/

/-- At every cursor index, the raw keys of two successful frames have the same physical incidence and
constitutional observable. -/
theorem frameWithRead_rawKeys_get_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeProjection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {leftFrame rightFrame : input.LocalizedRule3CanonicalKeyFrame}
    (leftComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = some leftFrame)
    (rightComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = some rightFrame)
    (index : Nat) (inRange : index < cursors.length) :
    LocalizedRule3KeyPhysicalConstitutionalCorrespondence input
      (leftFrame.rawKeys.get ⟨index, by
        rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
          target view read1 fuel cursors leftFrame leftComputed]
        exact inRange⟩)
      (rightFrame.rawKeys.get ⟨index, by
        rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
          target view read2 fuel cursors rightFrame rightComputed]
        exact inRange⟩) := by
  have frameRelated :=
    (localizedExtendedWithRead_mutualPhysicalSupport input target view read1 read2
      nodeProjection fuel).2 cursors
  obtain ⟨rightFrame', rightComputed', frameRelated'⟩ :=
    frameOption_exists_right_of_some input frameRelated leftComputed
  have sameFrame : rightFrame' = rightFrame := by
    rw [rightComputed] at rightComputed'
    exact (Option.some.inj rightComputed').symm
  subst rightFrame'
  obtain ⟨rawRelated, _keysRelated, _coupledEq, _excludedIff⟩ := frameRelated'
  exact rawRelated.get
    (by
      rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
        target view read1 fuel cursors leftFrame leftComputed]
      exact inRange)
    (by
      rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
        target view read2 fuel cursors rightFrame rightComputed]
      exact inRange)

/-- At every cursor index, the rebuilt keys of two successful frames have the same physical incidence
and constitutional observable.  This is the pass that sees the coupled exclusions. -/
theorem frameWithRead_keys_get_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (nodeProjection :
      LocalizedRule3ExtendedNodePhysicalProjection input target view read1 read2)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {leftFrame rightFrame : input.LocalizedRule3CanonicalKeyFrame}
    (leftComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = some leftFrame)
    (rightComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = some rightFrame)
    (index : Nat) (inRange : index < cursors.length) :
    LocalizedRule3KeyPhysicalConstitutionalCorrespondence input
      (leftFrame.keys.get ⟨index, by
        rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
          target view read1 fuel cursors leftFrame leftComputed]
        exact inRange⟩)
      (rightFrame.keys.get ⟨index, by
        rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
          target view read2 fuel cursors rightFrame rightComputed]
        exact inRange⟩) := by
  have frameRelated :=
    (localizedExtendedWithRead_mutualPhysicalSupport input target view read1 read2
      nodeProjection fuel).2 cursors
  obtain ⟨rightFrame', rightComputed', frameRelated'⟩ :=
    frameOption_exists_right_of_some input frameRelated leftComputed
  have sameFrame : rightFrame' = rightFrame := by
    rw [rightComputed] at rightComputed'
    exact (Option.some.inj rightComputed').symm
  subst rightFrame'
  obtain ⟨_rawRelated, keysRelated, _coupledEq, _excludedIff⟩ := frameRelated'
  exact keysRelated.get
    (by
      rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
        target view read1 fuel cursors leftFrame leftComputed]
      exact inRange)
    (by
      rw [input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
        target view read2 fuel cursors rightFrame rightComputed]
      exact inRange)

/-! ## Selected callback pairs have length two -/

/-- Every request emitted by the endpoint callback demand has exactly two cursors.  The underlying
substituent list is `[first, second]` and the only nonempty answer is `[[firstCursor, secondCursor]]`;
all refusal branches are empty. -/
theorem rule3EndpointCallbackRequests_length_eq_two
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpoint partner : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3EndpointCallbackRequests endpoint partner cursor) :
    request.length = 2 := by
  unfold rule3EndpointCallbackRequests at member
  repeat' split at member
  all_goals simp_all

/-- Every request emitted by the short endpoint callback demand has exactly two cursors. -/
theorem rule3ShortEndpointCallbackRequests_length_eq_two
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpoint partner : input.Atom)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests endpoint partner cursor) :
    request.length = 2 := by
  unfold rule3ShortEndpointCallbackRequests at member
  repeat' split at member
  all_goals simp_all

/-- Every request of the short ordinary spatial callback demand has exactly two cursors. -/
theorem rule3ShortSpatialCallbackRequests_length_eq_two
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortSpatialCallbackRequests occurrence) :
    request.length = 2 := by
  unfold rule3ShortSpatialCallbackRequests at member
  cases topologyComputed :
      input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp [topologyComputed] at member
  | some topology =>
      simp only [topologyComputed] at member
      rw [List.mem_append] at member
      rcases member with member | member
      · exact input.rule3ShortEndpointCallbackRequests_length_eq_two
          topology.left topology.right topology.leftCursor request member
      · exact input.rule3ShortEndpointCallbackRequests_length_eq_two
          topology.right topology.left topology.rightCursor request member

/-- Every request of the short odd callback demand has exactly two cursors. -/
theorem rule3ShortOddCallbackRequests_length_eq_two
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortOddCallbackRequests occurrence) :
    request.length = 2 := by
  unfold rule3ShortOddCallbackRequests at member
  cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [topologyComputed] at member
  | some topology =>
      simp only [topologyComputed] at member
      rw [List.mem_append] at member
      rcases member with member | member
      · exact input.rule3ShortEndpointCallbackRequests_length_eq_two
          topology.initial.left topology.initial.right topology.initial.leftCursor
          request member
      · exact input.rule3ShortEndpointCallbackRequests_length_eq_two
          topology.right topology.rightPartner topology.rightCursor request member

/-- **Every actually selected extended callback pair has length two.**  This covers the full
extended node demand, including the original-node fallback and the odd route: the extended list is
one of the two short lists, and both consist only of endpoint pairs. -/
theorem rule3ExtendedNodeCallbackRequests_length_eq_two
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ExtendedNodeCallbackRequests occurrence) :
    request.length = 2 := by
  rcases input.rule3ExtendedNodeCallbackRequests_mem_short occurrence request member with
    oddMember | spatialMember
  · exact input.rule3ShortOddCallbackRequests_length_eq_two occurrence request oddMember
  · exact input.rule3ShortSpatialCallbackRequests_length_eq_two occurrence request spatialMember

/-! ## Ordinary topology for non-four-key frames -/

/-- A successful frame compiled from a cursor list whose length is not four has `coupled = false`
and exclusion membership exactly the ordinary shared-unit domain of its raw keys.  In particular,
every two-cursor selected callback pair compiles under ordinary topology, even though the general
frame invariant retains the full coupled case. -/
theorem frameWithRead_coupled_eq_false_and_excluded_ordinary_of_length_ne_four
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {frame : input.LocalizedRule3CanonicalKeyFrame}
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read (fuel + 1) cursors = some frame)
    (lengthNe : cursors.length ≠ 4) :
    frame.coupled = false ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        unit ∈ frame.excluded ↔
          unit ∈ input.localizedRule3SharedPhysicalUnits frame.rawKeys) := by
  have computedOriginal := computed
  unfold buildLocalizedExtendedShortCircuitRule3FrameWithRead? at computed
  cases rawComputed : cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read fuel []) with
  | none => simp [rawComputed] at computed
  | some rawKeys =>
      cases topologyComputed :
          input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
      | none => simp [rawComputed, topologyComputed] at computed
      | some topology =>
          let excluded :=
            input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology
          cases keysComputed : cursors.mapM
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read fuel excluded) with
          | none =>
              simp [rawComputed, topologyComputed, excluded, keysComputed] at computed
          | some keys =>
              simp [rawComputed, topologyComputed, excluded, keysComputed] at computed
              subst frame
              have rawLength : rawKeys.length = cursors.length :=
                input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
                  target view read (fuel + 1) cursors _ computedOriginal
              have rawLengthNe : rawKeys.length ≠ 4 := by
                intro four
                exact lengthNe (by rw [← rawLength]; exact four)
              have ordinaryComputed :=
                LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolutionExec?_eq_ordinary_of_length_ne_four
                  input rawKeys rawLengthNe
              have topologyEq : topology =
                  LocalizedRule3CoupledTopologyResolution.ordinary := by
                rw [ordinaryComputed] at topologyComputed
                exact (Option.some.inj topologyComputed).symm
              subst topology
              refine ⟨rfl, ?_⟩
              intro unit
              exact input.mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff
                rawKeys unit

/-- **Selected callback pairs compile as two-key ordinary frames.**  If the cursor list is an
actually selected extended callback request, every successful frame over it has exactly two raw keys
and two rebuilt keys, `coupled = false`, and ordinary shared-unit exclusions.  The coupled branch of
the general frame invariant is therefore only needed for the outer descriptor frame, never for these
callback-selected pairs. -/
theorem frameWithRead_callbackRequest_ordinary
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (requestMember : request ∈ input.rule3ExtendedNodeCallbackRequests occurrence)
    {frame : input.LocalizedRule3CanonicalKeyFrame}
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read (fuel + 1) request = some frame) :
    frame.rawKeys.length = 2 ∧ frame.keys.length = 2 ∧
      frame.coupled = false ∧
        (∀ unit : input.LocalizedRule3PhysicalUnitId,
          unit ∈ frame.excluded ↔
            unit ∈ input.localizedRule3SharedPhysicalUnits frame.rawKeys) := by
  have requestLength :=
    input.rule3ExtendedNodeCallbackRequests_length_eq_two occurrence request requestMember
  have rawLength :=
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
      target view read (fuel + 1) request frame computed
  have keysLength :=
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
      target view read (fuel + 1) request frame computed
  have ordinary :=
    frameWithRead_coupled_eq_false_and_excluded_ordinary_of_length_ne_four
      input target view read fuel request computed (by
        rw [requestLength]
        exact (by decide : (2 : Nat) ≠ 4))
  exact ⟨by rw [rawLength, requestLength],
    by rw [keysLength, requestLength], ordinary.1, ordinary.2⟩

/-- **Conditional callback frame shape.**  For an actually selected extended callback request, every
successful frame over that request has exactly two rebuilt keys.  This is the implication form needed
by a downstream node projection: it quantifies over the frame produced by the real compiler and does
not assume that the callback frame succeeds. -/
theorem frameWithRead_callbackRequest_keys_length_eq_two
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (requestMember : request ∈ input.rule3ExtendedNodeCallbackRequests occurrence)
    {frame : input.LocalizedRule3CanonicalKeyFrame}
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read (fuel + 1) request = some frame) :
    frame.keys.length = 2 :=
  (frameWithRead_callbackRequest_ordinary input target view read fuel occurrence request
    requestMember computed).2.1

/-! ## Discharging the node step from the independent geometry domain -/

/-- **The independent geometric domain of the actual extended Rule-3 node at one occurrence.**  It
quantifies only actual route frames, the four actual candidate pairs, their reference cursors, and
the readiness of the cross pairings.  No reader, callback, callback request membership, solver
answer, priority comparison or success/failure outcome is mentioned. -/
def LocalizedRule3ExtendedNodeGeometryDomain
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Prop :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | some _ =>
      ∃ (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
        (leftFirst leftSecond rightFirst rightSecond : input.Atom)
        (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
          input.LocalizedRerootCursor carrierFuel),
        input.localizedRule3OddCumuleneEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence =
              some topology ∧
          input.localizedRule3ExplicitSubstituents
              topology.initial.left topology.initial.right = [leftFirst, leftSecond] ∧
          input.localizedRule3ExplicitSubstituents
              topology.right topology.rightPartner = [rightFirst, rightSecond] ∧
          input.localizedRule3ReferenceCursorExec?
              topology.initial.leftCursor leftFirst = some leftFirstCursor ∧
          input.localizedRule3ReferenceCursorExec?
              topology.initial.leftCursor leftSecond = some leftSecondCursor ∧
          input.localizedRule3ReferenceCursorExec?
              topology.rightCursor rightFirst = some rightFirstCursor ∧
          input.localizedRule3ReferenceCursorExec?
              topology.rightCursor rightSecond = some rightSecondCursor ∧
          input.LocalizedRule3AxisCandidateGeometryReadiness
              topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
  | none =>
      match input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some _ =>
          ∃ (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
            (leftFirst leftSecond rightFirst rightSecond : input.Atom)
            (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
              input.LocalizedRerootCursor carrierFuel),
            input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence =
                some topology ∧
              input.localizedRule3ExplicitSubstituents
                  topology.left topology.right = [leftFirst, leftSecond] ∧
              input.localizedRule3ExplicitSubstituents
                  topology.right topology.left = [rightFirst, rightSecond] ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.leftCursor leftFirst = some leftFirstCursor ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.leftCursor leftSecond = some leftSecondCursor ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.rightCursor rightFirst = some rightFirstCursor ∧
              input.localizedRule3ReferenceCursorExec?
                  topology.rightCursor rightSecond = some rightSecondCursor ∧
              input.LocalizedRule3AxisCandidateGeometryReadiness
                  topology.left topology.right leftFirst leftSecond rightFirst rightSecond
      | none => True

/-- Equality of the `Option.map (Option.map physicalUnitId)` projections is exactly the optional node
correspondence: an outer refusal can only match an outer refusal, a cancellation only a
cancellation, and a retained observation only one of the same physical identity. -/
theorem nodeOptionPhysicalCorrespondence_of_physicalUnit_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : Option (Option input.LocalizedRule3SpatialNodeResult)}
    (same : Option.map (Option.map LocalizedRule3SpatialNodeResult.physicalUnitId) left =
      Option.map (Option.map LocalizedRule3SpatialNodeResult.physicalUnitId) right) :
    LocalizedRule3NodeOptionPhysicalCorrespondence input left right := by
  cases left with
  | none =>
      cases right with
      | none => trivial
      | some right => simp at same
  | some left =>
      cases right with
      | none => simp at same
      | some right =>
          simp only [Option.map_some, Option.some.injEq] at same
          cases left with
          | none =>
              cases right with
              | none => trivial
              | some rightResult => simp at same
          | some leftResult =>
              cases right with
              | none => simp at same
              | some rightResult =>
                  simpa using same

/-- **Predecessor-frame correspondence yields synchronized pair-frame support at every cursor
pair.**  `isSome` agreement is the `Option` law for corresponding frames; the conditional two-key
shape is the general successful-frame length theorem at the same predecessor index, where the cursor
list `[firstCursor, secondCursor]` has length two.  No callback request membership and no success is
assumed on either side. -/
theorem synchronizedPairFrameSupport_of_frameCorrespondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (frameFuel : Nat)
    (frameCorrespondence : ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      LocalizedRule3FrameOptionPhysicalCorrespondence input
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read1 frameFuel cursors)
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read2 frameFuel cursors))
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel} :
    input.LocalizedRule3SynchronizedPairFrameSupport
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read1 frameFuel)
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read2 frameFuel)
      firstCursor secondCursor := by
  unfold LocalizedRule3SynchronizedPairFrameSupport
  refine ⟨?_, ?_, ?_⟩
  · exact frameOption_isSome_eq input (frameCorrespondence [firstCursor, secondCursor])
  · intro frame computed
    have length := input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
      target view read1 frameFuel [firstCursor, secondCursor] frame computed
    simpa using length
  · intro frame computed
    have length := input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
      target view read2 frameFuel [firstCursor, secondCursor] frame computed
    simpa using length

/-- The independent geometry domain and the predecessor-frame correspondence assemble the exact
route-indexed node support consumed by the sibling physical projection.  The synchronization
components are derived, not assumed. -/
theorem routePhysicalSupport_of_geometryDomain
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (frameFuel : Nat)
    (frameCorrespondence : ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      LocalizedRule3FrameOptionPhysicalCorrespondence input
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read1 frameFuel cursors)
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read2 frameFuel cursors))
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (geometry : LocalizedRule3ExtendedNodeGeometryDomain input occurrence) :
    input.LocalizedRule3ExtendedNodeRoutePhysicalSupport
      target target view view read1 read2
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read1 frameFuel)
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read2 frameFuel)
      occurrence := by
  unfold LocalizedRule3ExtendedNodeGeometryDomain at geometry
  unfold LocalizedRule3ExtendedNodeRoutePhysicalSupport
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      simp only [oddRoute] at geometry ⊢
      obtain ⟨topology, leftFirst, leftSecond, rightFirst, rightSecond,
        leftFirstCursor, leftSecondCursor, rightFirstCursor, rightSecondCursor,
        found, leftCandidates, rightCandidates, leftFirstSelected, leftSecondSelected,
        rightFirstSelected, rightSecondSelected, candidateReady⟩ := geometry
      exact ⟨topology, leftFirst, leftSecond, rightFirst, rightSecond,
        leftFirstCursor, leftSecondCursor, rightFirstCursor, rightSecondCursor,
        found, leftCandidates, rightCandidates, leftFirstSelected, leftSecondSelected,
        rightFirstSelected, rightSecondSelected,
        synchronizedPairFrameSupport_of_frameCorrespondence input target view read1 read2
          frameFuel frameCorrespondence,
        synchronizedPairFrameSupport_of_frameCorrespondence input target view read1 read2
          frameFuel frameCorrespondence,
        candidateReady⟩
  | none =>
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          simp only [oddRoute, ordinaryRoute] at geometry ⊢
          obtain ⟨topology, leftFirst, leftSecond, rightFirst, rightSecond,
            leftFirstCursor, leftSecondCursor, rightFirstCursor, rightSecondCursor,
            found, leftCandidates, rightCandidates, leftFirstSelected, leftSecondSelected,
            rightFirstSelected, rightSecondSelected, candidateReady⟩ := geometry
          exact ⟨topology, leftFirst, leftSecond, rightFirst, rightSecond,
            leftFirstCursor, leftSecondCursor, rightFirstCursor, rightSecondCursor,
            found, leftCandidates, rightCandidates, leftFirstSelected, leftSecondSelected,
            rightFirstSelected, rightSecondSelected,
            synchronizedPairFrameSupport_of_frameCorrespondence input target view read1 read2
              frameFuel frameCorrespondence,
            synchronizedPairFrameSupport_of_frameCorrespondence input target view read1 read2
              frameFuel frameCorrespondence,
            candidateReady⟩
      | none =>
          simp only [oddRoute, ordinaryRoute] at geometry ⊢

/-- **The node-step law is discharged by the actual node physical projection.**  The only input
beyond the predecessor-frame correspondence is the independent geometry domain; callback success is
never assumed, and the projected equality is converted into the optional node correspondence. -/
theorem nodeStepPhysicalSupport_of_geometryDomain
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      LocalizedRule3ExtendedNodeGeometryDomain input occurrence) :
    LocalizedRule3ExtendedNodeStepPhysicalProjection input target view read1 read2 := by
  intro frameFuel frameCorrespondence occurrence excluded1 excluded2 equivalence
  exact nodeOptionPhysicalCorrespondence_of_physicalUnit_eq input
    (input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_routeSupport
      target target view view read1 read2
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 frameFuel)
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 frameFuel)
      occurrence excluded1 excluded2 equivalence
      (routePhysicalSupport_of_geometryDomain input target view read1 read2 frameFuel
        frameCorrespondence occurrence (geometry occurrence)))

/-- **Mutual physical support under the independent geometric domain.**  This is the unconditional
form of the mutual key/frame induction: the only premise besides the actual inputs is the geometry
domain for every actual occurrence, which quantifies actual route frames and the four candidate
pairs.  Both key passes and both frame passes retain refusal synchronization, physical incidence and
constitutional equality across arbitrary direct readers. -/
theorem localizedExtendedWithRead_mutualPhysicalSupport_of_geometryDomain
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : ∀ occurrence : input.LocalizedCIPOccurrence carrierFuel,
      LocalizedRule3ExtendedNodeGeometryDomain input occurrence) :
    ∀ fuel : Nat,
      (∀ (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
        LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
          ∀ cursor : input.LocalizedRerootCursor carrierFuel,
            LocalizedRule3KeyOptionPhysicalCorrespondence input
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read1 fuel excluded1 cursor)
              (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                target view read2 fuel excluded2 cursor)) ∧
      (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
        LocalizedRule3FrameOptionPhysicalCorrespondence input
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 fuel cursors)
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 fuel cursors)) :=
  localizedExtendedWithRead_mutualPhysicalSupport_of_nodeStep input target view read1 read2
    (nodeStepPhysicalSupport_of_geometryDomain input target view read1 read2 geometry)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3KeyPhysicalConstitutionalCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3KeyPhysicalConstitutionalCorrespondence.refl
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3KeyPhysicalConstitutionalCorrespondence.symm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3KeyPhysicalConstitutionalCorrespondence.physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3KeyPhysicalConstitutionalCorrespondence.observable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3KeyOptionPhysicalCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3KeyListOptionPhysicalCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3NodeOptionPhysicalCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3FramePhysicalConstitutionalCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3FrameOptionPhysicalCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3TopologyResolutionPhysicalSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedNodePhysicalProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedNodeStepPhysicalProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.nodeStep_of_globalProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3CoupledTopologyPhysicalSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRule3PhysicalUnitIds_flatten_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3PhysicalIncidenceEquivalent_rootObservations
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.nodeOption_some_some_iff_rootObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyOption_none_iff_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyOption_isSome_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyOption_exists_right_of_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyOption_exists_left_of_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameOption_none_iff_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameOption_isSome_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameOption_exists_right_of_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameOption_exists_left_of_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyListOption_some_some_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyListOption_some_some_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyListOption_mapM_physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyWithRead_succ_physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.forall₂_physicalTopologyCongruent_of_forall₂_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.coupledTopologyPhysicalSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_succ_physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedWithRead_mutualPhysicalSupport_of_nodeStep
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedWithRead_mutualPhysicalSupport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyWithRead_none_iff_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyWithRead_some_physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_none_iff_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_some_physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_rawKeys_get_physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_keys_get_physical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3EndpointCallbackRequests_length_eq_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_length_eq_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortSpatialCallbackRequests_length_eq_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortOddCallbackRequests_length_eq_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ExtendedNodeCallbackRequests_length_eq_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_coupled_eq_false_and_excluded_ordinary_of_length_ne_four
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_callbackRequest_ordinary
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_callbackRequest_keys_length_eq_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedNodeGeometryDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.nodeOptionPhysicalCorrespondence_of_physicalUnit_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.synchronizedPairFrameSupport_of_frameCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.routePhysicalSupport_of_geometryDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.nodeStepPhysicalSupport_of_geometryDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedWithRead_mutualPhysicalSupport_of_geometryDomain
