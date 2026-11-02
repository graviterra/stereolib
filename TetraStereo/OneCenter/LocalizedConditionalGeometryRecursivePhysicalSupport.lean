import TetraStereo.OneCenter.LocalizedExtendedRecursivePhysicalSupport
import TetraStereo.OneCenter.LocalizedExtendedNodeConditionalGeometry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

































































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Actual-request callback premises from the predecessor frame hypothesis -/

/-- **`isSome` agreement on the actual extended request list.**  The predecessor-frame
correspondence applies to *every* cursor list, so at each actually emitted request it gives the
`isSome` law for the two callbacks.  Neither callback is assumed to succeed. -/
theorem rule3CallbackIsSomeAgreesOn_of_frameCorrespondence
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
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence)
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read1 frameFuel cursors)
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read2 frameFuel cursors) := by
  intro cursors _member
  exact frameOption_isSome_eq input (frameCorrespondence cursors)

/-- **Conditional two-key shape on the actual extended request list.**  A successful callback frame
over an actually emitted request has exactly two rebuilt keys.  The count is the *general*
successful-frame length theorem at exactly the predecessor fuel `frameFuel`, combined with the
selected-request length two.  No success is asserted. -/
theorem rule3CallbackFrameShapeOn_of_frameCorrespondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (frameFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.Rule3CallbackFrameShapeOn
      (input.rule3ExtendedNodeCallbackRequests occurrence)
      (fun cursors =>
        input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read frameFuel cursors) := by
  intro cursors member frame computed
  have length := input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
    target view read frameFuel cursors frame computed
  have requestLength :=
    input.rule3ExtendedNodeCallbackRequests_length_eq_two occurrence cursors member
  rw [length, requestLength]



theorem rule3CallbackPremises_of_frameCorrespondence
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
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.Rule3CallbackIsSomeAgreesOn
        (input.rule3ExtendedNodeCallbackRequests occurrence)
        (fun cursors =>
          input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 frameFuel cursors)
        (fun cursors =>
          input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 frameFuel cursors) ∧
      input.Rule3CallbackFrameShapeOn
        (input.rule3ExtendedNodeCallbackRequests occurrence)
        (fun cursors =>
          input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 frameFuel cursors) ∧
      input.Rule3CallbackFrameShapeOn
        (input.rule3ExtendedNodeCallbackRequests occurrence)
        (fun cursors =>
          input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 frameFuel cursors) :=
  ⟨rule3CallbackIsSomeAgreesOn_of_frameCorrespondence input target view read1 read2 frameFuel
      frameCorrespondence occurrence,
    rule3CallbackFrameShapeOn_of_frameCorrespondence input target view read1 frameFuel occurrence,
    rule3CallbackFrameShapeOn_of_frameCorrespondence input target view read2 frameFuel occurrence⟩

/-! ## The relation bridge -/

/-- **Projected node identity implies optional node correspondence.**  The accepted node
correspondence distinguishes exactly the three `Option (Option _)` shapes: outer refusal, inner
cancellation and a retained observation.  Equality of the projected physical identity decides all
three finite cases: outer refusal only against outer refusal, cancellation only against
cancellation, and a retained observation only against one of the same physical unit identity. -/
theorem nodeOptionPhysicalCorrespondence_of_extendedPhysicalUnit_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (targetOne targetTwo : input.LocalizedCIPOccurrence carrierFuel)
    (viewOne : input.LocalizedDependencyView targetOne)
    (viewTwo : input.LocalizedDependencyView targetTwo)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excludedOne excludedTwo : List input.LocalizedRule3PhysicalUnitId)
    (same :
      input.localizedRule3ExtendedNodePhysicalUnit?
          targetOne occurrence viewOne readOne before excludedOne =
        input.localizedRule3ExtendedNodePhysicalUnit?
          targetTwo occurrence viewTwo readTwo after excludedTwo) :
    LocalizedRule3NodeOptionPhysicalCorrespondence input
      (input.localizedRule3ExtendedShortCircuitNodeWithRead?
        targetOne occurrence viewOne readOne before excludedOne)
      (input.localizedRule3ExtendedShortCircuitNodeWithRead?
        targetTwo occurrence viewTwo readTwo after excludedTwo) := by
  unfold localizedRule3ExtendedNodePhysicalUnit? at same
  exact nodeOptionPhysicalCorrespondence_of_physicalUnit_eq input same







/-- Projected physical-identity equality of the two actual extended nodes, read through the two
actual predecessor frame callbacks, at every occurrence and every membership-equivalent exclusion
pair, **relative to the predecessor frame correspondence**.  The correspondence is a premise, not an
assertion: it is exactly the frame induction hypothesis at the same fuel, and it is what supplies
the request-local callback `isSome` agreement and the conditional two-key shape.  This is the exact
noncircular interface a conditional-geometry node law instantiates. -/
def LocalizedRule3ExtendedNodeConditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) : Prop :=
  ∀ (frameFuel : Nat) (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
    (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      LocalizedRule3FrameOptionPhysicalCorrespondence input
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read1 frameFuel cursors)
        (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
          target view read2 frameFuel cursors)) →
    LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
      input.localizedRule3ExtendedNodePhysicalUnit?
          target occurrence view read1
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read1 frameFuel)
          excluded1 =
        input.localizedRule3ExtendedNodePhysicalUnit?
          target occurrence view read2
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
            target view read2 frameFuel)
          excluded2

/-- **The independent conditional geometry domain yields the conditional node projection.**

At an arbitrary predecessor frame fuel, the frame correspondence supplies both request-local
callback premises for the actual frame callbacks; the route-dispatch integration then produces the
projected node equality for every occurrence and every membership-equivalent exclusion pair.  No
callback success, no topology existence and no existential route support is assumed. -/
theorem conditionalUnitProjection_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel) :
    LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2 := by
  intro frameFuel occurrence excluded1 excluded2 frameCorrespondence equivalence
  obtain ⟨isSomeAgree, beforeShape, afterShape⟩ :=
    rule3CallbackPremises_of_frameCorrespondence input target view read1 read2 frameFuel
      frameCorrespondence occurrence
  exact input.localizedRule3ExtendedNodePhysicalUnit?_eq_of_conditionalGeometry
    target target view view read1 read2
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read1 frameFuel)
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read2 frameFuel)
    occurrence (geometry occurrence) isSomeAgree beforeShape afterShape
    excluded1 excluded2 equivalence

/-- The conditional projection is the node step: convert the projected identity at every
occurrence into the accepted node correspondence, under the predecessor-frame correspondence the
step already carries. -/
theorem nodeStepPhysicalSupport_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2) :
    LocalizedRule3ExtendedNodeStepPhysicalProjection input target view read1 read2 := by
  intro frameFuel frameCorrespondence occurrence excluded1 excluded2 equivalence
  exact nodeOptionPhysicalCorrespondence_of_extendedPhysicalUnit_eq input
    target target view view read1 read2
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read1 frameFuel)
    (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read2 frameFuel)
    occurrence excluded1 excluded2
    (projection frameFuel occurrence excluded1 excluded2 frameCorrespondence equivalence)

/-- **Mutual physical/constitutional correspondence from the conditional node projection.**  At
every fuel, for arbitrary readers, membership-equivalent exclusions and every cursor list, the
actual extended key and frame compilers refuse on one side exactly when they refuse on the other;
successful keys carry equal physical incidence and constitutional observable; successful frames
carry pointwise-corresponding raw and rebuilt keys, the same coupled flag and membership-equivalent
exclusions. -/
theorem localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2) :
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
    (nodeStepPhysicalSupport_of_conditionalUnitProjection input target view read1 read2
      projection)

/-- **Terminal conditional-geometry closure of the recursive physical support.**

Under the independent all-occurrence conditional geometry domain of
`LocalizedExtendedNodeConditionalGeometry`, and for arbitrary direct Rules-4/5 readers, the actual
extended `WithRead` key and frame compilers satisfy, simultaneously at every fuel:

* key refusal synchronization, physical-incidence equality and constitutional-observable equality
  for every cursor under every membership-equivalent exclusion pair;
* frame refusal synchronization, pointwise raw-key and rebuilt-key physical/constitutional
  correspondence, equal `coupled` flags and exclusion membership equivalence for every cursor
  list — hence for both actual frame passes and the actual coupled topology/exclusion computation.

The conditional geometry is consumed directly through the route-dispatch integration; the old
existential `LocalizedRule3ExtendedNodeGeometryDomain` is never constructed, because it is false on
shared structural failures. -/
theorem localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel) :
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
  localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input target view
    read1 read2 (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2
      geometry)

/-! ## Corollaries at the exact accepted relation shapes -/

/-- Refusal synchronization of the actual key compiler under the conditional node projection. -/
theorem keyWithRead_none_iff_none_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
    (fuel : Nat)
    (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded1 excluded2)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read1 fuel excluded1 cursor = none ↔
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read2 fuel excluded2 cursor = none :=
  keyOption_none_iff_none input
    ((localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).1 excluded1 excluded2 equivalence cursor)

/-- A successful actual key determines a successful key on the other side, with the bundled
physical/constitutional correspondence, under the conditional node projection. -/
theorem keyWithRead_some_physical_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
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
    ((localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).1 excluded1 excluded2 equivalence cursor)
    computed

/-- Refusal synchronization of the actual two-pass frame compiler under the conditional node
projection. -/
theorem frameWithRead_none_iff_none_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = none ↔
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = none :=
  frameOption_none_iff_none input
    ((localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).2 cursors)

/-- A successful actual frame determines a successful frame on the other side, with both key-pass
correspondences, the coupled flag and exclusion membership, under the conditional node
projection. -/
theorem frameWithRead_some_physical_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
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
    ((localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).2 cursors) computed

/-! ## Positional raw/rebuilt and exclusion API at the same fuel

The stable downstream surface for the actual localized internal-target descriptor closure: at one
fixed fuel, two successful frames of arbitrary readers carry, positionally,

* the raw-key physical/constitutional relation,
* the rebuilt-key physical/constitutional relation,
* equal `coupled` flags, and
* exclusion membership equivalence.

These are projections of the single frame-pass relation and therefore never require a second
recursion or a fuel shift. -/

/-- Positional raw-key correspondence at one fixed fuel.  The index bound uses the general
successful-frame length theorem at that exact fuel on each side. -/
theorem frameWithRead_rawKeys_get_physical_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
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
    (localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).2 cursors
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

/-- Positional rebuilt-key correspondence at one fixed fuel, including the coupled exclusions. -/
theorem frameWithRead_keys_get_physical_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
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
    (localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).2 cursors
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

/-- The coupled flags of two successful frames at one fixed fuel agree. -/
theorem frameWithRead_coupled_eq_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {leftFrame rightFrame : input.LocalizedRule3CanonicalKeyFrame}
    (leftComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = some leftFrame)
    (rightComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = some rightFrame) :
    leftFrame.coupled = rightFrame.coupled := by
  have frameRelated :=
    (localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).2 cursors
  obtain ⟨rightFrame', rightComputed', frameRelated'⟩ :=
    frameOption_exists_right_of_some input frameRelated leftComputed
  have sameFrame : rightFrame' = rightFrame := by
    rw [rightComputed] at rightComputed'
    exact (Option.some.inj rightComputed').symm
  subst rightFrame'
  exact frameRelated'.2.2.1

/-- The exclusion payloads of two successful frames at one fixed fuel have the same membership.
The lists themselves may differ; only membership is claimed, which is exactly what the node
exclusion policy inspects. -/
theorem frameWithRead_excluded_mem_iff_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {leftFrame rightFrame : input.LocalizedRule3CanonicalKeyFrame}
    (leftComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = some leftFrame)
    (rightComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = some rightFrame) :
    ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ leftFrame.excluded ↔ unit ∈ rightFrame.excluded := by
  have frameRelated :=
    (localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
      target view read1 read2 projection fuel).2 cursors
  obtain ⟨rightFrame', rightComputed', frameRelated'⟩ :=
    frameOption_exists_right_of_some input frameRelated leftComputed
  have sameFrame : rightFrame' = rightFrame := by
    rw [rightComputed] at rightComputed'
    exact (Option.some.inj rightComputed').symm
  subst rightFrame'
  exact frameRelated'.2.2.2

/-! ## Named pass relations -/

/-- The key pass at one fixed fuel: every cursor under every membership-equivalent exclusion pair
is related by the accepted optional key correspondence. -/
def LocalizedRule3ExtendedKeyPassCorrespondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) : Prop :=
  ∀ (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId),
    LocalizedRule3ExclusionEquivalent input excluded1 excluded2 →
      ∀ cursor : input.LocalizedRerootCursor carrierFuel,
        LocalizedRule3KeyOptionPhysicalCorrespondence input
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read1 fuel excluded1 cursor)
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
            target view read2 fuel excluded2 cursor)

/-- The frame pass at one fixed fuel: every cursor list is related by the accepted optional frame
correspondence (both raw and rebuilt positional passes, coupled flag and exclusion membership). -/
def LocalizedRule3ExtendedFramePassCorrespondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) : Prop :=
  ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
    LocalizedRule3FrameOptionPhysicalCorrespondence input
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors)
      (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors)

/-- Both pass relations hold at every fuel under the conditional node projection. -/
theorem keyPass_and_framePass_of_conditionalUnitProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (projection :
      LocalizedRule3ExtendedNodeConditionalUnitProjection input target view read1 read2)
    (fuel : Nat) :
    LocalizedRule3ExtendedKeyPassCorrespondence input target view read1 read2 fuel ∧
      LocalizedRule3ExtendedFramePassCorrespondence input target view read1 read2 fuel :=
  (localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection input
    target view read1 read2 projection fuel)

/-! ## Geometry-parameterized endpoint API

The same endpoint facts, with the predecessor relation hidden: the only premise is the independent
all-occurrence conditional geometry domain.  This is the stable surface for downstream descriptor
closure, which needs the full `Option` relation, both positional key passes and exclusion
membership for arbitrary readers at the same fuel. -/

/-- Key refusal synchronization under the conditional geometry domain. -/
theorem keyWithRead_none_iff_none_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
    (fuel : Nat)
    (excluded1 excluded2 : List input.LocalizedRule3PhysicalUnitId)
    (equivalence : LocalizedRule3ExclusionEquivalent input excluded1 excluded2)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read1 fuel excluded1 cursor = none ↔
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
        target view read2 fuel excluded2 cursor = none :=
  keyWithRead_none_iff_none_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel excluded1 excluded2 equivalence cursor

/-- A successful actual key determines a successful key on the other side with the bundled
physical/constitutional correspondence, under the conditional geometry domain. -/
theorem keyWithRead_some_physical_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
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
  keyWithRead_some_physical_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel excluded1 excluded2 equivalence cursor computed

/-- Frame refusal synchronization under the conditional geometry domain. -/
theorem frameWithRead_none_iff_none_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = none ↔
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = none :=
  frameWithRead_none_iff_none_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel cursors

/-- A successful actual frame determines a successful frame on the other side with both key-pass
correspondences, the coupled flag and exclusion membership, under the conditional geometry
domain. -/
theorem frameWithRead_some_physical_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
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
  frameWithRead_some_physical_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel cursors computed

/-- Positional raw-key correspondence under the conditional geometry domain. -/
theorem frameWithRead_rawKeys_get_physical_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
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
        exact inRange⟩) :=
  frameWithRead_rawKeys_get_physical_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel cursors leftComputed rightComputed index inRange

/-- Positional rebuilt-key correspondence under the conditional geometry domain. -/
theorem frameWithRead_keys_get_physical_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
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
        exact inRange⟩) :=
  frameWithRead_keys_get_physical_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel cursors leftComputed rightComputed index inRange

/-- The coupled flags of two successful frames agree under the conditional geometry domain. -/
theorem frameWithRead_coupled_eq_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {leftFrame rightFrame : input.LocalizedRule3CanonicalKeyFrame}
    (leftComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = some leftFrame)
    (rightComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = some rightFrame) :
    leftFrame.coupled = rightFrame.coupled :=
  frameWithRead_coupled_eq_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel cursors leftComputed rightComputed

/-- Exclusion membership equivalence of two successful frames under the conditional geometry
domain. -/
theorem frameWithRead_excluded_mem_iff_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
    (fuel : Nat)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {leftFrame rightFrame : input.LocalizedRule3CanonicalKeyFrame}
    (leftComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read1 fuel cursors = some leftFrame)
    (rightComputed :
      input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
        target view read2 fuel cursors = some rightFrame) :
    ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ leftFrame.excluded ↔ unit ∈ rightFrame.excluded :=
  frameWithRead_excluded_mem_iff_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel cursors leftComputed rightComputed

/-- Both named pass relations at every fuel under the conditional geometry domain. -/
theorem keyPass_and_framePass_of_conditionalGeometry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll carrierFuel)
    (fuel : Nat) :
    LocalizedRule3ExtendedKeyPassCorrespondence input target view read1 read2 fuel ∧
      LocalizedRule3ExtendedFramePassCorrespondence input target view read1 read2 fuel :=
  keyPass_and_framePass_of_conditionalUnitProjection input target view read1 read2
    (conditionalUnitProjection_of_conditionalGeometry input target view read1 read2 geometry)
    fuel

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3CallbackIsSomeAgreesOn_of_frameCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3CallbackFrameShapeOn_of_frameCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3CallbackPremises_of_frameCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.nodeOptionPhysicalCorrespondence_of_extendedPhysicalUnit_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedNodeConditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.conditionalUnitProjection_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.nodeStepPhysicalSupport_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedWithRead_mutualPhysicalSupport_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyWithRead_none_iff_none_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyWithRead_some_physical_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_none_iff_none_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_some_physical_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_rawKeys_get_physical_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_keys_get_physical_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_coupled_eq_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_excluded_mem_iff_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedKeyPassCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedFramePassCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyPass_and_framePass_of_conditionalUnitProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyWithRead_none_iff_none_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyWithRead_some_physical_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_none_iff_none_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_some_physical_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_rawKeys_get_physical_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_keys_get_physical_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_coupled_eq_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameWithRead_excluded_mem_iff_of_conditionalGeometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.keyPass_and_framePass_of_conditionalGeometry
