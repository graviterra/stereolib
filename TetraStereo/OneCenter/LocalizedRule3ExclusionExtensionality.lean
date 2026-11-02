import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode
import TetraStereo.OneCenter.LocalizedDescriptorBearingRule3Executable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Extensionality of the compiled physical-unit exclusion list

Every compiled Rule-3 node reader carries an explicit list of physical unit identities whose
observations must be suppressed.  The list is consulted only through `List.contains`, so the
node interface must depend on the *membership* of that list and not on its order, its
multiplicity or its concrete representation.

This module proves that fact for the whole node interface:

* exact executable equality of the original, short-circuit and extended node readers when two
  exclusion lists contain exactly the same physical units;
* transport in both directions of the independently defined declarative node relations
  (`DeclarativeLocalizedDescriptorBearingRule3NodeWith`,
  `DeclarativeLocalizedRule3ShortCircuitNodeWith`,
  `DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith`) at the same frame meaning and the
  same observation;
* fuel-indexed invariance of the original compiled recursive key and of
  `localizedDescriptorBearingRule3NodeExec?`, which is what a completeness induction comparing a
  compiled and a declarative excluded list needs.

The node result type is `Option (Option …)`: the outer `none` means "no node outcome was
produced", while `some none` is a successful node with no emitted observation, including
structural nonunits, exclusions, and omissions. All statements below preserve that distinction:
no outer and inner option is ever identified.
-/

/-- Two physical-unit exclusion lists are interchangeable when they contain exactly the same
physical units.  Order and multiplicity are deliberately unconstrained. -/
def LocalizedRule3ExclusionEquivalent (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRule3PhysicalUnitId) : Prop :=
  ∀ unit, unit ∈ left ↔ unit ∈ right

theorem localizedRule3ExclusionEquivalent_refl (input : CertifiedLocalizedCIPInput)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    LocalizedRule3ExclusionEquivalent input excluded excluded :=
  fun _ => Iff.rfl

theorem localizedRule3ExclusionEquivalent_symm (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    LocalizedRule3ExclusionEquivalent input right left :=
  fun unit => (equivalent unit).symm

theorem localizedRule3ExclusionEquivalent_trans (input : CertifiedLocalizedCIPInput)
    {first second third : List input.LocalizedRule3PhysicalUnitId}
    (firstSecond : LocalizedRule3ExclusionEquivalent input first second)
    (secondThird : LocalizedRule3ExclusionEquivalent input second third) :
    LocalizedRule3ExclusionEquivalent input first third :=
  fun unit => (firstSecond unit).trans (secondThird unit)

/-- The runtime membership test of two membership-equivalent exclusion lists agrees on every
physical unit.  This is the single fact through which the exclusion list reaches the compiled
node readers. -/
theorem localizedRule3ExclusionEquivalent_contains (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    left.contains unit = right.contains unit := by
  rw [List.contains_eq_mem, List.contains_eq_mem, decide_eq_decide]
  exact equivalent unit

/-! ## Exact executable equality

Both sides of each statement below are the same compiled term except at the physical-unit
membership test, so rewriting that single test in the unfolded term identifies them. -/

/-- The compiled original node reader is insensitive to the order and multiplicity of its
exclusion list; only membership matters. -/
theorem localizedDescriptorBearingRule3NodeWithExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedDescriptorBearingRule3NodeWithExec?
        target occurrence view callback left =
      input.localizedDescriptorBearingRule3NodeWithExec?
        target occurrence view callback right := by
  have containsEq := localizedRule3ExclusionEquivalent_contains input equivalent
  unfold localizedDescriptorBearingRule3NodeWithExec?
  simp only [containsEq]

/-- The original node reader in its transparent classical formulation is insensitive to the
order and multiplicity of its exclusion list. -/
theorem localizedDescriptorBearingRule3NodeWith?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedDescriptorBearingRule3NodeWith?
        target occurrence view callback left =
      input.localizedDescriptorBearingRule3NodeWith?
        target occurrence view callback right := by
  calc
    input.localizedDescriptorBearingRule3NodeWith?
        target occurrence view callback left =
        input.localizedDescriptorBearingRule3NodeWithExec?
          target occurrence view callback left :=
        (input.localizedDescriptorBearingRule3NodeWithExec?_eq_original
          target occurrence view callback left).symm
    _ = input.localizedDescriptorBearingRule3NodeWithExec?
          target occurrence view callback right :=
        localizedDescriptorBearingRule3NodeWithExec?_exclusion_extensional
          input target occurrence view callback equivalent
    _ = input.localizedDescriptorBearingRule3NodeWith?
          target occurrence view callback right :=
        input.localizedDescriptorBearingRule3NodeWithExec?_eq_original
          target occurrence view callback right

/-- The compiled short-circuit node reader is insensitive to the order and multiplicity of its
exclusion list. -/
theorem localizedRule3ShortCircuitNodeWithExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedRule3ShortCircuitNodeWithExec? target occurrence view callback left =
      input.localizedRule3ShortCircuitNodeWithExec? target occurrence view callback right := by
  have containsEq := localizedRule3ExclusionEquivalent_contains input equivalent
  unfold localizedRule3ShortCircuitNodeWithExec? localizedDescriptorBearingRule3NodeWithExec?
  simp only [containsEq]

/-- The compiled extended node reader is insensitive to the order and multiplicity of its
exclusion list. -/
theorem localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view callback left =
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view callback right := by
  have containsEq := localizedRule3ExclusionEquivalent_contains input equivalent
  unfold localizedRule3ExtendedShortCircuitNodeWithExec?
    localizedRule3ShortCircuitNodeWithExec? localizedDescriptorBearingRule3NodeWithExec?
  simp only [containsEq]

/-! ## Transport of the independent declarative node relations

The relations below are defined by their own constructors; none of them defines meaning as
equality with the evaluator.  The only constructor fields that mention the exclusion list are
the membership proofs `observation.physicalUnitId ∈ excluded` and
`observation.physicalUnitId ∉ excluded`, so membership equivalence is exactly what transport
needs.  The frame meaning and the observation are held fixed. -/

/-- Original declarative node derivations transport between membership-equivalent exclusion
lists. -/
theorem declarativeLocalizedDescriptorBearingRule3NodeWith_exclusion_transport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view FrameMeaning left occurrence observation) :
    input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view FrameMeaning right occurrence observation := by
  cases derived with
  | structural notEdge => exact .structural notEdge
  | internalCumulatedAxis edge entry => exact .internalCumulatedAxis edge entry
  | omittedMonocycle edge route omitted => exact .omittedMonocycle edge route omitted
  | excludedCyclicUnit edge cyclic observationEq excludedIdentity =>
      exact .excludedCyclicUnit edge cyclic observationEq
        ((equivalent _).mp excludedIdentity)
  | retainedCyclicGeometry edge cyclic observationEq freshIdentity =>
      exact .retainedCyclicGeometry edge cyclic observationEq
        (fun member => freshIdentity ((equivalent _).mpr member))
  | evenCumulatedAxis edge topology notOrdinary notPlanar =>
      exact .evenCumulatedAxis edge topology notOrdinary notPlanar
  | excludedUnit edge axis topology ordinary spatial observationEq excludedIdentity =>
      exact .excludedUnit edge axis topology ordinary spatial observationEq
        ((equivalent _).mp excludedIdentity)
  | retainedGeometry edge axis topology ordinary spatial observationEq freshIdentity =>
      exact .retainedGeometry edge axis topology ordinary spatial observationEq
        (fun member => freshIdentity ((equivalent _).mpr member))
  | excludedBranchedUnit edge entry spatial observationEq excludedIdentity =>
      exact .excludedBranchedUnit edge entry spatial observationEq
        ((equivalent _).mp excludedIdentity)
  | retainedBranchedGeometry edge entry spatial observationEq freshIdentity =>
      exact .retainedBranchedGeometry edge entry spatial observationEq
        (fun member => freshIdentity ((equivalent _).mpr member))
  | excludedOddCumulene edge odd observationEq excludedIdentity =>
      exact .excludedOddCumulene edge odd observationEq
        ((equivalent _).mp excludedIdentity)
  | retainedOddCumulene edge odd observationEq freshIdentity =>
      exact .retainedOddCumulene edge odd observationEq
        (fun member => freshIdentity ((equivalent _).mpr member))

/-- A declarative original-node derivation exists for one exclusion list if and only if it
exists for a membership-equivalent one, at the same frame meaning and observation. -/
theorem declarativeLocalizedDescriptorBearingRule3NodeWith_exclusion_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    (input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view FrameMeaning left occurrence observation) ↔
      (input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view FrameMeaning right occurrence observation) :=
  ⟨declarativeLocalizedDescriptorBearingRule3NodeWith_exclusion_transport
      input target view FrameMeaning equivalent occurrence,
    declarativeLocalizedDescriptorBearingRule3NodeWith_exclusion_transport
      input target view FrameMeaning
      (localizedRule3ExclusionEquivalent_symm input equivalent) occurrence⟩

/-- Short-circuit declarative node derivations transport between membership-equivalent
exclusion lists. -/
theorem declarativeLocalizedRule3ShortCircuitNodeWith_exclusion_transport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedRule3ShortCircuitNodeWith
      target view FrameMeaning left occurrence observation) :
    input.DeclarativeLocalizedRule3ShortCircuitNodeWith
      target view FrameMeaning right occurrence observation := by
  cases derived with
  | original originalDerived =>
      exact .original
        (declarativeLocalizedDescriptorBearingRule3NodeWith_exclusion_transport
          input target view FrameMeaning equivalent occurrence originalDerived)
  | ordinary route result spatialDerived =>
      have containsEq := localizedRule3ExclusionEquivalent_contains input equivalent
        (input.localizedRule3ShortCircuitSpatialObservation result).physicalUnitId
      rw [containsEq]
      exact .ordinary route result spatialDerived

/-- A declarative short-circuit-node derivation exists for one exclusion list if and only if it
exists for a membership-equivalent one, at the same frame meaning and observation. -/
theorem declarativeLocalizedRule3ShortCircuitNodeWith_exclusion_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    (input.DeclarativeLocalizedRule3ShortCircuitNodeWith
        target view FrameMeaning left occurrence observation) ↔
      (input.DeclarativeLocalizedRule3ShortCircuitNodeWith
        target view FrameMeaning right occurrence observation) :=
  ⟨declarativeLocalizedRule3ShortCircuitNodeWith_exclusion_transport
      input target view FrameMeaning equivalent occurrence,
    declarativeLocalizedRule3ShortCircuitNodeWith_exclusion_transport
      input target view FrameMeaning
      (localizedRule3ExclusionEquivalent_symm input equivalent) occurrence⟩

/-- Extended declarative node derivations transport between membership-equivalent exclusion
lists. -/
theorem declarativeLocalizedRule3ExtendedShortCircuitNodeWith_exclusion_transport
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning fuel)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
      target view FrameMeaning left occurrence observation) :
    input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
      target view FrameMeaning right occurrence observation := by
  cases derived with
  | previous shortDerived =>
      exact .previous
        (declarativeLocalizedRule3ShortCircuitNodeWith_exclusion_transport
          input target view FrameMeaning equivalent occurrence shortDerived)
  | odd route result spatialDerived =>
      have containsEq := localizedRule3ExclusionEquivalent_contains input equivalent
        (input.localizedRule3ShortCircuitOddSpatialObservation result).physicalUnitId
      rw [containsEq]
      exact .odd route result spatialDerived

/-- A declarative extended-node derivation exists for one exclusion list if and only if it
exists for a membership-equivalent one, at the same frame meaning and observation. -/
theorem declarativeLocalizedRule3ExtendedShortCircuitNodeWith_exclusion_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning fuel)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    (input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
        target view FrameMeaning left occurrence observation) ↔
      (input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
        target view FrameMeaning right occurrence observation) :=
  ⟨declarativeLocalizedRule3ExtendedShortCircuitNodeWith_exclusion_transport
      input target view FrameMeaning equivalent occurrence,
    declarativeLocalizedRule3ExtendedShortCircuitNodeWith_exclusion_transport
      input target view FrameMeaning
      (localizedRule3ExclusionEquivalent_symm input equivalent) occurrence⟩

/-- The fuel-indexed declarative node meaning is invariant under membership-equivalent
exclusion lists at the same fuel index and observation.  At index zero the exclusion list is
unused; at a successor this is the constructor-level transport above. -/
theorem declarativeLocalizedDescriptorBearingRule3Node_exclusion_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (observation : Option input.LocalizedRule3SpatialNodeResult) :
    (input.DeclarativeLocalizedDescriptorBearingRule3Node
        target view fuel left occurrence observation) ↔
      (input.DeclarativeLocalizedDescriptorBearingRule3Node
        target view fuel right occurrence observation) := by
  cases fuel with
  | zero =>
      simp only [DeclarativeLocalizedDescriptorBearingRule3Node]
  | succ fuel =>
      exact declarativeLocalizedDescriptorBearingRule3NodeWith_exclusion_iff
        input target view
        (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view fuel)
        equivalent occurrence observation

/-! ## Fuel-indexed compiled invariance

A completeness induction compares the executable compilation with a declarative derivation that
may have been obtained under a differently represented exclusion list.  The compiled recursive
key and the fuel-indexed node reader must therefore be invariant under membership equivalence at
every index. -/

/-- The compiled descriptor-bearing recursive key is invariant under membership-equivalent
exclusion lists at every fuel index. -/
theorem buildLocalizedRerootDescriptorBearingRule3KeyExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) {left right : List input.LocalizedRule3PhysicalUnitId},
      LocalizedRule3ExclusionEquivalent input left right →
        ∀ cursor, input.buildLocalizedRerootDescriptorBearingRule3KeyExec?
            target view fuel left cursor =
          input.buildLocalizedRerootDescriptorBearingRule3KeyExec?
            target view fuel right cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right equivalent cursor
      simp only [buildLocalizedRerootDescriptorBearingRule3KeyExec?]
  | succ fuel inductionHypothesis =>
      intro left right equivalent cursor
      have keysEq : input.buildLocalizedRerootDescriptorBearingRule3KeyExec?
            target view fuel left =
          input.buildLocalizedRerootDescriptorBearingRule3KeyExec? target view fuel right :=
        funext fun child => inductionHypothesis equivalent child
      have nodeEq := localizedDescriptorBearingRule3NodeWithExec?_exclusion_extensional
        input target cursor.occurrence view
        (input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel) equivalent
      simp only [buildLocalizedRerootDescriptorBearingRule3KeyExec?]
      rw [nodeEq, keysEq]

/-- The fuel-indexed node reader is invariant under membership-equivalent exclusion lists at
every fuel index. -/
theorem localizedDescriptorBearingRule3NodeExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) {left right : List input.LocalizedRule3PhysicalUnitId},
      LocalizedRule3ExclusionEquivalent input left right →
        input.localizedDescriptorBearingRule3NodeExec? target occurrence view fuel left =
          input.localizedDescriptorBearingRule3NodeExec? target occurrence view fuel right := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right equivalent
      simp only [localizedDescriptorBearingRule3NodeExec?]
  | succ fuel inductionHypothesis =>
      intro left right equivalent
      simpa only [localizedDescriptorBearingRule3NodeExec?] using
        localizedDescriptorBearingRule3NodeWithExec?_exclusion_extensional
          input target occurrence view
          (input.buildLocalizedDescriptorBearingRule3FrameExec? target view fuel) equivalent

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
