import TetraStereo.OneCenter.LocalizedParametricExtendedRule3Key
import TetraStereo.OneCenter.LocalizedExtendedFallbackNoRead
import TetraStereo.OneCenter.LocalizedRule3ExclusionExtensionality
import TetraStereo.OneCenter.LocalizedOutwardExtendedRule3Locality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
















































































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The actual extended node under membership-equivalent exclusion lists -/
















theorem localizedRule3ExtendedShortCircuitNodeWithRead?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedRule3ExtendedShortCircuitNodeWithRead?
        target occurrence view read callback left =
      input.localizedRule3ExtendedShortCircuitNodeWithRead?
        target occurrence view read callback right := by
  unfold localizedRule3ExtendedShortCircuitNodeWithRead?
  cases oddRoute : input.localizedRule3OddRouteCertificate? occurrence with
  | some certificate =>
      have containsEq :=
        localizedRule3ExclusionEquivalent_contains input equivalent
      simp only [oddRoute, containsEq]
  | none =>
      simp only [oddRoute]
      unfold localizedRule3ShortCircuitNodeWithRead?
      cases ordinaryRoute : input.localizedRule3OrdinaryRouteCertificate? occurrence with
      | some certificate =>
          have containsEq :=
            localizedRule3ExclusionEquivalent_contains input equivalent
          simp only [ordinaryRoute, containsEq]
      | none =>
          simpa only [localizedRule3ExtendedShortCircuitNodeWithRead?,
            localizedRule3ShortCircuitNodeWithRead?, oddRoute, ordinaryRoute] using
            input.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_of_jointRouteCertificateNone
              target target occurrence view view read read callback callback left right
              ordinaryRoute oddRoute











theorem localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional_via_withRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view callback left =
      input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view callback right := by
  rw [← input.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel
        target occurrence view callback left,
    ← input.localizedRule3ExtendedShortCircuitNodeWithRead?_eq_localizedRule3ExtendedShortCircuitNodeWithExec?_of_localizedDependencyLabel
        target occurrence view callback right]
  exact
    input.localizedRule3ExtendedShortCircuitNodeWithRead?_exclusion_extensional
      target occurrence view
      (fun cursor => input.localizedDependencyLabel target view cursor)
      callback equivalent

/-! ## The actual recursive `WithRead` key

The two-pass frame `buildLocalizedExtendedShortCircuitRule3FrameWithRead?` takes no outer
exclusion parameter: its first key pass runs at `[]`, its exclusion payload is computed from the
coupled topology of those raw keys, and its second key pass runs at that computed payload.
Therefore the predecessor frame supplied as the Rule-3 callback at a successor key index is the
same term on both sides of the exclusion comparison, and the only obligation is the node equality
above. -/

/-- **Exclusion-membership congruence of the actual recursive `WithRead` key.**

At every fuel index, cursor and pair of membership-equivalent exclusion lists, the extended
recursive key is exactly the same `Option _` value, with the same target, view and reader.  The
induction on the shared structural fuel is direct: the executable child list is shared, the
callback frame is shared (it does not depend on the outer exclusion list), the node step is the
extended-node congruence, the child `mapM` pass uses the induction hypothesis pointwise, and the
sort, the terminal record and the parent assembly are syntactically identical.  At fuel zero the
exclusion list does not occur in the definition. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) {left right : List input.LocalizedRule3PhysicalUnitId},
      LocalizedRule3ExclusionEquivalent input left right →
        ∀ cursor : input.LocalizedRerootCursor carrierFuel,
          input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
              target view read fuel left cursor =
            input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
              target view read fuel right cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right _equivalent cursor
      simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?]
  | succ fuel inductionHypothesis =>
      intro left right equivalent cursor
      have keysEq :
          input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
              target view read fuel left =
            input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
              target view read fuel right :=
        funext fun child => inductionHypothesis equivalent child
      have nodeEq :=
        input.localizedRule3ExtendedShortCircuitNodeWithRead?_exclusion_extensional
          target cursor.occurrence view read
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read fuel)
          equivalent
      simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?]
      rw [nodeEq, keysEq]

/-! ## The fuel-indexed extended node

At a successor index the recursive node passes the predecessor frame, which again does not depend
on the outer exclusion list; at zero it is the structural node, which does not read the exclusion
list at all.  Hence only the single-node congruence is needed. -/

/-- **Exclusion-membership congruence of the fuel-indexed extended node.**  Full `Option` equality
at every fuel index and every pair of membership-equivalent exclusion lists, with the same target,
occurrence, view, reader and callback (the frame callback is the predecessor frame). -/
theorem localizedExtendedShortCircuitRule3NodeWithRead?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedExtendedShortCircuitRule3NodeWithRead?
        target occurrence view read fuel left =
      input.localizedExtendedShortCircuitRule3NodeWithRead?
        target occurrence view read fuel right := by
  cases fuel with
  | zero =>
      simp only [localizedExtendedShortCircuitRule3NodeWithRead?]
  | succ fuel =>
      simp only [localizedExtendedShortCircuitRule3NodeWithRead?]
      exact
        input.localizedRule3ExtendedShortCircuitNodeWithRead?_exclusion_extensional
          target occurrence view read
          (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target view read fuel)
          equivalent

/-! ## The shipped executable versions

The shipped executable recursive key and node are the `LocalizedDependencyLabel` specialization of
the parametric recursion.  The same fuel induction goes through with the executable extended-node
extensionality of `LocalizedRule3ExclusionExtensionality` in place of the parametric node step, so
no reader parameter occurs in the statements. -/

/-- **Exclusion-membership congruence of the shipped executable extended recursive key.** -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) {left right : List input.LocalizedRule3PhysicalUnitId},
      LocalizedRule3ExclusionEquivalent input left right →
        ∀ cursor : input.LocalizedRerootCursor carrierFuel,
          input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel left cursor =
            input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel right cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right _equivalent cursor
      simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?]
  | succ fuel inductionHypothesis =>
      intro left right equivalent cursor
      have keysEq :
          input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel left =
            input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
              target view fuel right :=
        funext fun child => inductionHypothesis equivalent child
      have nodeEq :=
        input.localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional
          target cursor.occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
          equivalent
      simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?]
      rw [nodeEq, keysEq]

/-- **Exclusion-membership congruence of the shipped executable fuel-indexed extended node.** -/
theorem localizedExtendedShortCircuitRule3NodeExec?_exclusion_extensional
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedExtendedShortCircuitRule3NodeExec?
        target occurrence view fuel left =
      input.localizedExtendedShortCircuitRule3NodeExec?
        target occurrence view fuel right := by
  cases fuel with
  | zero =>
      simp only [localizedExtendedShortCircuitRule3NodeExec?]
  | succ fuel =>
      simp only [localizedExtendedShortCircuitRule3NodeExec?]
      exact
        input.localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional
          target occurrence view
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel)
          equivalent

/-! ## Composition with outward whole-state locality

`LocalizedOutwardExtendedRule3Locality` proves whole-state versus restricted-dependency equality at
a *shared* exclusion list on outward cursors.  Composing it with the congruence above yields full
`Option` equality when the two exclusion lists merely have the same membership, which is exactly
what the physical-topology comparison supplies.  The shipped executable versions follow by the
unconditional `LocalizedDependencyLabel` specialization of
`LocalizedParametricExtendedRule3Key`. -/

/-- **Whole-state key at `left` versus restricted key at `right`.**  On an outward cursor, the
unrestricted whole-state reader at the exclusion list `left` and the restricted dependency reader
at `right` produce the same extended recursive key, provided `left` and `right` have the same
membership. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_restricted_of_outward_of_exclusionEquivalent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (outward : OutwardRerootCursor input target cursor) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel left cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
        (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) fuel right cursor :=
  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_restricted_of_outward
      target state fuel left cursor outward).trans
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_exclusion_extensional
      target (input.localizedDependencyView state target)
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      fuel equivalent cursor)

/-- **Whole-state key at `left` versus shipped executable key at `right`.**  The same outward
cursor comparison, with the right-hand side specialized to the shipped restricted reader. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_Exec?_of_outward_of_exclusionEquivalent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (outward : OutwardRerootCursor input target cursor) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel left cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target
        (input.localizedDependencyView state target) fuel right cursor :=
  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_restricted_of_outward_of_exclusionEquivalent
      target state fuel equivalent cursor outward).trans
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_eq_buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_of_localizedDependencyLabel
      target (input.localizedDependencyView state target) fuel right cursor)

/-- **Whole-state recursive node at `left` versus restricted recursive node at `right`.**  For a
strict dependency occurrence of the descriptor target, both fuel-indexed nodes agree as full
`Option` values even when the exclusion lists differ, as long as their membership agrees. -/
theorem localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_restricted_of_deeper_of_exclusionEquivalent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency occurrence target)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedExtendedShortCircuitRule3NodeWithRead? target occurrence
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel left =
      input.localizedExtendedShortCircuitRule3NodeWithRead? target occurrence
        (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) fuel right :=
  (input.localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_restricted_of_deeper
      target occurrence deeper state fuel left).trans
    (input.localizedExtendedShortCircuitRule3NodeWithRead?_exclusion_extensional
      target occurrence (input.localizedDependencyView state target)
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      fuel equivalent)

/-- **Whole-state recursive node at `left` versus shipped executable recursive node at `right`.** -/
theorem localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_Exec?_of_deeper_of_exclusionEquivalent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency occurrence target)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat)
    {left right : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input left right) :
    input.localizedExtendedShortCircuitRule3NodeWithRead? target occurrence
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) fuel left =
      input.localizedExtendedShortCircuitRule3NodeExec? target occurrence
        (input.localizedDependencyView state target) fuel right :=
  (input.localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_restricted_of_deeper_of_exclusionEquivalent
      target occurrence deeper state fuel equivalent).trans
    (input.localizedExtendedShortCircuitRule3NodeWithRead?_eq_localizedExtendedShortCircuitRule3NodeExec?_of_localizedDependencyLabel
      target occurrence (input.localizedDependencyView state target) fuel right)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithRead?_exclusion_extensional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional_via_withRead
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_exclusion_extensional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?_exclusion_extensional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_exclusion_extensional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeExec?_exclusion_extensional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_restricted_of_outward_of_exclusionEquivalent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_wholeState_eq_Exec?_of_outward_of_exclusionEquivalent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_restricted_of_deeper_of_exclusionEquivalent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedExtendedShortCircuitRule3NodeWithRead?_wholeState_eq_Exec?_of_deeper_of_exclusionEquivalent
