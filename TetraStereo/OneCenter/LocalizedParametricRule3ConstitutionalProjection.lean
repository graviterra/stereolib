import TetraStereo.OneCenter.LocalizedParametricExtendedRule3Key
import TetraStereo.OneCenter.LocalizedEndpointFrameCompletenessBridge
import TetraStereo.OneCenter.LocalizedRerootRootObservation
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Constitutional projection of the parametric extended Rule-3 key

`LocalizedParametricExtendedRule3Key` parameterizes the direct Rules-4/5 label reader of the
extended short-circuit Rule-3 recursion.  Its key/frame/node compilers are the executable ones with
only that reader replaced; their *successful* outcomes still carry the reader-dependent node
observation, so the unconditional executable soundness theorem
`buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_sound` and the bridge theorem
`extendedShortCircuitRule3Key_constitutional_derived` do not apply to an arbitrary reader.

The constitutional component of a successful key, however, never inspects that observation: at a
terminal node it is the address-`[]` root key, and at a branch node it is the address-`[]` root key
joined to the recursively assembled child constitutional keys.  This module therefore proves, by a
genuine structural induction over the *actual* successful `WithRead` key, that the constitutional
component is independently derivable:

`buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived`.

The induction erases the reader-dependent node meaning.  At a successor branch it consumes the
recursive success of the child key pass through
`projected_rule3_constitutional_key_list`, the sibling ranking through
`sortLocalizedRerootRecursiveRule3SpatialKeys_perm`, and the sibling order through
`sortLocalizedRerootRecursiveRule3SpatialKeys_descending` together with
`rule3_descending_constitutional`.  No frame meaning, node meaning, computed success of the frame,
or whole-key equality with the executable compiler is assumed or claimed.

From that derivation the module obtains:

* the three Rule-1a/1b/2 first-sphere observations of the successful key, pinned to the cursor
  occurrence's own root observations (`..._rootHeads`), using the `assemble` head lemmas;
* equality of the constitutional observable across two successful keys at arbitrary readers,
  fuels and exclusion lists on the same cursor, via
  `declarative_constitutional_observable_unique`;
* comparison transport (`ruleMajor_compare_congr`), equality of the transported comparison, and
  Rule-1b first-layer separation (`compare_ne_eq_of_rule1b_head_distances`) for distinct retained
  root distances;
* the length facts for both passes of the actual `WithRead` frame, mirroring
  `buildLocalizedExtendedShortCircuitRule3FrameExec?_keys_length`.  A successful ordinary frame is
  not claimed to have an empty exclusion list; both the raw pass and the rebuilt pass are retained.

## What is not claimed

No arbitrary-reader equality between the parameterized compiler and the executable compiler is
asserted, and no general totality of any compiler is asserted.  The only inputs are hypotheses of
success (`= some key`), and all conclusions are conditional on them.

## Kernel authority

Every exported declaration is guarded by `assert_kernel_only` at the end of the file.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Auxiliary success lemmas

The generic `mapM` lemmas and the executable-children soundness step are the components used by the
existing executable soundness proof.  They are restated here because the corresponding helpers in
`LocalizedRerootExtendedShortCircuitRule3Key` and `LocalizedExtendedRefusalClassification` are
private. -/

/-- A successful `mapM` realizes the pointwise relation selected by its per-element success. -/
private theorem mapM_forall₂_of_success_paramRule3
    {α β : Type*} (f : α → Option β) (R : α → β → Prop)
    (sound : ∀ a b, f a = some b → R a b) :
    ∀ as bs, as.mapM f = some bs → List.Forall₂ R as bs
  | [], bs, computed => by
      simp at computed
      subst bs
      exact List.Forall₂.nil
  | a :: as, bs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some b =>
          cases tailComputed : as.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst bs
              exact List.Forall₂.cons (sound a b headComputed)
                (mapM_forall₂_of_success_paramRule3 f R sound as tail tailComputed)

/-- A successful `mapM` preserves the length of its input list. -/
private theorem mapM_length_eq_of_success_paramRule3
    {α β : Type*} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β),
      inputs.mapM f = some outputs → outputs.length = inputs.length
  | [], outputs, computed => by
      simp at computed
      subst outputs
      rfl
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              simp [mapM_length_eq_of_success_paramRule3 f inputs tail tailComputed]

/-- The executable reroot child list is exactly the independently specified cut neighborhood. -/
private theorem executableChildren_declarative_paramRule3
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.executableLocalizedRerootChildren? cursor = some children) :
    input.DeclarativeLocalizedRerootChildren cursor children := by
  apply input.localizedRerootChildren?_sound cursor children
  rw [input.localizedRerootChildren?_eq_some_executable]
  exact (input.executableLocalizedRerootChildren?_eq_some cursor).symm.trans computed

/-! ## The successful-key constitutional core

The induction below follows the actual `WithRead` key compiler.  At a successor node the node
observation is quantified but never inspected: its success is only what allows the compiler to
return `some`.  The constitutional component is assembled from the recursive child keys, so the
induction hypothesis for the predecessor fuel is exactly what the child key pass needs. -/

/-- Every successful key of the parametric extended Rule-3 compiler has an independently derivable
constitutional component, and its first Rule-1a/1b/2 sphere is the cursor occurrence's own root
observation.  The reader, the node observation and the two-pass frame are all erased: only the
success of the compiler is used. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived_and_rootHeads
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ fuel excluded cursor key,
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
          target view read fuel excluded cursor = some key →
        input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional ∧
        key.constitutional.rule1a.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).1)] ∧
        key.constitutional.rule1b.head? =
          some [([], cursor.occurrence.1.node.rule1bRootDistance)] ∧
        key.constitutional.rule2.head? =
          some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).2)] := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor key computed
      unfold buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? at computed
      cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3StructuralNodeExec cursor.occurrence with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact
                  ⟨.terminal
                      (input.executableChildren_declarative_paramRule3
                        cursor children childrenComputed) terminal,
                    by simp [MoleculeGraph.officialRuleMajorRootKey],
                    by simp [MoleculeGraph.officialRuleMajorRootKey],
                    by simp [MoleculeGraph.officialRuleMajorRootKey]⟩
              · simp [childrenComputed, observationComputed, terminal] at computed
  | succ fuel ih =>
      intro excluded cursor key computed
      unfold buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead? at computed
      cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed :
              input.localizedRule3ExtendedShortCircuitNodeWithRead?
                target cursor.occurrence view read
                (input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
                  target view read fuel)
                excluded with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact
                  ⟨.terminal
                      (input.executableChildren_declarative_paramRule3
                        cursor children childrenComputed) terminal,
                    by simp [MoleculeGraph.officialRuleMajorRootKey],
                    by simp [MoleculeGraph.officialRuleMajorRootKey],
                    by simp [MoleculeGraph.officialRuleMajorRootKey]⟩
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                      target view read fuel excluded) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    have childDerivations :
                        input.DeclarativeLocalizedRerootRuleMajorKeyList fuel children
                          (childKeys.map (fun child => child.constitutional)) :=
                      input.projected_rule3_constitutional_key_list
                        (R := fun cursor key =>
                          input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                            target view read fuel excluded cursor = some key)
                        (fun cursor key success =>
                          (ih excluded cursor key success).1)
                        children childKeys
                        (mapM_forall₂_of_success_paramRule3 _
                          (fun cursor key =>
                            input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
                              target view read fuel excluded cursor = some key)
                          (fun _cursor _key success => success)
                          children childKeys childKeysComputed)
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · exact
                        DeclarativeLocalizedRerootRuleMajorKey.branch
                          (input.executableChildren_declarative_paramRule3
                            cursor children childrenComputed)
                          terminal childDerivations
                          ((input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm
                            childKeys).map
                              (fun key => key.constitutional))
                          (input.rule3_descending_constitutional
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys
                              childKeys)
                            (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending
                              childKeys))
                    · exact
                        OfficialRuleMajorKey.assemble_officialRuleMajorRootKey_rule1a_head
                          _ _ _ _
                    · exact
                        OfficialRuleMajorKey.assemble_officialRuleMajorRootKey_rule1b_head
                          _ _ _ _
                    · exact
                        OfficialRuleMajorKey.assemble_officialRuleMajorRootKey_rule2_head
                          _ _ _ _

/-- **Arbitrary-reader constitutional projection.**  Every successful key of the parametric
extended Rule-3 compiler, at any reader, fuel, exclusion list and cursor, has an independently
derived `DeclarativeLocalizedRerootRuleMajorKey` for its constitutional component.  Neither the
reader nor the node observation is inspected, and no totality is assumed. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view read fuel excluded cursor = some key) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional :=
  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived_and_rootHeads
    target view read fuel excluded cursor key computed).1

/-- The first Rule-1a sphere of a successful arbitrary-reader key is the cursor node's own
observation at the empty address. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view read fuel excluded cursor = some key) :
    key.constitutional.rule1a.head? =
      some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
        cursor.occurrence.1.node)).1)] :=
  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived_and_rootHeads
    target view read fuel excluded cursor key computed).2.1

/-- The first Rule-1b sphere of a successful arbitrary-reader key carries the cursor node's own
retained original-root distance at the empty address. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view read fuel excluded cursor = some key) :
    key.constitutional.rule1b.head? =
      some [([], cursor.occurrence.1.node.rule1bRootDistance)] :=
  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived_and_rootHeads
    target view read fuel excluded cursor key computed).2.2.1

/-- The first Rule-2 sphere of a successful arbitrary-reader key is the cursor node's own mass
observation at the empty address. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule2_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view read fuel excluded cursor = some key) :
    key.constitutional.rule2.head? =
      some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
        cursor.occurrence.1.node)).2)] :=
  (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived_and_rootHeads
    target view read fuel excluded cursor key computed).2.2.2

/-! ## The production specialization

For the shipped executable key compiler the existing bridge theorem
`extendedShortCircuitRule3Key_constitutional_derived` already extracts the constitutional
derivation from the independent extended key meaning.  Composing it with executable soundness gives
the same result as the arbitrary-reader core on the production path, without re-proving it. -/

/-- Production-path constitutional projection: every successful executable extended key has an
independently derivable constitutional component, obtained from executable soundness and the
existing bridge theorem. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view fuel excluded cursor = some key) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional :=
  input.extendedShortCircuitRule3Key_constitutional_derived
    target view fuel excluded cursor key
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_sound
      target view fuel excluded cursor key computed)

/-! ## Constitutional observable and comparator corollaries

Two successful keys at the same cursor but with arbitrary readers, fuels and exclusion lists have
independently derived constitutional components at possibly different budgets.  The existing
uniqueness theorem `declarative_constitutional_observable_unique` makes those components
observably equal, and `ruleMajor_compare_congr` transports every comparison across that equality. -/

/-- Two successful arbitrary-reader keys on the same cursor have equal constitutional
observables, regardless of reader, fuel or exclusion list. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (firstRead secondRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (firstFuel secondFuel : Nat)
    (firstExcluded secondExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view firstRead firstFuel firstExcluded cursor = some first)
    (secondComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view secondRead secondFuel secondExcluded cursor = some second) :
    constitutionalObservable first.constitutional =
      constitutionalObservable second.constitutional :=
  input.declarative_constitutional_observable_unique firstFuel secondFuel cursor
    first.constitutional second.constitutional
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived
      target view firstRead firstFuel firstExcluded cursor first firstComputed)
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived
      target view secondRead secondFuel secondExcluded cursor second secondComputed)

/-- Comparison transport on the left: replacing one successful key's constitutional component by
another successful one at the same cursor does not change its comparison with any fixed key. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_congr_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (firstRead secondRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (firstFuel secondFuel : Nat)
    (firstExcluded secondExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.LocalizedRerootRecursiveRule3SpatialKey)
    (other : OfficialRuleMajorKey input.Atom)
    (firstComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view firstRead firstFuel firstExcluded cursor = some first)
    (secondComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view secondRead secondFuel secondExcluded cursor = some second) :
    OfficialRuleMajorKey.compare first.constitutional other =
      OfficialRuleMajorKey.compare second.constitutional other :=
  ruleMajor_compare_congr first.constitutional other
    second.constitutional other
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_observable_eq
      target view firstRead secondRead firstFuel secondFuel
      firstExcluded secondExcluded cursor first second firstComputed secondComputed)
    rfl

/-- Comparison transport on the right: replacing one successful key's constitutional component by
another successful one at the same cursor does not change any fixed key's comparison with it. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_congr_right
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (firstRead secondRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (firstFuel secondFuel : Nat)
    (firstExcluded secondExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.LocalizedRerootRecursiveRule3SpatialKey)
    (other : OfficialRuleMajorKey input.Atom)
    (firstComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view firstRead firstFuel firstExcluded cursor = some first)
    (secondComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view secondRead secondFuel secondExcluded cursor = some second) :
    OfficialRuleMajorKey.compare other first.constitutional =
      OfficialRuleMajorKey.compare other second.constitutional :=
  ruleMajor_compare_congr other first.constitutional
    other second.constitutional rfl
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_observable_eq
      target view firstRead secondRead firstFuel secondFuel
      firstExcluded secondExcluded cursor first second firstComputed secondComputed)

/-- Two successful arbitrary-reader keys on the same cursor compare equal, despite possibly
different provenance records and recursion budgets. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (firstRead secondRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (firstFuel secondFuel : Nat)
    (firstExcluded secondExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view firstRead firstFuel firstExcluded cursor = some first)
    (secondComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view secondRead secondFuel secondExcluded cursor = some second) :
    OfficialRuleMajorKey.compare first.constitutional second.constitutional =
      Ordering.eq := by
  have observed :=
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_observable_eq
      target view firstRead secondRead firstFuel secondFuel
      firstExcluded secondExcluded cursor first second firstComputed secondComputed
  rw [ruleMajor_compare_eq_observable, observed]
  exact (compareConstitutionalObservable_eq_iff _ _).mpr rfl

/-- Rule-1b first-layer separation for successful arbitrary-reader keys: if the two cursors carry
distinct retained original-root distances, the constitutional keys cannot compare equal. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_ne_eq_of_rule1bRootDistance_ne
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (firstRead secondRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (firstFuel secondFuel : Nat)
    (firstExcluded secondExcluded : List input.LocalizedRule3PhysicalUnitId)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view firstRead firstFuel firstExcluded firstCursor = some first)
    (secondComputed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?
      target view secondRead secondFuel secondExcluded secondCursor = some second)
    (different : firstCursor.occurrence.1.node.rule1bRootDistance ≠
      secondCursor.occurrence.1.node.rule1bRootDistance) :
    OfficialRuleMajorKey.compare first.constitutional second.constitutional ≠
      Ordering.eq :=
  OfficialRuleMajorKey.compare_ne_eq_of_rule1b_head_distances
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule1b_head
      target view firstRead firstFuel firstExcluded firstCursor first firstComputed)
    (input.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule1b_head
      target view secondRead secondFuel secondExcluded secondCursor second secondComputed)
    different

/-! ## Length facts for the two-pass `WithRead` frame

The frame performs two independent key passes over the same cursor list: the raw pass with the
empty exclusion list, and the rebuilt pass with the coupled exclusion set computed from the raw
keys and the resolved topology.  Both passes preserve the cursor count, so both `rawKeys` and
`keys` have exactly the cursor-list length.  A successful ordinary frame is *not* claimed to have
an empty exclusion list. -/

/-- Every successful arbitrary-reader frame has exactly as many rebuilt keys as cursors. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read fuel cursors = some frame) :
    frame.keys.length = cursors.length := by
  cases fuel with
  | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameWithRead?] at computed
  | succ fuel =>
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
                  simp [rawComputed, topologyComputed, excluded,
                    keysComputed] at computed
              | some keys =>
                  simp [rawComputed, topologyComputed, excluded,
                    keysComputed] at computed
                  subst frame
                  exact mapM_length_eq_of_success_paramRule3 _ cursors keys keysComputed

/-- Every successful arbitrary-reader frame has exactly as many raw keys as cursors. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead?
      target view read fuel cursors = some frame) :
    frame.rawKeys.length = cursors.length := by
  cases fuel with
  | zero => simp [buildLocalizedExtendedShortCircuitRule3FrameWithRead?] at computed
  | succ fuel =>
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
                  simp [rawComputed, topologyComputed, excluded,
                    keysComputed] at computed
              | some keys =>
                  simp [rawComputed, topologyComputed, excluded,
                    keysComputed] at computed
                  subst frame
                  exact mapM_length_eq_of_success_paramRule3 _ cursors rawKeys rawComputed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the arbitrary-reader constitutional projection with its three
first-sphere corollaries, the production specialization through the existing bridge, the
observable and comparator corollaries, and the two frame length facts.  Every one is conditional
on a success hypothesis; no totality or arbitrary-reader whole-key equality is asserted. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived_and_rootHeads
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_derived
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule1a_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule1b_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_rule2_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_constitutional_derived
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_observable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_congr_left
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_congr_right
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootExtendedShortCircuitRule3KeyWithRead?_constitutional_compare_ne_eq_of_rule1bRootDistance_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_keys_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameWithRead?_rawKeys_length
