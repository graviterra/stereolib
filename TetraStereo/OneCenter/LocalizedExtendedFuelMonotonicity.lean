import TetraStereo.OneCenter.LocalizedRule3CallbackRefinement
import TetraStereo.OneCenter.LocalizedRule3ExtendedNodePreservation
import TetraStereo.OneCenter.LocalizedUniversalRule3Evaluation

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Monotone success of the actual extended Rule-3 evaluator in its recursion budget

The actual extended two-pass evaluator

* `buildLocalizedRerootExtendedShortCircuitRule3KeyExec?` (recursive cumulative key), and
* `buildLocalizedExtendedShortCircuitRule3FrameExec?` (full two-pass frame),

recurses into the *predecessor* budget at every node and every recursive child.  This module proves
that every successful recursive outcome is reproduced with the **identical value** when the budget
is increased: the full frame (raw keys, coupled topology, exclusions and rebuilt keys), not merely
some observable of it.

The single-step statement `extendedShortCircuitRule3_mutual_success_refines_succ` is proved by one
simultaneous induction on the budget.  The two directions of the recurrence are:

* the key at budget `n + 1` receives the refined callback frame at budget `n` (and, for a
  nonterminal cursor, the refined child keys at budget `n`); the children are mapped with exactly
  the same list order, so the constitutional assembly, the sort and the merged observation layers
  are unchanged;
* the frame at budget `n + 1` computes its raw keys, coupled topology resolution and excluded
  physical units from exactly the same cursor list and the same refined key function, and its
  rebuilt keys from the same refined key function at the same exclusion list, so both passes
  agree and the stored frame record is unchanged.

The zero-budget key case is structural: `buildLocalizedRerootExtendedShortCircuitRule3KeyExec?`
reads `localizedRule3StructuralNodeExec` at budget zero but the extended node reader at budget one.
A successful structural read already certifies that the occurrence has no real parent/current
order-two edge (`localizedRule3StructuralNodeExec_eq_some_none_iff`); at such an occurrence each
route certificate is absent and the extended node reader is exactly `some none`
(`localizedRule3ExtendedShortCircuitNodeWithExec?_eq_some_none_of_not_edge`).  Hence the terminal
root key is literally the same record at both budgets.

Everything is unconditional: no callback hypothesis, no acyclicity, no readiness certificate, no
root validity, no ranking and no desired descriptor appears.  The final universal theorems only
combine this operational monotonicity with the registered stability theorem
`prepareUniversalRule3EvaluationOutcome_stable` of the green module
`LocalizedUniversalRule3Evaluation`.  They are statements about the executable recursion only; they
do not claim chemical completeness, chemical converses or declarative nonexistence.
-/

/-! ## Structural observations without a parent/current double bond -/

/-- Without a real order-two parent/current edge the executable odd-route inspector finds no odd
route. -/
theorem localizedRule3OddRouteCertificate?_eq_none_of_not_edge
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :
    input.localizedRule3OddRouteCertificate? occurrence = none := by
  simp only [localizedRule3OddRouteCertificate?, dif_neg notEdge]

/-- Without a real order-two parent/current edge the executable ordinary-route inspector finds no
ordinary route either. -/
theorem localizedRule3OrdinaryRouteCertificate?_eq_none_of_not_edge
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :
    input.localizedRule3OrdinaryRouteCertificate? occurrence = none := by
  simp only [localizedRule3OrdinaryRouteCertificate?, dif_neg notEdge]

/-- At a structural nonunit every route certificate is absent, so the extended node reader is the
structural reader's value `some none`, independently of the supplied frame callback and of the
exclusion list.  This is the zero-budget bridge used by the terminal key case. -/
theorem localizedRule3ExtendedShortCircuitNodeWithExec?_eq_some_none_of_not_edge
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = some none := by
  simp only [localizedRule3ExtendedShortCircuitNodeWithExec?,
    input.localizedRule3OddRouteCertificate?_eq_none_of_not_edge occurrence notEdge,
    localizedRule3ShortCircuitNodeWithExec?,
    input.localizedRule3OrdinaryRouteCertificate?_eq_none_of_not_edge occurrence notEdge,
    localizedDescriptorBearingRule3NodeWithExec?, dif_neg notEdge]

/-! ## One-step simultaneous refinement of keys and frames -/

/-- **One-step monotonicity of the actual extended evaluator.**  For every budget, every successful
recursive key and every successful full two-pass frame is retained with the identical value at the
next budget.  Both components are proved by the same induction because the frame step consumes the
key step at the predecessor budget and the key step consumes the frame step at the predecessor
budget. -/
theorem extendedShortCircuitRule3_mutual_success_refines_succ
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel,
      (∀ (excluded : List input.LocalizedRule3PhysicalUnitId)
          (cursor : input.LocalizedRerootCursor carrierFuel),
        OptionSuccessRefines
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view fuel excluded cursor)
          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
            target view (fuel + 1) excluded cursor)) ∧
      (∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
        OptionSuccessRefines
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
            target view fuel cursors)
          (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
            target view (fuel + 1) cursors)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro excluded cursor key computed
        unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec? at computed ⊢
        cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            cases observationComputed :
                input.localizedRule3StructuralNodeExec cursor.occurrence with
            | none => simp [childrenComputed, observationComputed] at computed
            | some observation =>
                by_cases terminal : children = []
                · have notEdge :
                      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence := by
                    intro edge
                    have noneEq :
                        input.localizedRule3StructuralNodeExec cursor.occurrence = none :=
                      (input.localizedRule3StructuralNodeExec_eq_none_iff
                        cursor.occurrence).mpr edge
                    rw [noneEq] at observationComputed
                    cases observationComputed
                  have obsNone : observation = none := by
                    have someNone :
                        input.localizedRule3StructuralNodeExec cursor.occurrence = some none :=
                      (input.localizedRule3StructuralNodeExec_eq_some_none_iff
                        cursor.occurrence).mpr notEdge
                    rw [someNone] at observationComputed
                    simpa using observationComputed.symm
                  simp [childrenComputed, observationComputed, terminal, obsNone] at computed
                  subst key
                  have nodeSome :
                      input.localizedRule3ExtendedShortCircuitNodeWithExec?
                        target cursor.occurrence view
                        (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                          target view 0)
                        excluded = some none :=
                    input.localizedRule3ExtendedShortCircuitNodeWithExec?_eq_some_none_of_not_edge
                      target cursor.occurrence view
                      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                        target view 0)
                      excluded notEdge
                  simp [terminal, nodeSome]
                · simp [childrenComputed, observationComputed, terminal] at computed
      · intro cursors value computed
        simp [buildLocalizedExtendedShortCircuitRule3FrameExec?] at computed
  | succ fuel ih =>
      constructor
      · intro excluded cursor key computed
        unfold buildLocalizedRerootExtendedShortCircuitRule3KeyExec? at computed ⊢
        cases childrenComputed : input.executableLocalizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            cases observationComputed :
                input.localizedRule3ExtendedShortCircuitNodeWithExec?
                  target cursor.occurrence view
                  (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                    target view fuel)
                  excluded with
            | none => simp [childrenComputed, observationComputed] at computed
            | some observation =>
                have nodeNext :=
                  (input.extendedShortNodeWith_callback_refines
                    target cursor.occurrence view
                    (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                      target view fuel)
                    (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                      target view (fuel + 1))
                    ih.2 excluded) observation observationComputed
                by_cases terminal : children = []
                · simp [childrenComputed, observationComputed, terminal] at computed
                  subst key
                  simp [terminal, nodeNext]
                · simp [childrenComputed, observationComputed, terminal] at computed
                  cases childKeysComputed : children.mapM
                      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                        target view fuel excluded) with
                  | none => simp [childKeysComputed] at computed
                  | some childKeys =>
                      simp [childKeysComputed] at computed
                      subst key
                      have childKeysNext :
                          children.mapM
                            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                              target view (fuel + 1) excluded) = some childKeys :=
                        OptionSuccessRefines.mapM
                          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                            target view fuel excluded)
                          (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
                            target view (fuel + 1) excluded)
                          (ih.1 excluded) children childKeys childKeysComputed
                      simp [terminal, nodeNext, childKeysNext]
      · intro cursors
        unfold buildLocalizedExtendedShortCircuitRule3FrameExec? at ⊢
        apply OptionSuccessRefines.bind
          (OptionSuccessRefines.mapM _ _ (ih.1 []) cursors)
        intro rawKeys
        apply OptionSuccessRefines.bind (.refl _)
        intro topology
        apply OptionSuccessRefines.bind
          (OptionSuccessRefines.mapM _ _
            (ih.1 (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys topology))
            cursors)
        intro keys
        exact .refl _

/-! ## Named one-step projections -/

/-- One-step successful-value refinement of every complete recursive key. -/
theorem extendedShortCircuitRule3Key_success_refines_succ
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    OptionSuccessRefines
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view fuel excluded cursor)
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view (fuel + 1) excluded cursor) :=
  (input.extendedShortCircuitRule3_mutual_success_refines_succ target view fuel).1 excluded cursor

/-- One-step successful-value refinement of the complete two-pass frame, including raw keys,
coupled topology, the excluded physical-unit list and the rebuilt keys. -/
theorem extendedShortCircuitRule3Frame_success_refines_succ
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    OptionSuccessRefines
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view fuel cursors)
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view (fuel + 1) cursors) :=
  (input.extendedShortCircuitRule3_mutual_success_refines_succ target view fuel).2 cursors

/-! ## From one step to an arbitrary larger budget -/

/-- Every successful complete key at a budget is reproduced identically at every larger budget. -/
theorem extendedShortCircuitRule3Key_success_refines_of_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel) :
    OptionSuccessRefines
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view lowFuel excluded cursor)
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
        target view highFuel excluded cursor) := by
  obtain ⟨difference, rfl⟩ := Nat.le.dest le
  clear le
  induction difference with
  | zero => simpa using OptionSuccessRefines.refl _
  | succ difference ih =>
      exact ih.trans
        (input.extendedShortCircuitRule3Key_success_refines_succ target view
          (lowFuel + difference) excluded cursor)

/-- Every successful complete two-pass frame at a budget is reproduced identically at every larger
budget. -/
theorem extendedShortCircuitRule3Frame_success_refines_of_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel) :
    OptionSuccessRefines
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view lowFuel cursors)
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view highFuel cursors) := by
  obtain ⟨difference, rfl⟩ := Nat.le.dest le
  clear le
  induction difference with
  | zero => simpa using OptionSuccessRefines.refl _
  | succ difference ih =>
      exact ih.trans
        (input.extendedShortCircuitRule3Frame_success_refines_succ target view
          (lowFuel + difference) cursors)

/-- **Exported success monotonicity, exact full frame.**  Any complete frame produced at a budget
is produced, with the same raw keys, coupled topology, excluded physical units and rebuilt keys, at
every larger budget.  No callback, acyclicity, readiness, ranking or root-validity hypothesis is
used. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_success_monotone_of_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view lowFuel cursors = some frame) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view highFuel cursors = some frame :=
  (input.extendedShortCircuitRule3Frame_success_refines_of_le target view cursors le)
    frame computed

/-- The corresponding exact-key monotonicity. -/
theorem buildLocalizedRerootExtendedShortCircuitRule3KeyExec?_success_monotone_of_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view lowFuel excluded cursor = some key) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec?
      target view highFuel excluded cursor = some key :=
  (input.extendedShortCircuitRule3Key_success_refines_of_le target view excluded cursor le)
    key computed

/-- A frame successful at a lower budget has the declarative two-pass meaning at every larger
budget, because the *same* frame is still produced there.  This is a consequence of monotonicity
together with the registered soundness theorem, not a new semantic claim. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_sound_of_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target view lowFuel cursors = some frame) :
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame
      target view highFuel cursors frame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound target view highFuel cursors frame
    (input.buildLocalizedExtendedShortCircuitRule3FrameExec?_success_monotone_of_le
      target view cursors le frame computed)













/-- The computed universal optional frame is `some frame` exactly when some actual evaluation
budget returns that same frame. -/
theorem prepareUniversalRule3EvaluationOutcome_some_iff_exists_budget
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame) :
    (prepareUniversalRule3EvaluationOutcome input roots target view).2 = some frame ↔
      ∃ evaluationBudget,
        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view evaluationBudget roots = some frame := by
  constructor
  · intro computed
    refine ⟨(prepareUniversalRule3EvaluationOutcome input roots target view).1, ?_⟩
    rw [input.prepareUniversalRule3EvaluationOutcome_stable roots target view
      (prepareUniversalRule3EvaluationOutcome input roots target view).1 le_rfl]
    exact computed
  · rintro ⟨evaluationBudget, computed⟩
    have atMax :=
      input.buildLocalizedExtendedShortCircuitRule3FrameExec?_success_monotone_of_le
        target view roots
        (Nat.le_max_left evaluationBudget
          (prepareUniversalRule3EvaluationOutcome input roots target view).1)
        frame computed
    rw [input.prepareUniversalRule3EvaluationOutcome_stable roots target view
      (max evaluationBudget
        (prepareUniversalRule3EvaluationOutcome input roots target view).1)
      (Nat.le_max_right _ _)] at atMax
    exact atMax

/-- The computed universal optional frame is `none` exactly when the actual evaluator refuses at
every budget.  The forward direction is where monotonicity is essential: a success below the
computed bound would have to be reproduced at the bound. -/
theorem prepareUniversalRule3EvaluationOutcome_none_iff_forall_budget
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (prepareUniversalRule3EvaluationOutcome input roots target view).2 = none ↔
      ∀ evaluationBudget,
        input.buildLocalizedExtendedShortCircuitRule3FrameExec?
          target view evaluationBudget roots = none := by
  constructor
  · intro computed evaluationBudget
    cases actualComputed : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
        target view evaluationBudget roots with
    | none => rfl
    | some frame =>
        have someOutcome :=
          (input.prepareUniversalRule3EvaluationOutcome_some_iff_exists_budget
            roots target view frame).mpr ⟨evaluationBudget, actualComputed⟩
        rw [computed] at someOutcome
        cases someOutcome
  · intro allNone
    have stable := input.prepareUniversalRule3EvaluationOutcome_stable roots target view
      (prepareUniversalRule3EvaluationOutcome input roots target view).1 le_rfl
    rw [allNone] at stable
    exact stable.symm

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
