import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Exact
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact canonical semantics for the occurrence Rules-4a--5 descriptor

This module lifts exact canonical reroot-key compilation through pair comparison, the tracked
four-ligand stable sort, the all-pairs coherence gate, direct coordinate lookup, exact rational
orientation, and final uppercase/lowercase classification.  Both `some` and `none` results are
characterized.  This closes implementation correspondence for the current fuel-bounded evaluator;
it does not by itself prove that the chosen reroot fuel is chemically complete.
-/

namespace CertifiedLocalizedCIPInput

/-- Every indexed cursor in an exact four-ligand frame is a valid first reroot step from the
descriptor target. -/
theorem LocalizedOccurrenceFourLigandFrame.cursorAt_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    input.LocalizedRerootCursorValid (frame.cursorAt index) := by
  have present : frame.cursorAt index ∈ frame.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm index)
  exact input.localizedRerootChild_valid
    { occurrence := target, previous? := none }
    (frame.cursorAt index) frame.cursors derived.1 present

/-- Once the exact four-ligand carrier frame exists, reroot fuel cannot make a pair comparison
fail.  Any later refusal comes from a genuine tie/cycle or spatial-applicability gate. -/
theorem exists_compareLocalizedOccurrenceThroughRule5At?_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (left right : Fin 4) :
    ∃ result, input.compareLocalizedOccurrenceThroughRule5At?
      target view frame left right = some result := by
  obtain ⟨leftKey, leftComputed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view (frame.cursorAt left) (frame.cursorAt_valid input target derived left)
  obtain ⟨rightKey, rightComputed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view (frame.cursorAt right) (frame.cursorAt_valid input target derived right)
  refine ⟨localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey), ?_⟩
  simp [compareLocalizedOccurrenceThroughRule5At?, localizedOccurrenceRerootEvaluationFuel,
    leftComputed, rightComputed]

/-- Canonical pairwise comparison derived from the two exact compound Rule-45 keys. -/
def CanonicalLocalizedOccurrenceThroughRule5At
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison) : Prop :=
  ∃ leftKey rightKey,
    input.CanonicalLocalizedRerootCompoundRule45Key target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) leftKey ∧
    input.CanonicalLocalizedRerootCompoundRule45Key target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt right) rightKey ∧
    result = localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey)

/-- Pair comparison succeeds exactly when two canonical compound keys determine the result. -/
theorem compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) (result : ConstitutionalDescriptorHierarchyComparison) :
    input.compareLocalizedOccurrenceThroughRule5At?
        target view frame left right = some result ↔
      input.CanonicalLocalizedOccurrenceThroughRule5At
        target view frame left right result := by
  constructor
  · intro computed
    unfold compareLocalizedOccurrenceThroughRule5At? at computed
    cases leftComputed : input.buildLocalizedRerootCompoundRule45Key?
        target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (frame.cursorAt left) with
    | none => simp [leftComputed] at computed
    | some leftKey =>
        cases rightComputed : input.buildLocalizedRerootCompoundRule45Key?
            target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
            (frame.cursorAt right) with
        | none => simp [leftComputed, rightComputed] at computed
        | some rightKey =>
            simp [leftComputed, rightComputed] at computed
            subst result
            exact ⟨leftKey, rightKey,
              (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
                target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                (frame.cursorAt left) leftKey).mp leftComputed,
              (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
                target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                (frame.cursorAt right) rightKey).mp rightComputed,
              rfl⟩
  · rintro ⟨leftKey, rightKey, leftDerived, rightDerived, rfl⟩
    have leftComputed :=
      (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
        target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (frame.cursorAt left) leftKey).mpr leftDerived
    have rightComputed :=
      (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
        target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (frame.cursorAt right) rightKey).mpr rightDerived
    simp [compareLocalizedOccurrenceThroughRule5At?, leftComputed, rightComputed]

/-- Pair-comparison refusal is exactly absence of a canonical pair result. -/
theorem compareLocalizedOccurrenceThroughRule5At?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) :
    input.compareLocalizedOccurrenceThroughRule5At? target view frame left right = none ↔
      ¬ ∃ result, input.CanonicalLocalizedOccurrenceThroughRule5At
        target view frame left right result := by
  constructor
  · intro computed ⟨result, derived⟩
    have successful :=
      (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
        target view frame left right result).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : input.compareLocalizedOccurrenceThroughRule5At?
        target view frame left right with
    | none => rfl
    | some result =>
        exact False.elim (absent ⟨result,
          (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
            target view frame left right result).mp computed⟩)

/-! ## Exact tracked insertion and sorting -/

/-- Canonical occurrence-specific insertion history. -/
inductive CanonicalLocalizedOccurrenceRule45Insertion
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (candidate : Fin 4) :
    List (Fin 4) → TrackedLocalizedLigandInsertion → Prop
  | nil : CanonicalLocalizedOccurrenceRule45Insertion
      input target view frame candidate []
      { lowestFirst := [candidate], pseudoComparisons := 0 }
  | placeBefore {low remaining comparison}
      (compared : input.CanonicalLocalizedOccurrenceThroughRule5At
        target view frame low candidate comparison)
      (higherLow : comparison.ordering = Ordering.gt) :
      CanonicalLocalizedOccurrenceRule45Insertion input target view frame candidate
        (low :: remaining)
        { lowestFirst := candidate :: low :: remaining
          pseudoComparisons := if comparison.pseudo then 1 else 0 }
  | placeAfter {low remaining comparison deeper}
      (compared : input.CanonicalLocalizedOccurrenceThroughRule5At
        target view frame low candidate comparison)
      (lowerLow : comparison.ordering = Ordering.lt)
      (tail : CanonicalLocalizedOccurrenceRule45Insertion
        input target view frame candidate remaining deeper) :
      CanonicalLocalizedOccurrenceRule45Insertion input target view frame candidate
        (low :: remaining)
        { lowestFirst := low :: deeper.lowestFirst
          pseudoComparisons :=
            (if comparison.pseudo then 1 else 0) + deeper.pseudoComparisons }

theorem declarativeTrackedLocalizedLigandInsertion_toCanonicalOccurrenceRule45
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    {candidate : Fin 4} {existing : List (Fin 4)}
    {result : TrackedLocalizedLigandInsertion}
    (derived : DeclarativeTrackedLocalizedLigandInsertion
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      candidate existing result) :
    input.CanonicalLocalizedOccurrenceRule45Insertion
      target view frame candidate existing result := by
  induction derived with
  | nil => exact CanonicalLocalizedOccurrenceRule45Insertion.nil
  | placeBefore compared higherLow =>
      exact CanonicalLocalizedOccurrenceRule45Insertion.placeBefore
        ((input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
          target view frame _ _ _).mp compared) higherLow
  | placeAfter compared lowerLow tail inductionHypothesis =>
      exact CanonicalLocalizedOccurrenceRule45Insertion.placeAfter
        ((input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
          target view frame _ _ _).mp compared) lowerLow inductionHypothesis

theorem CanonicalLocalizedOccurrenceRule45Insertion.toTracked
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    {candidate : Fin 4} {existing : List (Fin 4)}
    {result : TrackedLocalizedLigandInsertion}
    (derived : input.CanonicalLocalizedOccurrenceRule45Insertion
      target view frame candidate existing result) :
    DeclarativeTrackedLocalizedLigandInsertion
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      candidate existing result := by
  induction derived with
  | nil => exact DeclarativeTrackedLocalizedLigandInsertion.nil
  | placeBefore compared higherLow =>
      exact DeclarativeTrackedLocalizedLigandInsertion.placeBefore
        ((input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
          target view frame _ _ _).mpr compared) higherLow
  | placeAfter compared lowerLow tail inductionHypothesis =>
      exact DeclarativeTrackedLocalizedLigandInsertion.placeAfter
        ((input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
          target view frame _ _ _).mpr compared) lowerLow inductionHypothesis

/-- Executable insertion is exactly the canonical occurrence-specific history. -/
theorem insertLocalizedOccurrenceRule45Tracked_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (candidate : Fin 4) (existing : List (Fin 4))
    (result : TrackedLocalizedLigandInsertion) :
    insertLocalizedLigandTracked
        (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
        candidate existing = some result ↔
      input.CanonicalLocalizedOccurrenceRule45Insertion
        target view frame candidate existing result := by
  constructor
  · intro computed
    exact input.declarativeTrackedLocalizedLigandInsertion_toCanonicalOccurrenceRule45
      target view frame ((insertLocalizedLigandTracked_eq_some_iff
        (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
        candidate existing result).mp computed)
  · intro derived
    exact (insertLocalizedLigandTracked_eq_some_iff
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      candidate existing result).mpr
        (derived.toTracked input target view frame)

/-- Canonical complete tracked stable-sort history. -/
inductive CanonicalLocalizedOccurrenceRule45Sort
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    List (Fin 4) → List (Fin 4) → Nat → TrackedLocalizedLigandOrder → Prop
  | nil (lowestFirst : List (Fin 4)) (pseudoComparisons : Nat) :
      CanonicalLocalizedOccurrenceRule45Sort input target view frame []
        lowestFirst pseudoComparisons
        { highestFirst := lowestFirst.reverse
          pseudoComparisons := pseudoComparisons }
  | cons {candidate candidates lowestFirst pseudoComparisons inserted result}
      (insertion : input.CanonicalLocalizedOccurrenceRule45Insertion
        target view frame candidate lowestFirst inserted)
      (tail : CanonicalLocalizedOccurrenceRule45Sort input target view frame
        candidates inserted.lowestFirst
        (pseudoComparisons + inserted.pseudoComparisons) result) :
      CanonicalLocalizedOccurrenceRule45Sort input target view frame
        (candidate :: candidates) lowestFirst pseudoComparisons result

theorem declarativeTrackedLocalizedLigandSort_toCanonicalOccurrenceRule45
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    {candidates lowestFirst : List (Fin 4)} {pseudoComparisons : Nat}
    {result : TrackedLocalizedLigandOrder}
    (derived : DeclarativeTrackedLocalizedLigandSort
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      candidates lowestFirst pseudoComparisons result) :
    input.CanonicalLocalizedOccurrenceRule45Sort target view frame
      candidates lowestFirst pseudoComparisons result := by
  induction derived with
  | nil lowestFirst pseudoComparisons =>
      exact CanonicalLocalizedOccurrenceRule45Sort.nil lowestFirst pseudoComparisons
  | cons insertion tail inductionHypothesis =>
      exact CanonicalLocalizedOccurrenceRule45Sort.cons
        (input.declarativeTrackedLocalizedLigandInsertion_toCanonicalOccurrenceRule45
          target view frame insertion)
        inductionHypothesis

theorem CanonicalLocalizedOccurrenceRule45Sort.toTracked
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    {candidates lowestFirst : List (Fin 4)} {pseudoComparisons : Nat}
    {result : TrackedLocalizedLigandOrder}
    (derived : input.CanonicalLocalizedOccurrenceRule45Sort target view frame
      candidates lowestFirst pseudoComparisons result) :
    DeclarativeTrackedLocalizedLigandSort
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      candidates lowestFirst pseudoComparisons result := by
  induction derived with
  | nil lowestFirst pseudoComparisons =>
      exact DeclarativeTrackedLocalizedLigandSort.nil lowestFirst pseudoComparisons
  | cons insertion tail inductionHypothesis =>
      exact DeclarativeTrackedLocalizedLigandSort.cons
        (insertion.toTracked input target view frame) inductionHypothesis

/-- The executable four-ligand sort is exactly the canonical occurrence sort. -/
theorem localizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder) :
    input.localizedOccurrenceRule45TrackedOrder? target view frame = some tracked ↔
      input.CanonicalLocalizedOccurrenceRule45Sort target view frame
        (List.finRange 4) [] 0 tracked := by
  unfold localizedOccurrenceRule45TrackedOrder?
  constructor
  · intro computed
    exact input.declarativeTrackedLocalizedLigandSort_toCanonicalOccurrenceRule45
      target view frame ((sortFourLocalizedLigandsTracked_eq_some_iff
        (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
        tracked).mp computed)
  · intro derived
    exact (sortFourLocalizedLigandsTracked_eq_some_iff
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      tracked).mpr (derived.toTracked input target view frame)

/-- Canonical safe order: exact sort history, exact permutation, and every earlier/later pair. -/
def CanonicalSafeLocalizedOccurrenceRule45TrackedOrder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder) : Prop :=
  input.CanonicalLocalizedOccurrenceRule45Sort target view frame
      (List.finRange 4) [] 0 tracked ∧
    tracked.highestFirst.Perm (List.finRange 4) ∧
    tracked.highestFirst.Pairwise fun left right =>
      ∃ result,
        input.CanonicalLocalizedOccurrenceThroughRule5At
          target view frame left right result ∧
        result.ordering = Ordering.gt

/-- The cycle/tie-safe order succeeds exactly for the canonical safe-order relation. -/
theorem safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder) :
    input.safeLocalizedOccurrenceRule45TrackedOrder?
        target view frame = some tracked ↔
      input.CanonicalSafeLocalizedOccurrenceRule45TrackedOrder
        target view frame tracked := by
  constructor
  · intro computed
    unfold safeLocalizedOccurrenceRule45TrackedOrder? at computed
    cases trackedComputed : input.localizedOccurrenceRule45TrackedOrder?
        target view frame with
    | none => simp [trackedComputed] at computed
    | some observed =>
        cases coherent : input.localizedOccurrenceRule45OrderCoherent?
            target view frame observed.highestFirst with
        | false => simp [trackedComputed, coherent] at computed
        | true =>
            simp [trackedComputed, coherent] at computed
            subst tracked
            have canonicalSort :=
              (input.localizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
                target view frame observed).mp trackedComputed
            have genericSort := canonicalSort.toTracked input target view frame
            refine ⟨canonicalSort, genericSort.perm, ?_⟩
            exact ((input.localizedOccurrenceRule45OrderCoherent?_eq_true_iff
              target view frame observed.highestFirst).mp coherent).imp (by
                rintro left right ⟨result, compared, higher⟩
                exact ⟨result,
                  (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
                    target view frame left right result).mp compared,
                  higher⟩)
  · rintro ⟨canonicalSort, _permutation, coherent⟩
    have trackedComputed :=
      (input.localizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
        target view frame tracked).mpr canonicalSort
    have coherentComputed : input.localizedOccurrenceRule45OrderCoherent?
        target view frame tracked.highestFirst = true :=
      (input.localizedOccurrenceRule45OrderCoherent?_eq_true_iff
        target view frame tracked.highestFirst).mpr (coherent.imp (by
          rintro left right ⟨result, compared, higher⟩
          exact ⟨result,
            (input.compareLocalizedOccurrenceThroughRule5At?_eq_some_iff_canonical
              target view frame left right result).mpr compared,
            higher⟩))
    simp [safeLocalizedOccurrenceRule45TrackedOrder?, trackedComputed, coherentComputed]

/-- Safe-order refusal is exactly absence of a canonical safe order. -/
theorem safeLocalizedOccurrenceRule45TrackedOrder?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame = none ↔
      ¬ ∃ tracked, input.CanonicalSafeLocalizedOccurrenceRule45TrackedOrder
        target view frame tracked := by
  constructor
  · intro computed ⟨tracked, derived⟩
    have successful :=
      (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
        target view frame tracked).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : input.safeLocalizedOccurrenceRule45TrackedOrder?
        target view frame with
    | none => rfl
    | some tracked =>
        exact False.elim (absent ⟨tracked,
          (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
            target view frame tracked).mp computed⟩)

/-! ## Exact coordinates, spatial evidence, and descriptor -/

private theorem mapM_localizedRerootCursorSpatialPoint?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points,
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
          (frame.cursorAt index)) = some points ↔
        List.Forall₂
          (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
            (frame.cursorAt index) point) order points
  | [], points => by
      constructor
      · intro computed
        simp at computed
        subst points
        exact List.Forall₂.nil
      · intro derived
        cases derived
        rfl
  | index :: order, points => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases pointComputed : input.localizedRerootCursorSpatialPoint?
            (frame.cursorAt index) with
        | none => simp [pointComputed] at computed
        | some point =>
            cases tailComputed : order.mapM fun next =>
                input.localizedRerootCursorSpatialPoint? (frame.cursorAt next) with
            | none => simp [pointComputed, tailComputed] at computed
            | some tail =>
                simp [pointComputed, tailComputed] at computed
                subst points
                exact List.Forall₂.cons
                  ((input.localizedRerootCursorSpatialPoint?_eq_some_iff
                    (frame.cursorAt index) point).mp pointComputed)
                  ((input.mapM_localizedRerootCursorSpatialPoint?_eq_some_iff
                    frame order tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            rw [List.mapM_cons,
              (input.localizedRerootCursorSpatialPoint?_eq_some_iff
                (frame.cursorAt index) _).mpr head,
              (input.mapM_localizedRerootCursorSpatialPoint?_eq_some_iff
                frame order _).mpr tail]
            rfl

/-- Canonical meaning of the complete spatial-evidence package. -/
def CanonicalLocalizedOccurrenceRule45SpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel) : Prop :=
  input.RealTetrahedralCenterNode target.1.node evidence.center ∧
    input.DeclarativeLocalizedOccurrenceFourLigandFrame target evidence.frame ∧
    input.CanonicalSafeLocalizedOccurrenceRule45TrackedOrder
      target view evidence.frame evidence.tracked ∧
    List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (evidence.frame.cursorAt index) point)
      evidence.tracked.highestFirst evidence.points

/-- Spatial evidence succeeds exactly for the canonical molecule-backed package. -/
theorem localizedOccurrenceRule45SpatialEvidence?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel) :
    input.localizedOccurrenceRule45SpatialEvidence? target view = some evidence ↔
      input.CanonicalLocalizedOccurrenceRule45SpatialEvidence
        target view evidence := by
  constructor
  · intro computed
    unfold localizedOccurrenceRule45SpatialEvidence? at computed
    cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
    | none => simp [centerComputed] at computed
    | some center =>
        cases frameComputed : input.localizedOccurrenceFourLigandFrame? target with
        | none => simp [centerComputed, frameComputed] at computed
        | some frame =>
            cases trackedComputed : input.safeLocalizedOccurrenceRule45TrackedOrder?
                target view frame with
            | none => simp [centerComputed, frameComputed, trackedComputed] at computed
            | some tracked =>
                cases pointsComputed : tracked.highestFirst.mapM fun index =>
                    input.localizedRerootCursorSpatialPoint? (frame.cursorAt index) with
                | none =>
                    simp [centerComputed, frameComputed, trackedComputed,
                      pointsComputed] at computed
                | some points =>
                    simp [centerComputed, frameComputed, trackedComputed,
                      pointsComputed] at computed
                    subst evidence
                    exact ⟨
                      (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
                        target center).mp centerComputed,
                      (input.localizedOccurrenceFourLigandFrame?_eq_some_iff
                        target frame).mp frameComputed,
                      (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
                        target view frame tracked).mp trackedComputed,
                      (input.mapM_localizedRerootCursorSpatialPoint?_eq_some_iff
                        frame tracked.highestFirst points).mp pointsComputed⟩
  · rintro ⟨centerDerived, frameDerived, trackedDerived, pointsDerived⟩
    have centerComputed :=
      (input.localizedOccurrenceDescriptorCenter?_eq_some_iff
        target evidence.center).mpr centerDerived
    have frameComputed :=
      (input.localizedOccurrenceFourLigandFrame?_eq_some_iff
        target evidence.frame).mpr frameDerived
    have trackedComputed :=
      (input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_some_iff_canonical
        target view evidence.frame evidence.tracked).mpr trackedDerived
    have pointsComputed :=
      (input.mapM_localizedRerootCursorSpatialPoint?_eq_some_iff
        evidence.frame evidence.tracked.highestFirst evidence.points).mpr pointsDerived
    simp [localizedOccurrenceRule45SpatialEvidence?, centerComputed, frameComputed,
      trackedComputed, pointsComputed]

/-- Spatial-evidence refusal is exactly absence of a canonical evidence package. -/
theorem localizedOccurrenceRule45SpatialEvidence?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45SpatialEvidence? target view = none ↔
      ¬ ∃ evidence, input.CanonicalLocalizedOccurrenceRule45SpatialEvidence
        target view evidence := by
  constructor
  · intro computed ⟨evidence, derived⟩
    have successful :=
      (input.localizedOccurrenceRule45SpatialEvidence?_eq_some_iff_canonical
        target view evidence).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : input.localizedOccurrenceRule45SpatialEvidence? target view with
    | none => rfl
    | some evidence =>
        exact False.elim (absent ⟨evidence,
          (input.localizedOccurrenceRule45SpatialEvidence?_eq_some_iff_canonical
            target view evidence).mp computed⟩)

/-- Canonical positive meaning of the final state-relative descriptor. -/
def CanonicalLocalizedOccurrenceRule45Descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    input.CanonicalLocalizedOccurrenceRule45SpatialEvidence target view evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo
      raw evidence.tracked.pseudoComparisons

/-- Final descriptor emission is equivalent to the complete canonical derivation. -/
theorem localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.localizedOccurrenceRule45Descriptor? target view = some descriptor ↔
      input.CanonicalLocalizedOccurrenceRule45Descriptor
        target view descriptor := by
  constructor
  · intro computed
    unfold localizedOccurrenceRule45Descriptor? at computed
    cases evidenceComputed : input.localizedOccurrenceRule45SpatialEvidence?
        target view with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
        | none => simp [evidenceComputed, rawComputed] at computed
        | some raw =>
            simp [evidenceComputed, rawComputed] at computed
            subst descriptor
            exact ⟨evidence, raw,
              (input.localizedOccurrenceRule45SpatialEvidence?_eq_some_iff_canonical
                target view evidence).mp evidenceComputed,
              (descriptorOfPriorityOrderedPoints?_eq_some_iff
                evidence.points raw).mp rawComputed,
              rfl⟩
  · rintro ⟨evidence, raw, evidenceDerived, rawDerived, rfl⟩
    have evidenceComputed :=
      (input.localizedOccurrenceRule45SpatialEvidence?_eq_some_iff_canonical
        target view evidence).mpr evidenceDerived
    have rawComputed :=
      (descriptorOfPriorityOrderedPoints?_eq_some_iff
        evidence.points raw).mpr rawDerived
    simp [localizedOccurrenceRule45Descriptor?, evidenceComputed, rawComputed]

/-- Final refusal is equivalent to absence of any canonical descriptor derivation. -/
theorem localizedOccurrenceRule45Descriptor?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45Descriptor? target view = none ↔
      ¬ ∃ descriptor, input.CanonicalLocalizedOccurrenceRule45Descriptor
        target view descriptor := by
  constructor
  · intro computed ⟨descriptor, derived⟩
    have successful :=
      (input.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
        target view descriptor).mpr derived
    rw [computed] at successful
    contradiction
  · intro absent
    cases computed : input.localizedOccurrenceRule45Descriptor? target view with
    | none => rfl
    | some descriptor =>
        exact False.elim (absent ⟨descriptor,
          (input.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
            target view descriptor).mp computed⟩)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
