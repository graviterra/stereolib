import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Occurrence-local Rules-4a--5 tetrahedral descriptor

This module joins the exact reroot frame, compound no/one/two-reference Rules-4b/4c key, both
Rule-5 readings, tracked stable-sort history, and exact rational geometry.  It is state-relative:
all auxiliary observations are read only through the target's proof-carrying strict-dependency
view.  Successful output has a molecule-backed declarative witness; complete optional-outcome
correspondence and the resulting fixed-point semantics remain a separate next obligation.
-/

namespace CertifiedLocalizedCIPInput

/-- Four exact zipper ligands around one occurrence. -/
structure LocalizedOccurrenceFourLigandFrame
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  cursors : List (input.LocalizedRerootCursor carrierFuel)
  length_eq : cursors.length = 4

/-- Indexed access to the exact four-cursor frame. -/
def LocalizedOccurrenceFourLigandFrame.cursorAt
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) (index : Fin 4) :
    input.LocalizedRerootCursor carrierFuel :=
  frame.cursors.get (Fin.cast frame.length_eq.symm index)

/-- Refuse unless the exact occurrence zipper has four ligand cursors. -/
noncomputable def localizedOccurrenceFourLigandFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedOccurrenceFourLigandFrame carrierFuel) := do
  let cursors ← input.localizedOccurrenceLigandFrame? target
  if length_eq : cursors.length = 4 then
    some { cursors := cursors, length_eq := length_eq }
  else none

/-- Independent exact meaning of a successful four-ligand occurrence frame. -/
def DeclarativeLocalizedOccurrenceFourLigandFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) : Prop :=
  input.DeclarativeLocalizedRerootChildren
      { occurrence := target, previous? := none } frame.cursors ∧
    frame.cursors.length = 4

theorem localizedOccurrenceFourLigandFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame := by
  unfold localizedOccurrenceFourLigandFrame? at computed
  cases cursorsComputed : input.localizedOccurrenceLigandFrame? target with
  | none => simp [cursorsComputed] at computed
  | some cursors =>
      by_cases length_eq : cursors.length = 4
      · simp [cursorsComputed, length_eq] at computed
        subst frame
        exact ⟨input.localizedOccurrenceLigandFrame?_sound
          target cursors cursorsComputed, length_eq⟩
      · simp [cursorsComputed, length_eq] at computed

/-- Successful four-ligand frame construction is exactly the independent ordered zipper relation
plus cardinality four. -/
theorem localizedOccurrenceFourLigandFrame?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    input.localizedOccurrenceFourLigandFrame? target = some frame ↔
      input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame := by
  constructor
  · exact input.localizedOccurrenceFourLigandFrame?_sound target frame
  · intro derived
    unfold localizedOccurrenceFourLigandFrame?
    have cursorsComputed : input.localizedOccurrenceLigandFrame? target =
        some frame.cursors :=
      (input.localizedOccurrenceLigandFrame?_eq_some_iff
        target frame.cursors).mpr derived.1
    rw [cursorsComputed]
    simp [frame.length_eq]

/-- Conservative reroot evaluation bound.  Every use is fail-closed, so soundness does not assume
that this bound succeeds.  Proving completeness of this bound for every carrier cursor is part of
the complete optional-outcome correspondence obligation. -/
def localizedOccurrenceRerootEvaluationFuel (carrierFuel : Nat) : Nat :=
  2 * (carrierFuel + 1)

/-- Adapt the through-Rule-5 result to the tracked classifier's comparison record. -/
def localizedOccurrenceRule45ComparisonRecord
    (result : ConstitutionalRule5Comparison) :
    ConstitutionalDescriptorHierarchyComparison :=
  { ordering := result.ordering, pseudo := result.pseudo }

/-- Complete state-relative comparison of two indexed occurrence ligands. -/
noncomputable def compareLocalizedOccurrenceThroughRule5At?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) : Option ConstitutionalDescriptorHierarchyComparison := do
  let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let leftKey ← input.buildLocalizedRerootCompoundRule45Key?
    target view fuel (frame.cursorAt left)
  let rightKey ← input.buildLocalizedRerootCompoundRule45Key?
    target view fuel (frame.cursorAt right)
  some (localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))

/-- Independent pairwise comparison witness. -/
def DeclarativeLocalizedOccurrenceThroughRule5At
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison) : Prop :=
  ∃ leftKey rightKey,
    input.DeclarativeLocalizedRerootCompoundThroughRule5 target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) (frame.cursorAt right) leftKey rightKey
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey) ∧
    result = localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey)

theorem compareLocalizedOccurrenceThroughRule5At?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) (result : ConstitutionalDescriptorHierarchyComparison)
    (computed : input.compareLocalizedOccurrenceThroughRule5At?
      target view frame left right = some result) :
    input.DeclarativeLocalizedOccurrenceThroughRule5At
      target view frame left right result := by
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
            input.compareLocalizedRerootCompoundThroughRule5_sound target view
              (localizedOccurrenceRerootEvaluationFuel carrierFuel)
              (frame.cursorAt left) (frame.cursorAt right)
              leftKey rightKey leftComputed rightComputed,
            rfl⟩

/-! ## Independent tracked sort -/

inductive DeclarativeLocalizedOccurrenceRule45Insertion
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (candidate : Fin 4) :
    List (Fin 4) → TrackedLocalizedLigandInsertion → Prop
  | nil : DeclarativeLocalizedOccurrenceRule45Insertion
      input target view frame candidate []
      { lowestFirst := [candidate], pseudoComparisons := 0 }
  | placeBefore {low remaining comparison}
      (compared : input.DeclarativeLocalizedOccurrenceThroughRule5At
        target view frame low candidate comparison)
      (higherLow : comparison.ordering = Ordering.gt) :
      DeclarativeLocalizedOccurrenceRule45Insertion input target view frame candidate
        (low :: remaining)
        { lowestFirst := candidate :: low :: remaining
          pseudoComparisons := if comparison.pseudo then 1 else 0 }
  | placeAfter {low remaining comparison deeper}
      (compared : input.DeclarativeLocalizedOccurrenceThroughRule5At
        target view frame low candidate comparison)
      (lowerLow : comparison.ordering = Ordering.lt)
      (tail : DeclarativeLocalizedOccurrenceRule45Insertion
        input target view frame candidate remaining deeper) :
      DeclarativeLocalizedOccurrenceRule45Insertion input target view frame candidate
        (low :: remaining)
        { lowestFirst := low :: deeper.lowestFirst
          pseudoComparisons :=
            (if comparison.pseudo then 1 else 0) + deeper.pseudoComparisons }

theorem DeclarativeTrackedLocalizedLigandInsertion.toOccurrenceRule45
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    {candidate : Fin 4} {existing : List (Fin 4)}
    {result : TrackedLocalizedLigandInsertion}
    (derived : DeclarativeTrackedLocalizedLigandInsertion
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      candidate existing result) :
    input.DeclarativeLocalizedOccurrenceRule45Insertion
      target view frame candidate existing result := by
  induction derived with
  | nil => exact DeclarativeLocalizedOccurrenceRule45Insertion.nil
  | placeBefore compared higherLow =>
      exact DeclarativeLocalizedOccurrenceRule45Insertion.placeBefore
        (input.compareLocalizedOccurrenceThroughRule5At?_sound
          target view frame _ _ _ compared) higherLow
  | placeAfter compared lowerLow tail inductionHypothesis =>
      exact DeclarativeLocalizedOccurrenceRule45Insertion.placeAfter
        (input.compareLocalizedOccurrenceThroughRule5At?_sound
          target view frame _ _ _ compared) lowerLow inductionHypothesis

inductive DeclarativeLocalizedOccurrenceRule45Sort
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    List (Fin 4) → List (Fin 4) → Nat → TrackedLocalizedLigandOrder → Prop
  | nil (lowestFirst : List (Fin 4)) (pseudoComparisons : Nat) :
      DeclarativeLocalizedOccurrenceRule45Sort input target view frame []
        lowestFirst pseudoComparisons
        { highestFirst := lowestFirst.reverse
          pseudoComparisons := pseudoComparisons }
  | cons {candidate candidates lowestFirst pseudoComparisons inserted result}
      (insertion : input.DeclarativeLocalizedOccurrenceRule45Insertion
        target view frame candidate lowestFirst inserted)
      (tail : DeclarativeLocalizedOccurrenceRule45Sort input target view frame
        candidates inserted.lowestFirst
        (pseudoComparisons + inserted.pseudoComparisons) result) :
      DeclarativeLocalizedOccurrenceRule45Sort input target view frame
        (candidate :: candidates) lowestFirst pseudoComparisons result

theorem DeclarativeTrackedLocalizedLigandSort.toOccurrenceRule45
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    {candidates lowestFirst : List (Fin 4)} {pseudoComparisons : Nat}
    {result : TrackedLocalizedLigandOrder}
    (derived : DeclarativeTrackedLocalizedLigandSort
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
      candidates lowestFirst pseudoComparisons result) :
    input.DeclarativeLocalizedOccurrenceRule45Sort target view frame
      candidates lowestFirst pseudoComparisons result := by
  induction derived with
  | nil lowestFirst pseudoComparisons =>
      exact DeclarativeLocalizedOccurrenceRule45Sort.nil
        lowestFirst pseudoComparisons
  | cons insertion tail inductionHypothesis =>
      exact DeclarativeLocalizedOccurrenceRule45Sort.cons
        (DeclarativeTrackedLocalizedLigandInsertion.toOccurrenceRule45
          input target view frame insertion) inductionHypothesis

/-- Proposed stable order before the all-pairs coherence check. -/
noncomputable def localizedOccurrenceRule45TrackedOrder?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder :=
  sortFourLocalizedLigandsTracked
    (input.compareLocalizedOccurrenceThroughRule5At? target view frame)

/-- Strict all-pairs check rejects cycles and hidden nonadjacent ties. -/
noncomputable def localizedOccurrenceRule45OrderPairStrict?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) : Bool :=
  match input.compareLocalizedOccurrenceThroughRule5At?
      target view frame left right with
  | none => false
  | some result => result.ordering == Ordering.gt

noncomputable def localizedOccurrenceRule45OrderCoherent?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    List (Fin 4) → Bool
  | [] => true
  | left :: rest =>
      rest.all (input.localizedOccurrenceRule45OrderPairStrict?
        target view frame left) &&
      input.localizedOccurrenceRule45OrderCoherent? target view frame rest

@[simp] theorem localizedOccurrenceRule45OrderPairStrict?_eq_true_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4) :
    input.localizedOccurrenceRule45OrderPairStrict?
        target view frame left right = true ↔
      ∃ result,
        input.compareLocalizedOccurrenceThroughRule5At?
          target view frame left right = some result ∧
        result.ordering = Ordering.gt := by
  cases computed : input.compareLocalizedOccurrenceThroughRule5At?
      target view frame left right with
  | none => simp [localizedOccurrenceRule45OrderPairStrict?, computed]
  | some result => simp [localizedOccurrenceRule45OrderPairStrict?, computed]

theorem localizedOccurrenceRule45OrderCoherent?_eq_true_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order,
      input.localizedOccurrenceRule45OrderCoherent?
          target view frame order = true ↔
        order.Pairwise fun left right =>
          ∃ result,
            input.compareLocalizedOccurrenceThroughRule5At?
              target view frame left right = some result ∧
            result.ordering = Ordering.gt
  | [] => by simp [localizedOccurrenceRule45OrderCoherent?]
  | left :: rest => by
      rw [localizedOccurrenceRule45OrderCoherent?, Bool.and_eq_true,
        List.all_eq_true, List.pairwise_cons,
        localizedOccurrenceRule45OrderCoherent?_eq_true_iff]
      constructor
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (input.localizedOccurrenceRule45OrderPairStrict?_eq_true_iff
            target view frame left right).mp (head right present), tail⟩
      · rintro ⟨head, tail⟩
        exact ⟨fun right present =>
          (input.localizedOccurrenceRule45OrderPairStrict?_eq_true_iff
            target view frame left right).mpr (head right present), tail⟩

/-- Tracked order after every earlier/later pair is checked. -/
noncomputable def safeLocalizedOccurrenceRule45TrackedOrder?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder := do
  let tracked ← input.localizedOccurrenceRule45TrackedOrder? target view frame
  if input.localizedOccurrenceRule45OrderCoherent?
      target view frame tracked.highestFirst then some tracked else none

/-- Independent safe-order relation with exact comparison history and all-pairs witnesses. -/
def DeclarativeSafeLocalizedOccurrenceRule45TrackedOrder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder) : Prop :=
  input.DeclarativeLocalizedOccurrenceRule45Sort target view frame
      (List.finRange 4) [] 0 tracked ∧
    tracked.highestFirst.Perm (List.finRange 4) ∧
    tracked.highestFirst.Pairwise fun left right =>
      ∃ result,
        input.DeclarativeLocalizedOccurrenceThroughRule5At
          target view frame left right result ∧
        result.ordering = Ordering.gt

theorem safeLocalizedOccurrenceRule45TrackedOrder?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : input.safeLocalizedOccurrenceRule45TrackedOrder?
      target view frame = some tracked) :
    input.DeclarativeSafeLocalizedOccurrenceRule45TrackedOrder
      target view frame tracked := by
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
          have genericSort := sortFourLocalizedLigandsTracked_sound
            (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
            observed trackedComputed
          refine ⟨DeclarativeTrackedLocalizedLigandSort.toOccurrenceRule45
              input target view frame genericSort,
            sortFourLocalizedLigandsTracked_perm
              (input.compareLocalizedOccurrenceThroughRule5At? target view frame)
              observed trackedComputed, ?_⟩
          exact ((input.localizedOccurrenceRule45OrderCoherent?_eq_true_iff
            target view frame observed.highestFirst).mp coherent).imp (by
              rintro left right ⟨result, compared, higher⟩
              exact ⟨result,
                input.compareLocalizedOccurrenceThroughRule5At?_sound
                  target view frame left right result compared,
                higher⟩)

/-! ## Exact occurrence geometry and final case -/

/-- Coordinate lookup for the current real atom at one reroot ligand cursor. -/
def localizedRerootCursorSpatialPoint?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) : Option CartesianPoint3 := do
  let atom ← cursor.occurrence.1.node.current?
  input.spatialPointAt? atom

def DeclarativeLocalizedRerootCursorSpatialPoint
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (point : CartesianPoint3) : Prop :=
  ∃ atom,
    cursor.occurrence.1.node.current? = some atom ∧
    input.SemanticSpatialPointAt atom point

theorem localizedRerootCursorSpatialPoint?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (point : CartesianPoint3) :
    input.localizedRerootCursorSpatialPoint? cursor = some point ↔
      input.DeclarativeLocalizedRerootCursorSpatialPoint cursor point := by
  unfold localizedRerootCursorSpatialPoint?
    DeclarativeLocalizedRerootCursorSpatialPoint
  cases atomComputed : cursor.occurrence.1.node.current? with
  | none => simp
  | some atom =>
      simp [input.spatialPointAt?_eq_some_iff atom point]

structure LocalizedOccurrenceRule45SpatialEvidence
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  center : input.TetrahedralCenter
  frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel
  tracked : TrackedLocalizedLigandOrder
  points : List CartesianPoint3

noncomputable def localizedOccurrenceRule45SpatialEvidence?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let frame ← input.localizedOccurrenceFourLigandFrame? target
  let tracked ← input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (frame.cursorAt index)
  some { center := center, frame := frame, tracked := tracked, points := points }

private theorem mapM_localizedRerootCursorSpatialPoint?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    ∀ order points,
      order.mapM (fun index => input.localizedRerootCursorSpatialPoint?
        (frame.cursorAt index)) = some points →
      List.Forall₂
        (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
          (frame.cursorAt index) point) order points
  | [], points, computed => by
      simp at computed
      subst points
      exact List.Forall₂.nil
  | index :: order, points, computed => by
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
                (input.mapM_localizedRerootCursorSpatialPoint?_sound
                  frame order tail tailComputed)

def DeclarativeLocalizedOccurrenceRule45SpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel) : Prop :=
  input.RealTetrahedralCenterNode target.1.node evidence.center ∧
    input.DeclarativeLocalizedOccurrenceFourLigandFrame target evidence.frame ∧
    input.DeclarativeSafeLocalizedOccurrenceRule45TrackedOrder
      target view evidence.frame evidence.tracked ∧
    List.Forall₂
      (fun index point => input.DeclarativeLocalizedRerootCursorSpatialPoint
        (evidence.frame.cursorAt index) point)
      evidence.tracked.highestFirst evidence.points

theorem localizedOccurrenceRule45SpatialEvidence?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evidence : input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel)
    (computed : input.localizedOccurrenceRule45SpatialEvidence?
      target view = some evidence) :
    input.DeclarativeLocalizedOccurrenceRule45SpatialEvidence
      target view evidence := by
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
                    input.localizedOccurrenceFourLigandFrame?_sound
                      target frame frameComputed,
                    input.safeLocalizedOccurrenceRule45TrackedOrder?_sound
                      target view frame tracked trackedComputed,
                    input.mapM_localizedRerootCursorSpatialPoint?_sound
                      frame tracked.highestFirst points pointsComputed⟩

/-- State-relative occurrence descriptor through Rules 4a--5. -/
noncomputable def localizedOccurrenceRule45Descriptor?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.localizedOccurrenceRule45SpatialEvidence? target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- Independent positive descriptor relation for the state-relative occurrence evaluator. -/
def DeclarativeLocalizedOccurrenceRule45Descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    input.DeclarativeLocalizedOccurrenceRule45SpatialEvidence target view evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo
      raw evidence.tracked.pseudoComparisons

theorem localizedOccurrenceRule45Descriptor?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceRule45Descriptor?
      target view = some descriptor) :
    input.DeclarativeLocalizedOccurrenceRule45Descriptor
      target view descriptor := by
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
            input.localizedOccurrenceRule45SpatialEvidence?_sound
              target view evidence evidenceComputed,
            (descriptorOfPriorityOrderedPoints?_eq_some_iff
              evidence.points raw).mp rawComputed,
            rfl⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
