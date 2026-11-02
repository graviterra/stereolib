import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6PromotedKey
import TetraStereo.OneCenter.CIPAuthoritativeRule6P92Enumeration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open Rule6ReferenceFamilySemantics
open AuthoritativeCIPRule6P92Enumeration

/-!
# Rule-3-aware source-canonical Rule-6 backend

The backend in this file resolves the complete four-ligand Rule-3 physical topology before any
Rule-6 reference is tried.  Every ranking then uses the strengthened recursive key, so a Rule-6
promotion can never override Rules 1a--5 at the root or in a descendant reranking.
-/

structure AromaticCanonicalRule3Through6IndexedKey
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  cursor : source.AromaticCanonicalRerootCursor carrierFuel
  position : Nat
  key : source.AromaticCanonicalRule3Through6PromotedKey

/-- The trace bit is true exactly when Rule 6 breaks a complete Rules-1a--5 tie. -/
noncomputable def compareAromaticCanonicalRule3Through6IndexedKeys
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) :
    Rule6TrackedDecision :=
  let prior := source.compareAromaticCanonicalOccurrenceRule3Through5Keys
    left.key.prior right.key.prior
  let ordering := source.compareAromaticCanonicalRule3Through6PromotedKeys
    left.key right.key
  { ordering := ordering
    pseudo := prior = Ordering.eq ∧ ordering ≠ Ordering.eq }

theorem compareAromaticCanonicalRule3Through6IndexedKeys_ordering
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) :
    (source.compareAromaticCanonicalRule3Through6IndexedKeys left right).ordering =
      source.compareAromaticCanonicalRule3Through6PromotedKeys left.key right.key := by
  rfl

theorem compareAromaticCanonicalRule3Through6IndexedKeys_pseudo_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) :
    (source.compareAromaticCanonicalRule3Through6IndexedKeys left right).pseudo ↔
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys
          left.key.prior right.key.prior = Ordering.eq ∧
        source.compareAromaticCanonicalRule3Through6PromotedKeys
          left.key right.key ≠ Ordering.eq := by
  simp [compareAromaticCanonicalRule3Through6IndexedKeys]

structure AromaticCanonicalRule3Through6IndexedInsertion
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  entries : List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)
  rule6Comparisons : Nat
  unique : Bool

/-- Descending stable insertion with an exact count of Rule-6-dependent comparisons. -/
noncomputable def insertAromaticCanonicalRule3Through6IndexedKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) :
    List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule3Through6IndexedInsertion carrierFuel
  | [] => { entries := [candidate], rule6Comparisons := 0, unique := true }
  | low :: remaining =>
      let decision := source.compareAromaticCanonicalRule3Through6IndexedKeys candidate low
      let observed := if decision.pseudo then 1 else 0
      match decision.ordering with
      | .lt =>
          let deeper := source.insertAromaticCanonicalRule3Through6IndexedKey
            candidate remaining
          { entries := low :: deeper.entries
            rule6Comparisons := observed + deeper.rule6Comparisons
            unique := deeper.unique }
      | .eq =>
          { entries := candidate :: low :: remaining
            rule6Comparisons := observed
            unique := false }
      | .gt =>
          { entries := candidate :: low :: remaining
            rule6Comparisons := observed
            unique := true }

structure AromaticCanonicalRule3Through6IndexedSort
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  entries : List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)
  rule6Comparisons : Nat
  unique : Bool

noncomputable def sortAromaticCanonicalRule3Through6IndexedKeys
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule3Through6IndexedSort carrierFuel
  | [] => { entries := [], rule6Comparisons := 0, unique := true }
  | candidate :: remaining =>
      let sorted := source.sortAromaticCanonicalRule3Through6IndexedKeys remaining
      let inserted := source.insertAromaticCanonicalRule3Through6IndexedKey
        candidate sorted.entries
      { entries := inserted.entries
        rule6Comparisons := sorted.rule6Comparisons + inserted.rule6Comparisons
        unique := sorted.unique && inserted.unique }

inductive DeclarativeAromaticCanonicalRule3Through6IndexedInsertion
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) :
    List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule3Through6IndexedInsertion carrierFuel → Prop
  | nil :
      source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion candidate []
        { entries := [candidate], rule6Comparisons := 0, unique := true }
  | placeAfter {low remaining deeper}
      (lower : (source.compareAromaticCanonicalRule3Through6IndexedKeys
        candidate low).ordering = Ordering.lt)
      (tail : source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion
        candidate remaining deeper) :
      source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion
        candidate (low :: remaining)
          { entries := low :: deeper.entries
            rule6Comparisons :=
              (if (source.compareAromaticCanonicalRule3Through6IndexedKeys
                candidate low).pseudo then 1 else 0) + deeper.rule6Comparisons
            unique := deeper.unique }
  | tie {low remaining}
      (equal : (source.compareAromaticCanonicalRule3Through6IndexedKeys
        candidate low).ordering = Ordering.eq) :
      source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion
        candidate (low :: remaining)
          { entries := candidate :: low :: remaining
            rule6Comparisons :=
              if (source.compareAromaticCanonicalRule3Through6IndexedKeys
                candidate low).pseudo then 1 else 0
            unique := false }
  | placeBefore {low remaining}
      (higher : (source.compareAromaticCanonicalRule3Through6IndexedKeys
        candidate low).ordering = Ordering.gt) :
      source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion
        candidate (low :: remaining)
          { entries := candidate :: low :: remaining
            rule6Comparisons :=
              if (source.compareAromaticCanonicalRule3Through6IndexedKeys
                candidate low).pseudo then 1 else 0
            unique := true }

theorem insertAromaticCanonicalRule3Through6IndexedKey_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) :
    ∀ entries,
      source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion candidate entries
        (source.insertAromaticCanonicalRule3Through6IndexedKey candidate entries)
  | [] => .nil
  | low :: remaining => by
      generalize decisionEq :
        source.compareAromaticCanonicalRule3Through6IndexedKeys candidate low = decision
      cases comparison : decision.ordering with
      | lt =>
          have lower :
              (source.compareAromaticCanonicalRule3Through6IndexedKeys
                candidate low).ordering = Ordering.lt := by
            rw [decisionEq]
            exact comparison
          simpa [insertAromaticCanonicalRule3Through6IndexedKey,
              decisionEq, comparison] using
            (DeclarativeAromaticCanonicalRule3Through6IndexedInsertion.placeAfter lower
              (source.insertAromaticCanonicalRule3Through6IndexedKey_sound
                candidate remaining))
      | eq =>
          have equal :
              (source.compareAromaticCanonicalRule3Through6IndexedKeys
                candidate low).ordering = Ordering.eq := by
            rw [decisionEq]
            exact comparison
          simpa [insertAromaticCanonicalRule3Through6IndexedKey,
              decisionEq, comparison] using
            (DeclarativeAromaticCanonicalRule3Through6IndexedInsertion.tie
              (remaining := remaining) equal)
      | gt =>
          have higher :
              (source.compareAromaticCanonicalRule3Through6IndexedKeys
                candidate low).ordering = Ordering.gt := by
            rw [decisionEq]
            exact comparison
          simpa [insertAromaticCanonicalRule3Through6IndexedKey,
              decisionEq, comparison] using
            (DeclarativeAromaticCanonicalRule3Through6IndexedInsertion.placeBefore
              (remaining := remaining) higher)

theorem DeclarativeAromaticCanonicalRule3Through6IndexedInsertion.perm
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    {candidate : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel}
    {entries : List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)}
    {inserted : source.AromaticCanonicalRule3Through6IndexedInsertion carrierFuel}
    (derivation : source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion
      candidate entries inserted) :
    inserted.entries.Perm (candidate :: entries) := by
  induction derivation with
  | nil => exact List.Perm.refl _
  | tie => exact List.Perm.refl _
  | placeBefore => exact List.Perm.refl _
  | placeAfter _ _ inductionHypothesis =>
      exact (List.Perm.cons _ inductionHypothesis).trans
        (List.Perm.swap _ _ _)

inductive DeclarativeAromaticCanonicalRule3Through6IndexedSort
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule3Through6IndexedSort carrierFuel → Prop
  | nil : source.DeclarativeAromaticCanonicalRule3Through6IndexedSort []
      { entries := [], rule6Comparisons := 0, unique := true }
  | cons {candidate remaining sorted inserted}
      (tail : source.DeclarativeAromaticCanonicalRule3Through6IndexedSort
        remaining sorted)
      (insertion : source.DeclarativeAromaticCanonicalRule3Through6IndexedInsertion
        candidate sorted.entries inserted) :
      source.DeclarativeAromaticCanonicalRule3Through6IndexedSort
        (candidate :: remaining)
          { entries := inserted.entries
            rule6Comparisons := sorted.rule6Comparisons + inserted.rule6Comparisons
            unique := sorted.unique && inserted.unique }

theorem sortAromaticCanonicalRule3Through6IndexedKeys_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    ∀ entries : List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel),
      source.DeclarativeAromaticCanonicalRule3Through6IndexedSort entries
        (source.sortAromaticCanonicalRule3Through6IndexedKeys entries)
  | [] => .nil
  | candidate :: remaining => by
      unfold sortAromaticCanonicalRule3Through6IndexedKeys
      exact .cons
        (source.sortAromaticCanonicalRule3Through6IndexedKeys_sound remaining)
        (source.insertAromaticCanonicalRule3Through6IndexedKey_sound candidate
          (source.sortAromaticCanonicalRule3Through6IndexedKeys remaining).entries)

theorem DeclarativeAromaticCanonicalRule3Through6IndexedSort.perm
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    {entries : List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)}
    {sorted : source.AromaticCanonicalRule3Through6IndexedSort carrierFuel}
    (derivation : source.DeclarativeAromaticCanonicalRule3Through6IndexedSort
      entries sorted) :
    sorted.entries.Perm entries := by
  induction derivation with
  | nil => exact List.Perm.refl []
  | cons tail insertion inductionHypothesis =>
      exact insertion.perm.trans (List.Perm.cons _ inductionHypothesis)

/-- Compile one strengthened key and retain its original frame position. -/
noncomputable def buildAromaticCanonicalRule3Through6IndexedKey?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat) :
    source.AromaticCanonicalRerootCursor carrierFuel × Nat →
      Option (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)
  | (cursor, position) => do
      let key ← source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel cursor
      some { cursor, position, key }

def DeclarativeAromaticCanonicalRule3Through6IndexedKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat)
    (input : source.AromaticCanonicalRerootCursor carrierFuel × Nat)
    (output : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel) : Prop :=
  output.cursor = input.1 ∧ output.position = input.2 ∧
    source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
      excluded target view reference fuel input.1 output.key

theorem buildAromaticCanonicalRule3Through6IndexedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat)
    (input : source.AromaticCanonicalRerootCursor carrierFuel × Nat)
    (output : source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)
    (computed : source.buildAromaticCanonicalRule3Through6IndexedKey?
      excluded target view reference fuel input = some output) :
    source.DeclarativeAromaticCanonicalRule3Through6IndexedKey
      excluded target view reference fuel input output := by
  rcases input with ⟨cursor, position⟩
  unfold buildAromaticCanonicalRule3Through6IndexedKey? at computed
  cases keyComputed : source.buildAromaticCanonicalRule3Through6PromotedKey?
      excluded target view reference fuel cursor with
  | none => simp [keyComputed] at computed
  | some key =>
      simp [keyComputed] at computed
      subst output
      exact ⟨rfl, rfl,
        source.buildAromaticCanonicalRule3Through6PromotedKey?_sound
          excluded target view reference fuel cursor key keyComputed⟩

private theorem mapM_buildAromaticCanonicalRule3Through6IndexedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat) :
    ∀ inputs outputs,
      inputs.mapM (source.buildAromaticCanonicalRule3Through6IndexedKey?
        excluded target view reference fuel) = some outputs →
      List.Forall₂
        (source.DeclarativeAromaticCanonicalRule3Through6IndexedKey
          excluded target view reference fuel) inputs outputs
  | [], outputs, computed => by
      simp at computed
      subst outputs
      exact .nil
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalRule3Through6IndexedKey?
          excluded target view reference fuel input with
      | none => simp [headComputed] at computed
      | some output =>
          cases tailComputed : inputs.mapM
              (source.buildAromaticCanonicalRule3Through6IndexedKey?
                excluded target view reference fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              exact .cons
                (source.buildAromaticCanonicalRule3Through6IndexedKey?_sound
                  excluded target view reference fuel input output headComputed)
                (mapM_buildAromaticCanonicalRule3Through6IndexedKey?_sound
                  source excluded target view reference fuel inputs tail tailComputed)

theorem DeclarativeAromaticCanonicalRule3Through6IndexedKeys.positions
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {view : source.AromaticCanonicalDependencyView target}
    {reference : source.AromaticCanonicalAtom}
    {inputs : List (source.AromaticCanonicalRerootCursor carrierFuel × Nat)}
    {outputs : List (source.AromaticCanonicalRule3Through6IndexedKey carrierFuel)}
    (derived : List.Forall₂
      (source.DeclarativeAromaticCanonicalRule3Through6IndexedKey
        excluded target view reference fuel) inputs outputs) :
    outputs.map (fun entry => entry.position) = inputs.map Prod.snd := by
  induction derived with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [head.2.1, inductionHypothesis]

/-- Ranking backend specialized to an already resolved physical-topology frame.  This is the
single-frame entry point used by a final scheduler so initial and promoted comparisons share the
same exclusion set by construction. -/
noncomputable def aromaticCanonicalRule3Through6RankingBackendForFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    ProductionRule6RankingBackend :=
  fun referencePosition => do
    if _rootsLength : roots.length = 4 then
      if _frameLength : frame.keys.length = 4 then
        let referenceCursor ← roots[referencePosition]?
        let reference ← referenceCursor.occurrence.1.node.current?
        let entries ← roots.zipIdx.mapM
          (source.buildAromaticCanonicalRule3Through6IndexedKey?
            frame.excluded target view reference fuel)
        let sorted := source.sortAromaticCanonicalRule3Through6IndexedKeys entries
        some
          { positions := sorted.entries.map fun entry => entry.position
            pseudoComparisons := sorted.rule6Comparisons
            unique := sorted.unique }
      else none
    else none

/-- Concrete Rule-6 backend with one proved four-ligand physical-topology frame per ranking. -/
noncomputable def aromaticCanonicalRule3Through6RankingBackend
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    ProductionRule6RankingBackend :=
  fun referencePosition => do
    if _rootsLength : roots.length = 4 then
      let frame ← source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel roots
      if _frameLength : frame.keys.length = 4 then
        let referenceCursor ← roots[referencePosition]?
        let reference ← referenceCursor.occurrence.1.node.current?
        let entries ← roots.zipIdx.mapM
          (source.buildAromaticCanonicalRule3Through6IndexedKey?
            frame.excluded target view reference fuel)
        let sorted := source.sortAromaticCanonicalRule3Through6IndexedKeys entries
        some
          { positions := sorted.entries.map fun entry => entry.position
            pseudoComparisons := sorted.rule6Comparisons
            unique := sorted.unique }
      else none
    else none

/-- Every successful ranking from a resolved four-root frame contains each source position
exactly once.  This invariant depends only on indexed compilation and the tracked sort, not on
how the physical-topology frame was obtained. -/
theorem aromaticCanonicalRule3Through6RankingBackendForFrame_positions_perm
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat) (ranking : Rule6TrackedRanking)
    (computed : source.aromaticCanonicalRule3Through6RankingBackendForFrame
      frame target view fuel roots referencePosition = some ranking) :
    ranking.positions.Perm (List.range 4) := by
  unfold aromaticCanonicalRule3Through6RankingBackendForFrame at computed
  by_cases rootsLength : roots.length = 4
  · by_cases frameLength : frame.keys.length = 4
    · cases referenceCursorComputed : roots[referencePosition]? with
      | none =>
          simp [rootsLength, frameLength, referenceCursorComputed] at computed
      | some referenceCursor =>
          cases referenceComputed : referenceCursor.occurrence.1.node.current? with
          | none =>
              simp [rootsLength, frameLength, referenceCursorComputed,
                referenceComputed] at computed
          | some reference =>
              cases entriesComputed : roots.zipIdx.mapM
                  (source.buildAromaticCanonicalRule3Through6IndexedKey?
                    frame.excluded target view reference fuel) with
              | none =>
                  simp [rootsLength, frameLength, referenceCursorComputed,
                    referenceComputed, entriesComputed] at computed
              | some entries =>
                  let sorted := source.sortAromaticCanonicalRule3Through6IndexedKeys entries
                  simp [rootsLength, frameLength, referenceCursorComputed,
                    referenceComputed, entriesComputed] at computed
                  subst ranking
                  have compiled :=
                    mapM_buildAromaticCanonicalRule3Through6IndexedKey?_sound
                      source frame.excluded target view reference fuel
                      roots.zipIdx entries entriesComputed
                  have sortedDerivation :=
                    source.sortAromaticCanonicalRule3Through6IndexedKeys_sound entries
                  have sortedPerm :=
                    sortedDerivation.perm.map (fun entry => entry.position)
                  have compiledPositions :=
                    DeclarativeAromaticCanonicalRule3Through6IndexedKeys.positions compiled
                  rw [compiledPositions] at sortedPerm
                  simpa [List.range_eq_range', rootsLength] using sortedPerm
    · simp [rootsLength, frameLength] at computed
  · simp [rootsLength] at computed

/-- Resolving the frame outside the backend gives exactly the same reference ranking. -/
theorem aromaticCanonicalRule3Through6RankingBackend_eq_forFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (rootsLength : roots.length = 4) (frameLength : frame.keys.length = 4)
    (frameComputed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      fuel roots = some frame) :
    source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots =
      source.aromaticCanonicalRule3Through6RankingBackendForFrame
        frame target view fuel roots := by
  funext referencePosition
  simp [aromaticCanonicalRule3Through6RankingBackend,
    aromaticCanonicalRule3Through6RankingBackendForFrame,
    rootsLength, frameLength, frameComputed]

/-- Independent meaning of one successful Rule-3-aware ranking. -/
def DeclarativeAromaticCanonicalRule3Through6Ranking
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat) (ranking : Rule6TrackedRanking) : Prop :=
  ∃ frame referenceCursor reference entries sorted,
    roots.length = 4 ∧
      source.DeclarativeAromaticCanonicalRule3CanonicalKeyFrame fuel roots frame ∧
      frame.keys.length = 4 ∧
      roots[referencePosition]? = some referenceCursor ∧
      referenceCursor.occurrence.1.node.current? = some reference ∧
      List.Forall₂
        (source.DeclarativeAromaticCanonicalRule3Through6IndexedKey
          frame.excluded target view reference fuel) roots.zipIdx entries ∧
      source.DeclarativeAromaticCanonicalRule3Through6IndexedSort entries sorted ∧
      ranking.positions = sorted.entries.map (fun entry => entry.position) ∧
      ranking.pseudoComparisons = sorted.rule6Comparisons ∧
      ranking.unique = sorted.unique

theorem aromaticCanonicalRule3Through6RankingBackend_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat) (ranking : Rule6TrackedRanking)
    (computed : source.aromaticCanonicalRule3Through6RankingBackend
      target view fuel roots referencePosition = some ranking) :
    source.DeclarativeAromaticCanonicalRule3Through6Ranking
      target view fuel roots referencePosition ranking := by
  unfold aromaticCanonicalRule3Through6RankingBackend at computed
  by_cases rootsLength : roots.length = 4
  · cases frameComputed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
        fuel roots with
    | none => simp [rootsLength, frameComputed] at computed
    | some frame =>
        by_cases frameLength : frame.keys.length = 4
        · cases referenceCursorComputed : roots[referencePosition]? with
          | none =>
              simp [rootsLength, frameComputed,
                referenceCursorComputed] at computed
          | some referenceCursor =>
              cases referenceComputed : referenceCursor.occurrence.1.node.current? with
              | none =>
                  simp [rootsLength, frameComputed,
                    referenceCursorComputed, referenceComputed] at computed
              | some reference =>
                  cases entriesComputed : roots.zipIdx.mapM
                      (source.buildAromaticCanonicalRule3Through6IndexedKey?
                        frame.excluded target view reference fuel) with
                  | none =>
                      simp [rootsLength, frameComputed, frameLength,
                        referenceCursorComputed, referenceComputed,
                        entriesComputed] at computed
                  | some entries =>
                      let sorted :=
                        source.sortAromaticCanonicalRule3Through6IndexedKeys entries
                      simp [rootsLength, frameComputed, frameLength,
                        referenceCursorComputed, referenceComputed,
                        entriesComputed] at computed
                      subst ranking
                      exact ⟨frame, referenceCursor, reference, entries, sorted,
                        rootsLength,
                        source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
                          fuel roots frame frameComputed,
                        frameLength, referenceCursorComputed, referenceComputed,
                        mapM_buildAromaticCanonicalRule3Through6IndexedKey?_sound
                          source frame.excluded target view reference fuel
                          roots.zipIdx entries entriesComputed,
                        source.sortAromaticCanonicalRule3Through6IndexedKeys_sound entries,
                        rfl, rfl, rfl⟩
        · simp [rootsLength, frameComputed, frameLength] at computed
  · simp [rootsLength] at computed

/-- Every successful ranking contains each of the four source positions exactly once. -/
theorem aromaticCanonicalRule3Through6RankingBackend_positions_perm
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat) (ranking : Rule6TrackedRanking)
    (computed : source.aromaticCanonicalRule3Through6RankingBackend
      target view fuel roots referencePosition = some ranking) :
    ranking.positions.Perm (List.range 4) := by
  rcases source.aromaticCanonicalRule3Through6RankingBackend_sound
      target view fuel roots referencePosition ranking computed with
    ⟨frame, _referenceCursor, _reference, entries, sorted, rootsLength,
      _frameDerived, _frameLength, _lookup, _current, compiled,
      sortedDerivation, positions, _comparisons, _unique⟩
  rw [positions]
  have sortedPerm := sortedDerivation.perm.map (fun entry => entry.position)
  have compiledPositions :=
    DeclarativeAromaticCanonicalRule3Through6IndexedKeys.positions compiled
  rw [compiledPositions] at sortedPerm
  simpa [List.range_eq_range', rootsLength] using sortedPerm

theorem aromaticCanonicalRule3Through6RankingBackend_of_length_ne_four
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat)
    (wrongLength : roots.length ≠ 4) :
    source.aromaticCanonicalRule3Through6RankingBackend
      target view fuel roots referencePosition = none := by
  simp [aromaticCanonicalRule3Through6RankingBackend, wrongLength]

/-- Two-group/common-reference Rule-6 descriptor using the Rule-3-aware backend. -/
noncomputable def aromaticCanonicalRule3Through6FamilyDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (references : List Nat) : Option RS :=
  rule6FamilyDescriptorWithBackend?
    (source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots)
    parity references

theorem aromaticCanonicalRule3Through6FamilyDescriptor?_eq_some_iff_commonDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (references : List Nat) (descriptor : RS) :
    source.aromaticCanonicalRule3Through6FamilyDescriptor?
        target view fuel roots parity references = some descriptor ↔
      CommonRule6Descriptor
        (source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots)
        parity references descriptor := by
  exact rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor _ _ _ _

/-- Exact two-group family: every reference in the rank-one equivalence class must agree. -/
noncomputable def aromaticCanonicalRule3Through6TwoGroupDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (parity : TetrahedralInputParity) : Option RS :=
  source.aromaticCanonicalRule3Through6FamilyDescriptor?
    target view fuel roots parity
      (rule6EquivalentReferencePositions sorted adjacent)

theorem aromaticCanonicalRule3Through6TwoGroupDescriptor?_eq_some_iff_commonDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (parity : TetrahedralInputParity) (descriptor : RS) :
    source.aromaticCanonicalRule3Through6TwoGroupDescriptor?
        target view fuel roots sorted adjacent parity = some descriptor ↔
      CommonRule6Descriptor
        (source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots)
        parity (rule6EquivalentReferencePositions sorted adjacent) descriptor := by
  exact source.aromaticCanonicalRule3Through6FamilyDescriptor?_eq_some_iff_commonDescriptor
    target view fuel roots parity
      (rule6EquivalentReferencePositions sorted adjacent) descriptor

/-- Three-group singleton-reference route with the prescribed descriptor reversal. -/
noncomputable def aromaticCanonicalRule3Through6ThreeGroupDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option RS := do
  let descriptor ← source.aromaticCanonicalRule3Through6FamilyDescriptor?
    target view fuel roots parity (rule6ThreeGroupReferencePositions sorted)
  some (RS.swap descriptor)

theorem aromaticCanonicalRule3Through6ThreeGroupDescriptor?_eq_some_iff_swappedCommonDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS) :
    source.aromaticCanonicalRule3Through6ThreeGroupDescriptor?
        target view fuel roots parity sorted = some descriptor ↔
      CommonRule6Descriptor
        (source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots)
        parity (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor) := by
  unfold aromaticCanonicalRule3Through6ThreeGroupDescriptor?
  cases familyEq : source.aromaticCanonicalRule3Through6FamilyDescriptor?
      target view fuel roots parity (rule6ThreeGroupReferencePositions sorted) with
  | none =>
      have noCommon :=
        (source.aromaticCanonicalRule3Through6FamilyDescriptor?_eq_some_iff_commonDescriptor
          target view fuel roots parity (rule6ThreeGroupReferencePositions sorted)
            (RS.swap descriptor)).not.mp (by simp [familyEq])
      simp [noCommon]
  | some base =>
      have commonBase :=
        (source.aromaticCanonicalRule3Through6FamilyDescriptor?_eq_some_iff_commonDescriptor
          target view fuel roots parity (rule6ThreeGroupReferencePositions sorted) base).mp
          familyEq
      constructor
      · intro emitted
        have baseEq : base = RS.swap descriptor := by
          have swappedEq : RS.swap base = descriptor := by
            simpa [familyEq] using emitted
          calc
            base = RS.swap (RS.swap base) := (rs_swap_involutive base).symm
            _ = RS.swap descriptor := congrArg RS.swap swappedEq
        simpa [baseEq] using commonBase
      · intro commonSwapped
        have descriptorsEqual : base = RS.swap descriptor :=
          commonRule6Descriptor_functional
            (source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots)
            parity (rule6ThreeGroupReferencePositions sorted) commonBase commonSwapped
        simp [descriptorsEqual]

/-- Dependent four-way route using only Rule-3-aware source rankings. -/
noncomputable def aromaticCanonicalRule3Through6FourWayDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option RS :=
  authoritativeOccurrenceRule6FourWayDescriptor?
    (source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots)
    parity sorted

theorem aromaticCanonicalRule3Through6FourWayDescriptor?_eq_some_iff_judgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS) :
    source.aromaticCanonicalRule3Through6FourWayDescriptor?
        target view fuel roots parity sorted = some descriptor ↔
      AuthoritativeFourWayDescriptorJudgment
        (source.aromaticCanonicalRule3Through6RankingBackend target view fuel roots)
        parity sorted descriptor := by
  exact authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment _ _ _ _

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
