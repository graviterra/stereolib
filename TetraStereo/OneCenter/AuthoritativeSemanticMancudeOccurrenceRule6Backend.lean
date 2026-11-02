import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule6PromotedKey
import TetraStereo.OneCenter.CIPAuthoritativeRule6P92Enumeration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open Rule6ReferenceFamilySemantics
open AuthoritativeCIPRule6P92Enumeration

/-!
# Concrete source-canonical Rule-6 ranking backend

The generic P-92 Rule-6 family theorems consume a backend indexed by ligand position.  This module
constructs that backend from the proved promoted keys, retains the exact stable comparison trace,
and proves that every returned position list is a permutation of the supplied ligand frame.
-/

structure AromaticCanonicalRule6IndexedKey
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  cursor : source.AromaticCanonicalRerootCursor carrierFuel
  position : Nat
  key : source.AromaticCanonicalRule6PromotedKey

/-- A comparison is Rule-6-dependent precisely when the certified Rules-1a--2, 4--5 key ties but promotion
breaks that tie. -/
def compareAromaticCanonicalRule6IndexedKeys
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalRule6IndexedKey carrierFuel) :
    Rule6TrackedDecision :=
  let prior := source.compareAromaticCanonicalRerootCompoundRule45Keys
    left.key.prior right.key.prior
  let ordering := source.compareAromaticCanonicalRule6PromotedKeys left.key right.key
  { ordering := ordering
    pseudo := prior = Ordering.eq ∧ ordering ≠ Ordering.eq }

structure AromaticCanonicalRule6IndexedInsertion
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  entries : List (source.AromaticCanonicalRule6IndexedKey carrierFuel)
  pseudoComparisons : Nat
  unique : Bool

/-- Descending stable insertion.  Equality is retained as an explicit non-unique ranking. -/
def insertAromaticCanonicalRule6IndexedKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalRule6IndexedKey carrierFuel) :
    List (source.AromaticCanonicalRule6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule6IndexedInsertion carrierFuel
  | [] => { entries := [candidate], pseudoComparisons := 0, unique := true }
  | low :: remaining =>
      let decision := source.compareAromaticCanonicalRule6IndexedKeys candidate low
      let observed := if decision.pseudo then 1 else 0
      match decision.ordering with
      | .lt =>
          let deeper := source.insertAromaticCanonicalRule6IndexedKey candidate remaining
          { entries := low :: deeper.entries
            pseudoComparisons := observed + deeper.pseudoComparisons
            unique := deeper.unique }
      | .eq =>
          { entries := candidate :: low :: remaining
            pseudoComparisons := observed
            unique := false }
      | .gt =>
          { entries := candidate :: low :: remaining
            pseudoComparisons := observed
            unique := true }

structure AromaticCanonicalRule6IndexedSort
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  entries : List (source.AromaticCanonicalRule6IndexedKey carrierFuel)
  pseudoComparisons : Nat
  unique : Bool

def sortAromaticCanonicalRule6IndexedKeys
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    List (source.AromaticCanonicalRule6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule6IndexedSort carrierFuel
  | [] => { entries := [], pseudoComparisons := 0, unique := true }
  | candidate :: remaining =>
      let sorted := source.sortAromaticCanonicalRule6IndexedKeys remaining
      let inserted := source.insertAromaticCanonicalRule6IndexedKey candidate sorted.entries
      { entries := inserted.entries
        pseudoComparisons := sorted.pseudoComparisons + inserted.pseudoComparisons
        unique := sorted.unique && inserted.unique }

/-! ## Independent stable-sort derivations -/

inductive DeclarativeAromaticCanonicalRule6IndexedInsertion
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalRule6IndexedKey carrierFuel) :
    List (source.AromaticCanonicalRule6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule6IndexedInsertion carrierFuel → Prop
  | nil : DeclarativeAromaticCanonicalRule6IndexedInsertion source candidate []
      { entries := [candidate], pseudoComparisons := 0, unique := true }
  | placeAfter {low remaining deeper}
      (lower : (source.compareAromaticCanonicalRule6IndexedKeys candidate low).ordering =
        Ordering.lt)
      (tail : DeclarativeAromaticCanonicalRule6IndexedInsertion
        source candidate remaining deeper) :
      DeclarativeAromaticCanonicalRule6IndexedInsertion source candidate (low :: remaining)
        { entries := low :: deeper.entries
          pseudoComparisons :=
            (if (source.compareAromaticCanonicalRule6IndexedKeys candidate low).pseudo
              then 1 else 0) + deeper.pseudoComparisons
          unique := deeper.unique }
  | tie {low remaining}
      (equal : (source.compareAromaticCanonicalRule6IndexedKeys candidate low).ordering =
        Ordering.eq) :
      DeclarativeAromaticCanonicalRule6IndexedInsertion source candidate (low :: remaining)
        { entries := candidate :: low :: remaining
          pseudoComparisons :=
            if (source.compareAromaticCanonicalRule6IndexedKeys candidate low).pseudo
              then 1 else 0
          unique := false }
  | placeBefore {low remaining}
      (higher : (source.compareAromaticCanonicalRule6IndexedKeys candidate low).ordering =
        Ordering.gt) :
      DeclarativeAromaticCanonicalRule6IndexedInsertion source candidate (low :: remaining)
        { entries := candidate :: low :: remaining
          pseudoComparisons :=
            if (source.compareAromaticCanonicalRule6IndexedKeys candidate low).pseudo
              then 1 else 0
          unique := true }

theorem insertAromaticCanonicalRule6IndexedKey_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalRule6IndexedKey carrierFuel) :
    ∀ entries,
      source.DeclarativeAromaticCanonicalRule6IndexedInsertion candidate entries
        (source.insertAromaticCanonicalRule6IndexedKey candidate entries)
  | [] => DeclarativeAromaticCanonicalRule6IndexedInsertion.nil
  | low :: remaining => by
      generalize decisionEq :
        source.compareAromaticCanonicalRule6IndexedKeys candidate low = decision
      cases comparison : decision.ordering with
      | lt =>
          have lower :
              (source.compareAromaticCanonicalRule6IndexedKeys candidate low).ordering =
                Ordering.lt := by
            rw [decisionEq]
            exact comparison
          simpa [insertAromaticCanonicalRule6IndexedKey, decisionEq, comparison] using
            (DeclarativeAromaticCanonicalRule6IndexedInsertion.placeAfter lower
              (source.insertAromaticCanonicalRule6IndexedKey_sound candidate remaining))
      | eq =>
          have equal :
              (source.compareAromaticCanonicalRule6IndexedKeys candidate low).ordering =
                Ordering.eq := by
            rw [decisionEq]
            exact comparison
          simpa [insertAromaticCanonicalRule6IndexedKey, decisionEq, comparison] using
            (DeclarativeAromaticCanonicalRule6IndexedInsertion.tie
              (remaining := remaining) equal)
      | gt =>
          have higher :
              (source.compareAromaticCanonicalRule6IndexedKeys candidate low).ordering =
                Ordering.gt := by
            rw [decisionEq]
            exact comparison
          simpa [insertAromaticCanonicalRule6IndexedKey, decisionEq, comparison] using
            (DeclarativeAromaticCanonicalRule6IndexedInsertion.placeBefore
              (remaining := remaining) higher)

theorem DeclarativeAromaticCanonicalRule6IndexedInsertion.perm
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    {candidate : source.AromaticCanonicalRule6IndexedKey carrierFuel}
    {entries : List (source.AromaticCanonicalRule6IndexedKey carrierFuel)}
    {inserted : source.AromaticCanonicalRule6IndexedInsertion carrierFuel}
    (derivation : source.DeclarativeAromaticCanonicalRule6IndexedInsertion
      candidate entries inserted) :
    inserted.entries.Perm (candidate :: entries) := by
  induction derivation with
  | nil => exact List.Perm.refl _
  | tie => exact List.Perm.refl _
  | placeBefore => exact List.Perm.refl _
  | placeAfter _ _ inductionHypothesis =>
      exact (List.Perm.cons _ inductionHypothesis).trans
        (List.Perm.swap _ _ _)

inductive DeclarativeAromaticCanonicalRule6IndexedSort
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    List (source.AromaticCanonicalRule6IndexedKey carrierFuel) →
      source.AromaticCanonicalRule6IndexedSort carrierFuel → Prop
  | nil : DeclarativeAromaticCanonicalRule6IndexedSort source []
      { entries := [], pseudoComparisons := 0, unique := true }
  | cons {candidate remaining sorted inserted}
      (tail : DeclarativeAromaticCanonicalRule6IndexedSort source remaining sorted)
      (insertion : DeclarativeAromaticCanonicalRule6IndexedInsertion
        source candidate sorted.entries inserted) :
      DeclarativeAromaticCanonicalRule6IndexedSort source (candidate :: remaining)
        { entries := inserted.entries
          pseudoComparisons := sorted.pseudoComparisons + inserted.pseudoComparisons
          unique := sorted.unique && inserted.unique }

theorem sortAromaticCanonicalRule6IndexedKeys_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    ∀ entries : List (source.AromaticCanonicalRule6IndexedKey carrierFuel),
      source.DeclarativeAromaticCanonicalRule6IndexedSort entries
        (source.sortAromaticCanonicalRule6IndexedKeys entries)
  | [] => DeclarativeAromaticCanonicalRule6IndexedSort.nil
  | candidate :: remaining => by
      unfold sortAromaticCanonicalRule6IndexedKeys
      exact DeclarativeAromaticCanonicalRule6IndexedSort.cons
        (source.sortAromaticCanonicalRule6IndexedKeys_sound remaining)
        (source.insertAromaticCanonicalRule6IndexedKey_sound candidate
          (source.sortAromaticCanonicalRule6IndexedKeys remaining).entries)

theorem DeclarativeAromaticCanonicalRule6IndexedSort.perm
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    {entries : List (source.AromaticCanonicalRule6IndexedKey carrierFuel)}
    {sorted : source.AromaticCanonicalRule6IndexedSort carrierFuel}
    (derivation : source.DeclarativeAromaticCanonicalRule6IndexedSort entries sorted) :
    sorted.entries.Perm entries := by
  induction derivation with
  | nil => exact List.Perm.refl []
  | cons tail insertion inductionHypothesis =>
      exact insertion.perm.trans (List.Perm.cons _ inductionHypothesis)

/-- Compile a promoted key while retaining its original ligand position. -/
noncomputable def buildAromaticCanonicalRule6IndexedKey?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat) :
    source.AromaticCanonicalRerootCursor carrierFuel × Nat →
      Option (source.AromaticCanonicalRule6IndexedKey carrierFuel)
  | (cursor, position) => do
      let key ← source.buildAromaticCanonicalRule6PromotedKey?
        target view reference fuel cursor
      some { cursor := cursor, position := position, key := key }

def DeclarativeAromaticCanonicalRule6IndexedKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat)
    (input : source.AromaticCanonicalRerootCursor carrierFuel × Nat)
    (output : source.AromaticCanonicalRule6IndexedKey carrierFuel) : Prop :=
  output.cursor = input.1 ∧ output.position = input.2 ∧
    source.DeclarativeAromaticCanonicalRule6PromotedKey
      target view reference fuel input.1 output.key

theorem buildAromaticCanonicalRule6IndexedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat)
    (input : source.AromaticCanonicalRerootCursor carrierFuel × Nat)
    (output : source.AromaticCanonicalRule6IndexedKey carrierFuel)
    (computed : source.buildAromaticCanonicalRule6IndexedKey?
      target view reference fuel input = some output) :
    source.DeclarativeAromaticCanonicalRule6IndexedKey
      target view reference fuel input output := by
  rcases input with ⟨cursor, position⟩
  unfold buildAromaticCanonicalRule6IndexedKey? at computed
  cases keyComputed : source.buildAromaticCanonicalRule6PromotedKey?
      target view reference fuel cursor with
  | none => simp [keyComputed] at computed
  | some key =>
      simp [keyComputed] at computed
      subst output
      exact ⟨rfl, rfl,
        source.buildAromaticCanonicalRule6PromotedKey?_sound
          target view reference fuel cursor key keyComputed⟩

private theorem mapM_buildAromaticCanonicalRule6IndexedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) (fuel : Nat) :
    ∀ inputs outputs,
      inputs.mapM (source.buildAromaticCanonicalRule6IndexedKey?
        target view reference fuel) = some outputs →
      List.Forall₂ (source.DeclarativeAromaticCanonicalRule6IndexedKey
        target view reference fuel) inputs outputs
  | [], outputs, computed => by
      simp at computed
      subst outputs
      exact List.Forall₂.nil
  | input :: inputs, outputs, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalRule6IndexedKey?
          target view reference fuel input with
      | none => simp [headComputed] at computed
      | some output =>
          cases tailComputed : inputs.mapM
              (source.buildAromaticCanonicalRule6IndexedKey?
                target view reference fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              exact List.Forall₂.cons
                (source.buildAromaticCanonicalRule6IndexedKey?_sound
                  target view reference fuel input output headComputed)
                (mapM_buildAromaticCanonicalRule6IndexedKey?_sound
                  source target view reference fuel inputs tail tailComputed)

theorem DeclarativeAromaticCanonicalRule6IndexedKeys.positions
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {target : source.AromaticCanonicalOccurrence carrierFuel}
    {view : source.AromaticCanonicalDependencyView target}
    {reference : source.AromaticCanonicalAtom}
    {inputs : List (source.AromaticCanonicalRerootCursor carrierFuel × Nat)}
    {outputs : List (source.AromaticCanonicalRule6IndexedKey carrierFuel)}
    (derived : List.Forall₂ (source.DeclarativeAromaticCanonicalRule6IndexedKey
      target view reference fuel) inputs outputs) :
    outputs.map (fun entry => entry.position) = inputs.map Prod.snd := by
  induction derived with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [head.2.1, inductionHypothesis]

/-- Concrete backend consumed by the P-92 two-, three-, and four-way family algorithms. -/
noncomputable def aromaticCanonicalRule6RankingBackend
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    ProductionRule6RankingBackend :=
  fun referencePosition => do
    let referenceCursor ← roots[referencePosition]?
    let reference ← referenceCursor.occurrence.1.node.current?
    let entries ← roots.zipIdx.mapM
      (source.buildAromaticCanonicalRule6IndexedKey? target view reference fuel)
    let sorted := source.sortAromaticCanonicalRule6IndexedKeys entries
    some
      { positions := sorted.entries.map fun entry => entry.position
        pseudoComparisons := sorted.pseudoComparisons
        unique := sorted.unique }

/-- Independent meaning of one concrete backend result. -/
def DeclarativeAromaticCanonicalRule6Ranking
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat) (ranking : Rule6TrackedRanking) : Prop :=
  ∃ referenceCursor reference entries sorted,
    roots[referencePosition]? = some referenceCursor ∧
      referenceCursor.occurrence.1.node.current? = some reference ∧
      List.Forall₂ (source.DeclarativeAromaticCanonicalRule6IndexedKey
        target view reference fuel) roots.zipIdx entries ∧
      source.DeclarativeAromaticCanonicalRule6IndexedSort entries sorted ∧
      ranking.positions = sorted.entries.map (fun entry => entry.position) ∧
      ranking.pseudoComparisons = sorted.pseudoComparisons ∧
      ranking.unique = sorted.unique

theorem aromaticCanonicalRule6RankingBackend_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat) (ranking : Rule6TrackedRanking)
    (computed : source.aromaticCanonicalRule6RankingBackend
      target view fuel roots referencePosition = some ranking) :
    source.DeclarativeAromaticCanonicalRule6Ranking
      target view fuel roots referencePosition ranking := by
  unfold aromaticCanonicalRule6RankingBackend at computed
  cases referenceCursorComputed : roots[referencePosition]? with
  | none => simp [referenceCursorComputed] at computed
  | some referenceCursor =>
      cases referenceComputed : referenceCursor.occurrence.1.node.current? with
      | none => simp [referenceCursorComputed, referenceComputed] at computed
      | some reference =>
          cases entriesComputed : roots.zipIdx.mapM
              (source.buildAromaticCanonicalRule6IndexedKey?
                target view reference fuel) with
          | none =>
              simp [referenceCursorComputed, referenceComputed, entriesComputed] at computed
          | some entries =>
              let sorted := source.sortAromaticCanonicalRule6IndexedKeys entries
              simp [referenceCursorComputed, referenceComputed, entriesComputed] at computed
              subst ranking
              exact ⟨referenceCursor, reference, entries, sorted,
                referenceCursorComputed, referenceComputed,
                mapM_buildAromaticCanonicalRule6IndexedKey?_sound
                  source target view reference fuel roots.zipIdx entries entriesComputed,
                source.sortAromaticCanonicalRule6IndexedKeys_sound entries,
                rfl, rfl, rfl⟩

/-- Every successful source-canonical ranking contains every ligand position exactly once. -/
theorem aromaticCanonicalRule6RankingBackend_positions_perm
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (referencePosition : Nat) (ranking : Rule6TrackedRanking)
    (computed : source.aromaticCanonicalRule6RankingBackend
      target view fuel roots referencePosition = some ranking) :
    ranking.positions.Perm (List.range roots.length) := by
  rcases source.aromaticCanonicalRule6RankingBackend_sound
      target view fuel roots referencePosition ranking computed with
    ⟨_referenceCursor, _reference, entries, sorted, _lookup, _current,
      compiled, sortedDerivation, positions, _pseudo, _unique⟩
  rw [positions]
  have sortedPerm := sortedDerivation.perm.map
    (fun entry => entry.position)
  have compiledPositions :=
    DeclarativeAromaticCanonicalRule6IndexedKeys.positions compiled
  rw [compiledPositions] at sortedPerm
  simpa [List.range_eq_range'] using sortedPerm

/-- Two-group/common-reference Rule-6 descriptor on the concrete source backend. -/
noncomputable def aromaticCanonicalRule6FamilyDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (references : List Nat) : Option RS :=
  rule6FamilyDescriptorWithBackend?
    (source.aromaticCanonicalRule6RankingBackend target view fuel roots)
    parity references

theorem aromaticCanonicalRule6FamilyDescriptor?_eq_some_iff_commonDescriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (references : List Nat) (descriptor : RS) :
    source.aromaticCanonicalRule6FamilyDescriptor?
        target view fuel roots parity references = some descriptor ↔
      CommonRule6Descriptor
        (source.aromaticCanonicalRule6RankingBackend target view fuel roots)
        parity references descriptor := by
  exact rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor _ _ _ _

/-- Three-group singleton-reference route with the prescribed descriptor reversal. -/
noncomputable def aromaticCanonicalRule6ThreeGroupDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option RS := do
  let descriptor ← source.aromaticCanonicalRule6FamilyDescriptor?
    target view fuel roots parity (rule6ThreeGroupReferencePositions sorted)
  some (RS.swap descriptor)

/-- Dependent four-way route on the concrete source backend. -/
noncomputable def aromaticCanonicalRule6FourWayDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option RS :=
  authoritativeOccurrenceRule6FourWayDescriptor?
    (source.aromaticCanonicalRule6RankingBackend target view fuel roots) parity sorted

theorem aromaticCanonicalRule6FourWayDescriptor?_eq_some_iff_judgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS) :
    source.aromaticCanonicalRule6FourWayDescriptor?
        target view fuel roots parity sorted = some descriptor ↔
      AuthoritativeFourWayDescriptorJudgment
        (source.aromaticCanonicalRule6RankingBackend target view fuel roots)
        parity sorted descriptor := by
  exact authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment _ _ _ _

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
