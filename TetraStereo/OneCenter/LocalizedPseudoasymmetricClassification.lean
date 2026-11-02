import TetraStereo.OneCenter.LocalizedRecursiveRule45Comparison

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
# Stable-sort Rule-5 history and localized uppercase/lowercase classification

Pseudoasymmetric classification is a property of the comparisons actually made by the stable
four-ligand insertion sort.  Counting every pair, or inspecting only the final adjacent pairs, is
not equivalent.  This module makes the comparison history part of the result and provides a
proof-relevant derivation of that exact execution.
-/

/-- A tetrahedral configurational descriptor whose case is part of the type. -/
inductive LocalizedTetrahedralRSPseudoDescriptor where
  | chiral (descriptor : RS)
  | pseudoasymmetric (descriptor : PseudoRS)
  deriving DecidableEq, Repr

/-- Lowercase spelling corresponding to the exact same priority-ordered spatial sense. -/
def pseudoRSOfRS : RS → PseudoRS
  | RS.R => PseudoRS.r
  | RS.S => PseudoRS.s

/-- Exactly one enantiomorphic (`±2`) comparison makes the tetrahedral result lowercase. Zero or
two-or-more such comparisons leave the result uppercase. -/
def classifyTetrahedralRSPseudo (descriptor : RS) (pseudoComparisons : ℕ) :
    LocalizedTetrahedralRSPseudoDescriptor :=
  if pseudoComparisons = 1 then
    .pseudoasymmetric (pseudoRSOfRS descriptor)
  else
    .chiral descriptor

/-- Simultaneous complement on uppercase and lowercase tetrahedral labels. -/
def LocalizedTetrahedralRSPseudoDescriptor.swap :
    LocalizedTetrahedralRSPseudoDescriptor → LocalizedTetrahedralRSPseudoDescriptor
  | .chiral .R => .chiral .S
  | .chiral .S => .chiral .R
  | .pseudoasymmetric .r => .pseudoasymmetric .s
  | .pseudoasymmetric .s => .pseudoasymmetric .r

/-- Classification commutes with complementing the underlying spatial `R/S` sense. -/
theorem classifyTetrahedralRSPseudo_swap
    (descriptor : RS) (pseudoComparisons : ℕ) :
    classifyTetrahedralRSPseudo (RS.swap descriptor) pseudoComparisons =
      (classifyTetrahedralRSPseudo descriptor pseudoComparisons).swap := by
  cases descriptor <;> by_cases one : pseudoComparisons = 1 <;>
    simp [classifyTetrahedralRSPseudo, one,
      LocalizedTetrahedralRSPseudoDescriptor.swap, pseudoRSOfRS, RS.swap]

@[simp] theorem classifyTetrahedralRSPseudo_one (descriptor : RS) :
    classifyTetrahedralRSPseudo descriptor 1 =
      .pseudoasymmetric (pseudoRSOfRS descriptor) := by
  simp [classifyTetrahedralRSPseudo]

theorem classifyTetrahedralRSPseudo_chiral_of_ne_one
    (descriptor : RS) {pseudoComparisons : ℕ}
    (notOne : pseudoComparisons ≠ 1) :
    classifyTetrahedralRSPseudo descriptor pseudoComparisons =
      .chiral descriptor := by
  simp [classifyTetrahedralRSPseudo, notOne]

@[simp] theorem classifyTetrahedralRSPseudo_zero (descriptor : RS) :
    classifyTetrahedralRSPseudo descriptor 0 = .chiral descriptor := by
  simp [classifyTetrahedralRSPseudo]

@[simp] theorem classifyTetrahedralRSPseudo_two (descriptor : RS) :
    classifyTetrahedralRSPseudo descriptor 2 = .chiral descriptor := by
  simp [classifyTetrahedralRSPseudo]

/-- Result of inserting one canonical ligand position into a lowest-to-highest priority list. -/
structure TrackedLocalizedLigandInsertion where
  lowestFirst : List (Fin 4)
  pseudoComparisons : ℕ
  deriving DecidableEq, Repr

/-- Insert one ligand into a lowest-to-highest list while recording exactly the strict `±2`
comparisons made during this insertion. Failure and ties are refused. -/
def insertLocalizedLigandTracked
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (candidate : Fin 4) :
    List (Fin 4) → Option TrackedLocalizedLigandInsertion
  | [] => some { lowestFirst := [candidate], pseudoComparisons := 0 }
  | low :: remaining => do
      let comparison ← compareAt low candidate
      let observed := if comparison.pseudo then 1 else 0
      match comparison.ordering with
      | Ordering.eq => none
      | Ordering.gt =>
          some
            { lowestFirst := candidate :: low :: remaining
              pseudoComparisons := observed }
      | Ordering.lt => do
          let deeper ← insertLocalizedLigandTracked compareAt candidate remaining
          some
            { lowestFirst := low :: deeper.lowestFirst
              pseudoComparisons := observed + deeper.pseudoComparisons }

/-- A proof-relevant derivation of one exact tracked insertion. -/
inductive DeclarativeTrackedLocalizedLigandInsertion
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (candidate : Fin 4) :
    List (Fin 4) → TrackedLocalizedLigandInsertion → Prop
  | nil : DeclarativeTrackedLocalizedLigandInsertion compareAt candidate []
      { lowestFirst := [candidate], pseudoComparisons := 0 }
  | placeBefore {low remaining comparison}
      (compared : compareAt low candidate = some comparison)
      (higherLow : comparison.ordering = Ordering.gt) :
      DeclarativeTrackedLocalizedLigandInsertion compareAt candidate (low :: remaining)
        { lowestFirst := candidate :: low :: remaining
          pseudoComparisons := if comparison.pseudo then 1 else 0 }
  | placeAfter {low remaining comparison deeper}
      (compared : compareAt low candidate = some comparison)
      (lowerLow : comparison.ordering = Ordering.lt)
      (tail : DeclarativeTrackedLocalizedLigandInsertion
        compareAt candidate remaining deeper) :
      DeclarativeTrackedLocalizedLigandInsertion compareAt candidate (low :: remaining)
        { lowestFirst := low :: deeper.lowestFirst
          pseudoComparisons :=
            (if comparison.pseudo then 1 else 0) + deeper.pseudoComparisons }

/-- Successful insertion has exactly the comparison-by-comparison derivation above. -/
theorem insertLocalizedLigandTracked_sound
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (candidate : Fin 4) :
    ∀ existing result,
      insertLocalizedLigandTracked compareAt candidate existing = some result →
      DeclarativeTrackedLocalizedLigandInsertion compareAt candidate existing result
  | [], result, computed => by
      simp [insertLocalizedLigandTracked] at computed
      subst result
      exact DeclarativeTrackedLocalizedLigandInsertion.nil
  | low :: remaining, result, computed => by
      unfold insertLocalizedLigandTracked at computed
      cases comparisonComputed : compareAt low candidate with
      | none => simp [comparisonComputed] at computed
      | some comparison =>
          cases ordering : comparison.ordering with
          | eq => simp [comparisonComputed, ordering] at computed
          | gt =>
              simp [comparisonComputed, ordering] at computed
              subst result
              exact DeclarativeTrackedLocalizedLigandInsertion.placeBefore
                comparisonComputed ordering
          | lt =>
              cases deeperComputed :
                  insertLocalizedLigandTracked compareAt candidate remaining with
              | none => simp [comparisonComputed, ordering, deeperComputed] at computed
              | some deeper =>
                  simp [comparisonComputed, ordering, deeperComputed] at computed
                  subst result
                  exact DeclarativeTrackedLocalizedLigandInsertion.placeAfter
                    comparisonComputed ordering
                    (insertLocalizedLigandTracked_sound compareAt candidate
                      remaining deeper deeperComputed)

/-- Successful tracked insertion is exactly the structural comparison-history derivation. -/
theorem insertLocalizedLigandTracked_eq_some_iff
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (candidate : Fin 4) :
    ∀ existing result,
      insertLocalizedLigandTracked compareAt candidate existing = some result ↔
        DeclarativeTrackedLocalizedLigandInsertion compareAt candidate existing result
  | [], result => by
      constructor
      · exact insertLocalizedLigandTracked_sound compareAt candidate [] result
      · intro derived
        cases derived
        rfl
  | low :: remaining, result => by
      constructor
      · exact insertLocalizedLigandTracked_sound compareAt candidate
          (low :: remaining) result
      · intro derived
        cases derived with
        | placeBefore compared higherLow =>
            simp [insertLocalizedLigandTracked, compared, higherLow]
        | placeAfter compared lowerLow tail =>
            unfold insertLocalizedLigandTracked
            rw [compared]
            simp [lowerLow, (insertLocalizedLigandTracked_eq_some_iff
              compareAt candidate remaining _).mpr tail]

/-- Tracked insertion preserves exactly the candidate plus the existing ligand multiset. -/
theorem DeclarativeTrackedLocalizedLigandInsertion.perm
    {compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison}
    {candidate : Fin 4} {existing : List (Fin 4)}
    {result : TrackedLocalizedLigandInsertion}
    (derivation : DeclarativeTrackedLocalizedLigandInsertion
      compareAt candidate existing result) :
    result.lowestFirst.Perm (candidate :: existing) := by
  induction derivation with
  | nil => exact List.Perm.refl _
  | placeBefore => exact List.Perm.refl _
  | placeAfter _ _ tail ih =>
      exact (List.Perm.cons _ ih).trans (List.Perm.swap _ _ _)

/-- Result of the complete stable insertion sort. `highestFirst` is descriptor-facing; the
comparison history is accumulated while maintaining the reverse lowest-to-highest list. -/
structure TrackedLocalizedLigandOrder where
  highestFirst : List (Fin 4)
  pseudoComparisons : ℕ
  deriving DecidableEq, Repr

/-- Tail-recursive stable sort state. Candidates are consumed in canonical input order, exactly
matching the production left fold. -/
def sortLocalizedLigandsTrackedFrom
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    List (Fin 4) → List (Fin 4) → ℕ →
      Option TrackedLocalizedLigandOrder
  | [], lowestFirst, pseudoComparisons =>
      some
        { highestFirst := lowestFirst.reverse
          pseudoComparisons := pseudoComparisons }
  | candidate :: candidates, lowestFirst, pseudoComparisons => do
      let inserted ←
        insertLocalizedLigandTracked compareAt candidate lowestFirst
      sortLocalizedLigandsTrackedFrom compareAt candidates inserted.lowestFirst
        (pseudoComparisons + inserted.pseudoComparisons)

/-- Stable tracked sort of an explicitly supplied canonical ligand-position list. -/
def sortLocalizedLigandsTracked
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (candidates : List (Fin 4)) : Option TrackedLocalizedLigandOrder :=
  sortLocalizedLigandsTrackedFrom compareAt candidates [] 0

/-- Recursive derivation of the exact tracked stable sort. -/
inductive DeclarativeTrackedLocalizedLigandSort
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    List (Fin 4) → List (Fin 4) → ℕ →
      TrackedLocalizedLigandOrder → Prop
  | nil (lowestFirst : List (Fin 4)) (pseudoComparisons : ℕ) :
      DeclarativeTrackedLocalizedLigandSort compareAt [] lowestFirst pseudoComparisons
        { highestFirst := lowestFirst.reverse
          pseudoComparisons := pseudoComparisons }
  | cons {candidate candidates lowestFirst pseudoComparisons inserted result}
      (insertion : DeclarativeTrackedLocalizedLigandInsertion compareAt candidate
        lowestFirst inserted)
      (tail : DeclarativeTrackedLocalizedLigandSort compareAt candidates
        inserted.lowestFirst
        (pseudoComparisons + inserted.pseudoComparisons) result) :
      DeclarativeTrackedLocalizedLigandSort compareAt (candidate :: candidates)
        lowestFirst pseudoComparisons result

theorem sortLocalizedLigandsTrackedFrom_sound
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    ∀ candidates lowestFirst pseudoComparisons result,
      sortLocalizedLigandsTrackedFrom compareAt candidates lowestFirst
        pseudoComparisons = some result →
      DeclarativeTrackedLocalizedLigandSort compareAt candidates lowestFirst
        pseudoComparisons result
  | [], lowestFirst, pseudoComparisons, result, computed => by
      simp [sortLocalizedLigandsTrackedFrom] at computed
      subst result
      exact DeclarativeTrackedLocalizedLigandSort.nil lowestFirst pseudoComparisons
  | candidate :: candidates, lowestFirst, pseudoComparisons, result, computed => by
      unfold sortLocalizedLigandsTrackedFrom at computed
      cases insertedComputed :
          insertLocalizedLigandTracked compareAt candidate lowestFirst with
      | none => simp [insertedComputed] at computed
      | some inserted =>
          simp [insertedComputed] at computed
          exact DeclarativeTrackedLocalizedLigandSort.cons
            (insertLocalizedLigandTracked_sound compareAt candidate
              lowestFirst inserted insertedComputed)
            (sortLocalizedLigandsTrackedFrom_sound compareAt candidates
              inserted.lowestFirst
              (pseudoComparisons + inserted.pseudoComparisons) result computed)

/-- The tail-recursive tracked sort is exactly its structural derivation. -/
theorem sortLocalizedLigandsTrackedFrom_eq_some_iff
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    ∀ candidates lowestFirst pseudoComparisons result,
      sortLocalizedLigandsTrackedFrom compareAt candidates lowestFirst
          pseudoComparisons = some result ↔
        DeclarativeTrackedLocalizedLigandSort compareAt candidates lowestFirst
          pseudoComparisons result
  | [], lowestFirst, pseudoComparisons, result => by
      constructor
      · exact sortLocalizedLigandsTrackedFrom_sound compareAt []
          lowestFirst pseudoComparisons result
      · intro derived
        cases derived
        rfl
  | candidate :: candidates, lowestFirst, pseudoComparisons, result => by
      constructor
      · exact sortLocalizedLigandsTrackedFrom_sound compareAt (candidate :: candidates)
          lowestFirst pseudoComparisons result
      · intro derived
        cases derived with
        | cons insertion tail =>
            unfold sortLocalizedLigandsTrackedFrom
            rw [(insertLocalizedLigandTracked_eq_some_iff
              compareAt candidate lowestFirst _).mpr insertion]
            exact (sortLocalizedLigandsTrackedFrom_eq_some_iff compareAt
              candidates _ _ result).mpr tail

theorem sortLocalizedLigandsTracked_sound
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (candidates : List (Fin 4)) (result : TrackedLocalizedLigandOrder)
    (computed : sortLocalizedLigandsTracked compareAt candidates = some result) :
    DeclarativeTrackedLocalizedLigandSort compareAt candidates [] 0 result := by
  exact sortLocalizedLigandsTrackedFrom_sound compareAt candidates [] 0 result computed

/-- The public tracked sort is exactly its structural derivation. -/
theorem sortLocalizedLigandsTracked_eq_some_iff
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (candidates : List (Fin 4)) (result : TrackedLocalizedLigandOrder) :
    sortLocalizedLigandsTracked compareAt candidates = some result ↔
      DeclarativeTrackedLocalizedLigandSort compareAt candidates [] 0 result := by
  exact sortLocalizedLigandsTrackedFrom_eq_some_iff
    compareAt candidates [] 0 result

/-- A successful tracked stable sort preserves exactly its input ligand positions. -/
theorem DeclarativeTrackedLocalizedLigandSort.perm
    {compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison}
    {candidates lowestFirst : List (Fin 4)} {pseudoComparisons : ℕ}
    {result : TrackedLocalizedLigandOrder}
    (derivation : DeclarativeTrackedLocalizedLigandSort
      compareAt candidates lowestFirst pseudoComparisons result) :
    result.highestFirst.Perm (lowestFirst ++ candidates) := by
  induction derivation with
  | nil lowestFirst _ =>
      simpa only [List.append_nil] using List.reverse_perm lowestFirst
  | @cons candidate candidates lowestFirst pseudoComparisons inserted result insertion tail ih =>
      have insertedPerm := insertion.perm
      have moved :
          (candidate :: lowestFirst ++ candidates).Perm
            (lowestFirst ++ candidate :: candidates) := by
        exact List.perm_middle.symm
      exact ih.trans ((insertedPerm.append_right _).trans moved)

/-- The concrete four-position stable sort used by the localized classifier. -/
def sortFourLocalizedLigandsTracked
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison) :
    Option TrackedLocalizedLigandOrder :=
  sortLocalizedLigandsTracked compareAt (List.finRange 4)

theorem sortFourLocalizedLigandsTracked_sound
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (result : TrackedLocalizedLigandOrder)
    (computed : sortFourLocalizedLigandsTracked compareAt = some result) :
    DeclarativeTrackedLocalizedLigandSort compareAt (List.finRange 4) [] 0 result := by
  exact sortLocalizedLigandsTracked_sound compareAt (List.finRange 4) result computed

/-- Four-position tracked sorting is exactly its structural derivation. -/
theorem sortFourLocalizedLigandsTracked_eq_some_iff
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (result : TrackedLocalizedLigandOrder) :
    sortFourLocalizedLigandsTracked compareAt = some result ↔
      DeclarativeTrackedLocalizedLigandSort compareAt (List.finRange 4) [] 0 result := by
  exact sortLocalizedLigandsTracked_eq_some_iff compareAt (List.finRange 4) result

theorem sortFourLocalizedLigandsTracked_perm
    (compareAt : Fin 4 → Fin 4 →
      Option ConstitutionalDescriptorHierarchyComparison)
    (result : TrackedLocalizedLigandOrder)
    (computed : sortFourLocalizedLigandsTracked compareAt = some result) :
    result.highestFirst.Perm (List.finRange 4) :=
  (sortFourLocalizedLigandsTracked_sound compareAt result computed).perm

end TetraStereo.OneCenter
