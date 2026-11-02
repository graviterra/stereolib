import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeP93PatternAttachment
import TetraStereo.OneCenter.P93SpiroConfigurationCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace SpiroOccurrencePattern

/-!
# Occurrence-bearing Xabab traversal

The earlier P-93 boundary records the three traversal checks as booleans.  The structures below
retain the actual occurrences and complete keys that justify those checks.  In particular, the
first senior occurrence is selected by a strict result of the complete comparator, while the
second senior occurrence is the cross-ring occurrence in the same complete-key equivalence class.
-/

/-- One occurrence is strictly senior to another under two successfully materialized keys. -/
def ResolvedComparatorSenior {α κ : Type}
    (key? : α → Option κ) (compare : κ → κ → Ordering)
    (senior junior : α) : Prop :=
  ∃ seniorKey juniorKey,
    key? senior = some seniorKey ∧ key? junior = some juniorKey ∧
      compare seniorKey juniorKey = Ordering.gt

/-- An actual four-occurrence traversal for the alternating `Xabab` pattern. -/
structure CanonicalXababOccurrenceTraversal
    {α κ : Type} [DecidableEq α]
    (key? : α → Option κ) (compare : κ → κ → Ordering)
    (first second : Finset α) where
  firstSenior : α
  firstJunior : α
  secondSenior : α
  secondJunior : α
  first_pair : first = {firstSenior, firstJunior}
  second_pair : second = {secondSenior, secondJunior}
  first_distinct : firstSenior ≠ firstJunior
  second_distinct : secondSenior ≠ secondJunior
  first_senior : ResolvedComparatorSenior key? compare firstSenior firstJunior
  senior_equivalent : SameResolvedKey key? (ComparatorTie compare)
    firstSenior secondSenior
  junior_equivalent : SameResolvedKey key? (ComparatorTie compare)
    firstJunior secondJunior

/-- Comparator-tie equivalence of resolved keys is transitive whenever the comparator is. -/
theorem sameResolvedKey_comparatorTie_transitive
    {α κ : Type} (key? : α → Option κ) (compare : κ → κ → Ordering)
    [Std.TransCmp compare] {first second third : α} :
    SameResolvedKey key? (ComparatorTie compare) first second →
      SameResolvedKey key? (ComparatorTie compare) second third →
        SameResolvedKey key? (ComparatorTie compare) first third := by
  rintro ⟨firstKey, secondKey, firstComputed, secondComputed, firstTie⟩
    ⟨otherSecondKey, thirdKey, otherSecondComputed, thirdComputed, secondTie⟩
  have middleEq : secondKey = otherSecondKey :=
    Option.some.inj (secondComputed.symm.trans otherSecondComputed)
  subst otherSecondKey
  exact ⟨firstKey, thirdKey, firstComputed, thirdComputed,
    Std.TransCmp.eq_trans firstTie secondTie⟩

/-- Every resolved alternating two-by-two pattern admits a concrete senior-first traversal. -/
theorem xabab_exists_canonicalOccurrenceTraversal
    {α κ : Type} [DecidableEq α]
    (key? : α → Option κ) (compare : κ → κ → Ordering)
    [Std.TransCmp compare]
    (first second : Finset α)
    (firstCard : first.card = 2) (secondCard : second.card = 2)
    (resolved : ∀ occurrence, occurrence ∈ first ∪ second →
      ∃ key, key? occurrence = some key)
    (alternating : Xabab (SameResolvedKey key? (ComparatorTie compare)) first second) :
    Nonempty (CanonicalXababOccurrenceTraversal key? compare first second) := by
  obtain ⟨left, right, different, firstEq⟩ := Finset.card_eq_two.mp firstCard
  have leftPresent : left ∈ first := by simp [firstEq]
  have rightPresent : right ∈ first := by simp [firstEq]
  obtain ⟨leftKey, leftComputed⟩ :=
    resolved left (Finset.mem_union_left second leftPresent)
  obtain ⟨rightKey, rightComputed⟩ :=
    resolved right (Finset.mem_union_left second rightPresent)
  have notTie : compare leftKey rightKey ≠ Ordering.eq := by
    intro tied
    exact alternating.1 left leftPresent right rightPresent different
      ⟨leftKey, rightKey, leftComputed, rightComputed, tied⟩
  have build
      (senior junior : α) (seniorKey juniorKey : κ)
      (seniorPresent : senior ∈ first) (juniorPresent : junior ∈ first)
      (seniorNe : senior ≠ junior)
      (seniorComputed : key? senior = some seniorKey)
      (juniorComputed : key? junior = some juniorKey)
      (seniorComparison : compare seniorKey juniorKey = Ordering.gt)
      (pairEq : first = {senior, junior}) :
      Nonempty (CanonicalXababOccurrenceTraversal key? compare first second) := by
    obtain ⟨secondSenior, secondSeniorPresent, seniorEquivalent⟩ :=
      alternating.2.2.1 senior seniorPresent
    obtain ⟨secondJunior, secondJuniorPresent, juniorEquivalent⟩ :=
      alternating.2.2.1 junior juniorPresent
    have secondNe : secondSenior ≠ secondJunior := by
      intro equal
      subst secondJunior
      have seniorJuniorEquivalent :
          SameResolvedKey key? (ComparatorTie compare) senior junior :=
        sameResolvedKey_comparatorTie_transitive key? compare seniorEquivalent
          (sameResolvedKey_symmetric key? (ComparatorTie compare)
            (fun {firstKey secondKey} tied => Std.OrientedCmp.eq_comm.mp tied)
            juniorEquivalent)
      exact alternating.1 senior seniorPresent junior juniorPresent seniorNe
        seniorJuniorEquivalent
    have pairSubset : ({secondSenior, secondJunior} : Finset α) ⊆ second := by
      intro occurrence present
      simp only [Finset.mem_insert, Finset.mem_singleton] at present
      rcases present with rfl | rfl
      · exact secondSeniorPresent
      · exact secondJuniorPresent
    have reverseCard : second.card ≤ ({secondSenior, secondJunior} : Finset α).card := by
      simp [secondCard, secondNe]
    have secondPair : second = {secondSenior, secondJunior} :=
      (Finset.eq_of_subset_of_card_le pairSubset reverseCard).symm
    exact ⟨
      { firstSenior := senior
        firstJunior := junior
        secondSenior
        secondJunior
        first_pair := pairEq
        second_pair := secondPair
        first_distinct := seniorNe
        second_distinct := secondNe
        first_senior := ⟨seniorKey, juniorKey, seniorComputed, juniorComputed,
          seniorComparison⟩
        senior_equivalent := seniorEquivalent
        junior_equivalent := juniorEquivalent }
      ⟩
  cases comparison : compare leftKey rightKey with
  | lt =>
      exact build right left rightKey leftKey rightPresent leftPresent different.symm
        rightComputed leftComputed
        (Std.OrientedCmp.gt_iff_lt.mpr comparison) (by
          calc
            first = {left, right} := firstEq
            _ = {right, left} := by
              ext occurrence
              simp [or_comm])
  | eq => exact False.elim (notTie comparison)
  | gt =>
      exact build left right leftKey rightKey leftPresent rightPresent different
        leftComputed rightComputed comparison firstEq

end SpiroOccurrencePattern

namespace CertifiedLocalizedCIPInput

open BlueBookP93.Cyclic
open SpiroOccurrencePattern

/-- Molecule-attached traversal retaining the two actual rings and their four ordered branch
occurrences. -/
structure AuthoritativeSpiroMatrixRowXababTraversal
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (referencePosition : Fin 4) where
  firstRing : Finset input.Atom
  secondRing : Finset input.Atom
  rings_distinct : firstRing ≠ secondRing
  rings_eq : carrier.rings = {firstRing, secondRing}
  occurrenceTraversal : CanonicalXababOccurrenceTraversal
    (input.authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
      carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
      view referencePosition)
    input.certified.input.compareAromaticCanonicalRule3Through6PromotedKeys
    (input.localizedCycleNeighbors firstRing center)
    (input.localizedCycleNeighbors secondRing center)

/-- An exact matrix-row `Xabab` judgment constructs an occurrence-bearing senior-first traversal;
the old three booleans are not premises. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.exists_matrixRow_xababTraversal
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) view)
    (referencePosition : Fin 4)
    (patternJudged : input.DeclarativeAuthoritativeSpiroMatrixRowLigandPattern
      carrierFuel evaluationFuel center carrier judged view referencePosition .Xabab) :
    Nonempty (input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel evaluationFuel
      center carrier judged view referencePosition) := by
  unfold DeclarativeAuthoritativeSpiroMatrixRowLigandPattern
    DeclarativeLocalizedSpiroLigandPattern at patternJudged
  obtain ⟨firstRing, secondRing, ringsDifferent, ringsEq, alternating⟩ := patternJudged
  have firstPresent : firstRing ∈ carrier.rings := by simp [ringsEq]
  have secondPresent : secondRing ∈ carrier.rings := by simp [ringsEq]
  have firstCard := judged.1.ringNeighbors_card input center carrier firstRing firstPresent
  have secondCard := judged.1.ringNeighbors_card input center carrier secondRing secondPresent
  have resolved := ready.matrixRow_branchKeysResolved input carrierFuel evaluationFuel center
    carrier judged view referencePosition
  let key? := input.authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
    carrierFuel evaluationFuel
    (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
    view referencePosition
  let compare := input.certified.input.compareAromaticCanonicalRule3Through6PromotedKeys
  letI : Std.TransCmp compare :=
    input.certified.input.compareAromaticCanonicalRule3Through6PromotedKeys_transCmp
  have allResolved : ∀ occurrence,
      occurrence ∈ input.localizedCycleNeighbors firstRing center ∪
          input.localizedCycleNeighbors secondRing center →
        ∃ key, key? occurrence = some key := by
    intro occurrence present
    rw [Finset.mem_union] at present
    rcases present with firstOccurrence | secondOccurrence
    · exact resolved firstRing firstPresent occurrence firstOccurrence
    · exact resolved secondRing secondPresent occurrence secondOccurrence
  have traversal := xabab_exists_canonicalOccurrenceTraversal key? compare
    (input.localizedCycleNeighbors firstRing center)
    (input.localizedCycleNeighbors secondRing center)
    firstCard secondCard allResolved alternating
  exact ⟨
    { firstRing
      secondRing
      rings_distinct := ringsDifferent
      rings_eq := ringsEq
      occurrenceTraversal := traversal.some }
    ⟩

/-- Executable selector for one actual traversal.  Classical choice is confined to choosing among
the two ring-order presentations; the selected value itself carries all occurrence/key proofs. -/
noncomputable def authoritativeSpiroMatrixRowXababTraversal?
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (referencePosition : Fin 4) :
    Option (input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel evaluationFuel
      center carrier judged view referencePosition) := by
  classical
  if available : Nonempty (input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel
      evaluationFuel center carrier judged view referencePosition) then
    exact some available.some
  else exact none

@[simp] theorem authoritativeSpiroMatrixRowXababTraversal?_isSome_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (referencePosition : Fin 4) :
    (input.authoritativeSpiroMatrixRowXababTraversal? carrierFuel evaluationFuel
      center carrier judged view referencePosition).isSome = true ↔
      Nonempty (input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel evaluationFuel
        center carrier judged view referencePosition) := by
  by_cases available : Nonempty (input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel
      evaluationFuel center carrier judged view referencePosition) <;>
    simp [authoritativeSpiroMatrixRowXababTraversal?, available]

/-- Forgetting the actual occurrences yields valid legacy traversal evidence.  Validity is now a
consequence of an occurrence-bearing certificate, rather than three caller-supplied booleans. -/
def AuthoritativeSpiroMatrixRowXababTraversal.toLegacyEvidence
    {input : CertifiedLocalizedCIPInput} {carrierFuel evaluationFuel : Nat}
    {center : input.Atom} {carrier : input.LocalizedSpiroCenter center}
    {judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier}
    {view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged))}
    {referencePosition : Fin 4}
    (_traversal : input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel evaluationFuel
      center carrier judged view referencePosition) : XababTraversalEvidence :=
  { firstSeniorChosen := true
    secondSeniorDistinguishedByTraversal := true
    juniorOnFirstSeniorBranchChosenFirst := true }

@[simp] theorem AuthoritativeSpiroMatrixRowXababTraversal.toLegacyEvidence_valid
    {input : CertifiedLocalizedCIPInput} {carrierFuel evaluationFuel : Nat}
    {center : input.Atom} {carrier : input.LocalizedSpiroCenter center}
    {judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier}
    {view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged))}
    {referencePosition : Fin 4}
    (traversal : input.AuthoritativeSpiroMatrixRowXababTraversal carrierFuel evaluationFuel
      center carrier judged view referencePosition) :
    ValidXababTraversalEvidence traversal.toLegacyEvidence := by
  simp [AuthoritativeSpiroMatrixRowXababTraversal.toLegacyEvidence,
    ValidXababTraversalEvidence]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
