import TetraStereo.OneCenter.LocalizedSpiroCenterPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace SpiroOccurrencePattern

open BlueBookP93.Cyclic

/-!
# Occurrence-equivalence classification of the four branches at a simple spiro center

Topology supplies two disjoint two-element branch sets.  The `same` relation below is deliberately
semantic: it is intended to mean equality after the complete occurrence-aware CIP comparison.  It
is not replaced by atom identity or atomic-number equality.  The three predicates are the exact
three P-93.5.3 arrangements; all other multiplicity arrangements are refused.
-/

/-- Four pairwise CIP-inequivalent branch occurrences (`Xabcd`). -/
def Xabcd {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α) : Prop :=
  ∀ left, left ∈ first ∪ second →
    ∀ right, right ∈ first ∪ second →
      left ≠ right → ¬same left right

/-- Two CIP-equivalence classes, with one occurrence of each class in each ring (`Xabab`). -/
def Xabab {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α) : Prop :=
  (∀ left, left ∈ first → ∀ right, right ∈ first → left ≠ right → ¬same left right) ∧
  (∀ left, left ∈ second → ∀ right, right ∈ second → left ≠ right → ¬same left right) ∧
  (∀ left, left ∈ first → ∃ right, right ∈ second ∧ same left right) ∧
  (∀ right, right ∈ second → ∃ left, left ∈ first ∧ same left right)

/-- One CIP-equivalence class per ring, with the two ring classes distinct (`Xaabb`). -/
def Xaabb {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α) : Prop :=
  (∀ left, left ∈ first → ∀ right, right ∈ first → same left right) ∧
  (∀ left, left ∈ second → ∀ right, right ∈ second → same left right) ∧
  (∀ left, left ∈ first → ∀ right, right ∈ second → ¬same left right)

def PatternJudgment {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α) :
    SpiroLigandPattern → Prop
  | .Xabcd => Xabcd same first second
  | .Xabab => Xabab same first second
  | .Xaabb => Xaabb same first second

theorem xabcd_symmetric {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α) :
    Xabcd same first second ↔ Xabcd same second first := by
  simp only [Xabcd, Finset.union_comm]

theorem xabab_symmetric {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (sameSymmetric : ∀ {left right}, same left right → same right left) :
    Xabab same first second ↔ Xabab same second first := by
  constructor
  · rintro ⟨firstDifferent, secondDifferent, firstMatched, secondMatched⟩
    refine ⟨secondDifferent, firstDifferent, ?_, ?_⟩
    · intro left leftPresent
      obtain ⟨right, rightPresent, related⟩ := secondMatched left leftPresent
      exact ⟨right, rightPresent, sameSymmetric related⟩
    · intro right rightPresent
      obtain ⟨left, leftPresent, related⟩ := firstMatched right rightPresent
      exact ⟨left, leftPresent, sameSymmetric related⟩
  · rintro ⟨secondDifferent, firstDifferent, secondMatched, firstMatched⟩
    refine ⟨firstDifferent, secondDifferent, ?_, ?_⟩
    · intro left leftPresent
      obtain ⟨right, rightPresent, related⟩ := firstMatched left leftPresent
      exact ⟨right, rightPresent, sameSymmetric related⟩
    · intro right rightPresent
      obtain ⟨left, leftPresent, related⟩ := secondMatched right rightPresent
      exact ⟨left, leftPresent, sameSymmetric related⟩

theorem xaabb_symmetric {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (sameSymmetric : ∀ {left right}, same left right → same right left) :
    Xaabb same first second ↔ Xaabb same second first := by
  constructor <;>
    rintro ⟨firstSame, secondSame, crossDifferent⟩
  · refine ⟨secondSame, firstSame, ?_⟩
    intro right rightPresent left leftPresent related
    exact crossDifferent left leftPresent right rightPresent (sameSymmetric related)
  · refine ⟨secondSame, firstSame, ?_⟩
    intro left leftPresent right rightPresent related
    exact crossDifferent right rightPresent left leftPresent (sameSymmetric related)

theorem patternJudgment_symmetric {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (sameSymmetric : ∀ {left right}, same left right → same right left)
    (pattern : SpiroLigandPattern) :
    PatternJudgment same first second pattern ↔
      PatternJudgment same second first pattern := by
  cases pattern with
  | Xabcd => exact xabcd_symmetric same first second
  | Xabab => exact xabab_symmetric same first second sameSymmetric
  | Xaabb => exact xaabb_symmetric same first second sameSymmetric

private theorem exists_two_distinct_of_card_two {α : Type} [DecidableEq α]
    (members : Finset α) (card : members.card = 2) :
    ∃ first second, first ∈ members ∧ second ∈ members ∧ first ≠ second := by
  obtain ⟨first, second, different, membersEq⟩ := Finset.card_eq_two.mp card
  exact ⟨first, second, by simp [membersEq], by simp [membersEq], different⟩

theorem xabcd_not_xabab {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (firstCard : first.card = 2) (disjoint : Disjoint first second) :
    Xabcd same first second → ¬Xabab same first second := by
  intro allDifferent alternating
  obtain ⟨left, _, leftPresent, _, _⟩ := exists_two_distinct_of_card_two first firstCard
  obtain ⟨right, rightPresent, related⟩ := alternating.2.2.1 left leftPresent
  have different : left ≠ right := by
    intro equal
    subst right
    exact (Finset.disjoint_left.mp disjoint leftPresent rightPresent)
  exact allDifferent left (Finset.mem_union_left second leftPresent) right
    (Finset.mem_union_right first rightPresent) different related

theorem xabcd_not_xaabb {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (firstCard : first.card = 2) :
    Xabcd same first second → ¬Xaabb same first second := by
  intro allDifferent grouped
  obtain ⟨left, right, leftPresent, rightPresent, different⟩ :=
    exists_two_distinct_of_card_two first firstCard
  exact allDifferent left (Finset.mem_union_left second leftPresent) right
    (Finset.mem_union_left second rightPresent) different
    (grouped.1 left leftPresent right rightPresent)

theorem xabab_not_xaabb {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (firstCard : first.card = 2) :
    Xabab same first second → ¬Xaabb same first second := by
  intro alternating grouped
  obtain ⟨left, right, leftPresent, rightPresent, different⟩ :=
    exists_two_distinct_of_card_two first firstCard
  exact alternating.1 left leftPresent right rightPresent different
    (grouped.1 left leftPresent right rightPresent)

/-- The three source patterns are mutually exclusive on two genuine branch pairs. -/
theorem patternJudgment_subsingleton {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (firstCard : first.card = 2) (disjoint : Disjoint first second)
    {left right : SpiroLigandPattern}
    (leftJudged : PatternJudgment same first second left)
    (rightJudged : PatternJudgment same first second right) :
    left = right := by
  cases left <;> cases right
  all_goals try rfl
  · exact False.elim ((xabcd_not_xabab same first second firstCard disjoint)
      leftJudged rightJudged)
  · exact False.elim ((xabcd_not_xaabb same first second firstCard)
      leftJudged rightJudged)
  · exact False.elim ((xabcd_not_xabab same first second firstCard disjoint)
      rightJudged leftJudged)
  · exact False.elim ((xabab_not_xaabb same first second firstCard)
      leftJudged rightJudged)
  · exact False.elim ((xabcd_not_xaabb same first second firstCard)
      rightJudged leftJudged)
  · exact False.elim ((xabab_not_xaabb same first second firstCard)
      rightJudged leftJudged)

/-- Specification classifier: it chooses a pattern iff exactly one of the three P-93 arrangements
holds.  The use of classical choice is isolated here; later executable CIP equality may discharge
the same relation with a decidable comparator. -/
noncomputable def classify?
    {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α) :
    Option SpiroLigandPattern := by
  classical
  if Xabcd same first second then
    exact some .Xabcd
  else if Xabab same first second then
    exact some .Xabab
  else if Xaabb same first second then
    exact some .Xaabb
  else
    exact none

theorem classify?_eq_some_iff {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α)
    (firstCard : first.card = 2) (disjoint : Disjoint first second)
    (pattern : SpiroLigandPattern) :
    classify? same first second = some pattern ↔
      PatternJudgment same first second pattern := by
  classical
  unfold classify?
  by_cases abcd : Xabcd same first second
  · have notAbab := xabcd_not_xabab same first second firstCard disjoint abcd
    have notAabb := xabcd_not_xaabb same first second firstCard abcd
    cases pattern <;> simp [abcd, notAbab, notAabb, PatternJudgment]
  · by_cases abab : Xabab same first second
    · have notAabb := xabab_not_xaabb same first second firstCard abab
      cases pattern <;> simp [abcd, abab, notAabb, PatternJudgment]
    · by_cases aabb : Xaabb same first second
      · cases pattern <;> simp [abcd, abab, aabb, PatternJudgment]
      · cases pattern <;> simp [abcd, abab, aabb, PatternJudgment]

theorem classify?_eq_none_iff {α : Type} [DecidableEq α]
    (same : α → α → Prop) (first second : Finset α) :
    classify? same first second = none ↔
      ¬Xabcd same first second ∧
      ¬Xabab same first second ∧
      ¬Xaabb same first second := by
  classical
  by_cases abcd : Xabcd same first second <;>
    by_cases abab : Xabab same first second <;>
      by_cases aabb : Xaabb same first second <;>
        simp [classify?, abcd, abab, aabb]

/-- Equivalence of two successfully constructed complete CIP keys.  The key relation is intended
to be “the complete comparator returns `Ordering.eq`”; literal record equality would be too strong
for occurrence-distinct but CIP-equivalent branches.  Two construction failures are never treated
as equivalent. -/
def SameResolvedKey {α κ : Type} (key? : α → Option κ)
    (keyEquivalent : κ → κ → Prop) (left right : α) : Prop :=
  ∃ leftKey rightKey,
    key? left = some leftKey ∧ key? right = some rightKey ∧
      keyEquivalent leftKey rightKey

theorem sameResolvedKey_symmetric {α κ : Type} (key? : α → Option κ)
    (keyEquivalent : κ → κ → Prop)
    (keyEquivalentSymmetric : ∀ {left right},
      keyEquivalent left right → keyEquivalent right left)
    {left right : α} :
    SameResolvedKey key? keyEquivalent left right →
      SameResolvedKey key? keyEquivalent right left := by
  rintro ⟨leftKey, rightKey, leftResolved, rightResolved, equivalent⟩
  exact ⟨rightKey, leftKey, rightResolved, leftResolved,
    keyEquivalentSymmetric equivalent⟩

/-- Canonical instantiation of key equivalence: the complete lawful comparator ties. -/
def ComparatorTie {κ : Type} (compare : κ → κ → Ordering) (left right : κ) : Prop :=
  compare left right = Ordering.eq

theorem comparatorTie_symmetric {κ : Type} (compare : κ → κ → Ordering)
    [Std.OrientedCmp compare] {left right : κ} :
    ComparatorTie compare left right → ComparatorTie compare right left := by
  exact Std.OrientedCmp.eq_comm.mp

def AllBranchKeysResolved {α κ : Type} [DecidableEq α]
    (key? : α → Option κ) (first second : Finset α) : Prop :=
  ∀ occurrence, occurrence ∈ first ∪ second → ∃ key, key? occurrence = some key

/-- Guarded classifier for an actual partial CIP-key builder.  The readiness guard prevents the
chemically invalid conclusion that several unresolved branches are pairwise different. -/
noncomputable def classifyResolvedKeys?
    {α κ : Type} [DecidableEq α]
    (key? : α → Option κ) (keyEquivalent : κ → κ → Prop)
    (first second : Finset α) : Option SpiroLigandPattern := by
  classical
  if AllBranchKeysResolved key? first second then
    exact classify? (SameResolvedKey key? keyEquivalent) first second
  else
    exact none

theorem classifyResolvedKeys?_eq_some_iff
    {α κ : Type} [DecidableEq α]
    (key? : α → Option κ) (keyEquivalent : κ → κ → Prop)
    (first second : Finset α)
    (firstCard : first.card = 2) (disjoint : Disjoint first second)
    (pattern : SpiroLigandPattern) :
    classifyResolvedKeys? key? keyEquivalent first second = some pattern ↔
      AllBranchKeysResolved key? first second ∧
        PatternJudgment (SameResolvedKey key? keyEquivalent) first second pattern := by
  classical
  by_cases resolved : AllBranchKeysResolved key? first second
  · simp only [classifyResolvedKeys?, resolved, true_and]
    exact classify?_eq_some_iff (SameResolvedKey key? keyEquivalent)
      first second firstCard disjoint pattern
  · simp [classifyResolvedKeys?, resolved]

theorem classifyResolvedKeys?_eq_none_iff
    {α κ : Type} [DecidableEq α]
    (key? : α → Option κ) (keyEquivalent : κ → κ → Prop)
    (first second : Finset α) :
    classifyResolvedKeys? key? keyEquivalent first second = none ↔
      ¬AllBranchKeysResolved key? first second ∨
        (¬Xabcd (SameResolvedKey key? keyEquivalent) first second ∧
          ¬Xabab (SameResolvedKey key? keyEquivalent) first second ∧
          ¬Xaabb (SameResolvedKey key? keyEquivalent) first second) := by
  classical
  by_cases resolved : AllBranchKeysResolved key? first second
  · simp only [classifyResolvedKeys?, resolved, not_true_eq_false, false_or]
    exact classify?_eq_none_iff (SameResolvedKey key? keyEquivalent) first second
  · simp [classifyResolvedKeys?, resolved]

end SpiroOccurrencePattern

namespace CertifiedLocalizedCIPInput

open BlueBookP93.Cyclic

/-- Molecular meaning of a spiro ligand-pattern judgment for one perceived carrier.  The relation
`same` is occurrence-aware CIP equivalence; symmetry is stated explicitly because the carrier's
two rings are unordered. -/
def DeclarativeLocalizedSpiroLigandPattern
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (same : input.Atom → input.Atom → Prop)
    (pattern : SpiroLigandPattern) : Prop :=
  ∃ first second,
    first ≠ second ∧
    carrier.rings = {first, second} ∧
    SpiroOccurrencePattern.PatternJudgment same
      (input.localizedCycleNeighbors first center)
      (input.localizedCycleNeighbors second center) pattern

private theorem pair_representations_eq_or_swap
    {α : Type} [DecidableEq α] {first second first' second' : α}
    (different : first ≠ second)
    (pairEq : ({first, second} : Finset α) = {first', second'}) :
    (first = first' ∧ second = second') ∨
      (first = second' ∧ second = first') := by
  have firstMem : first = first' ∨ first = second' := by
    have : first ∈ ({first', second'} : Finset α) := by
      rw [← pairEq]
      simp
    simpa using this
  have secondMem : second = first' ∨ second = second' := by
    have : second ∈ ({first', second'} : Finset α) := by
      rw [← pairEq]
      simp
    simpa using this
  rcases firstMem with firstEq | firstEq <;>
    rcases secondMem with secondEq | secondEq
  · exact False.elim (different (firstEq.trans secondEq.symm))
  · exact Or.inl ⟨firstEq, secondEq⟩
  · exact Or.inr ⟨firstEq, secondEq⟩
  · exact False.elim (different (firstEq.trans secondEq.symm))

/-- The molecular judgment may be checked against either ordering of the carrier's two rings. -/
theorem declarativeLocalizedSpiroLigandPattern_iff_of_ring_pair
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (same : input.Atom → input.Atom → Prop)
    (sameSymmetric : ∀ {left right}, same left right → same right left)
    (first second : Finset input.Atom) (different : first ≠ second)
    (ringsEq : carrier.rings = {first, second})
    (pattern : SpiroLigandPattern) :
    input.DeclarativeLocalizedSpiroLigandPattern center carrier same pattern ↔
      SpiroOccurrencePattern.PatternJudgment same
        (input.localizedCycleNeighbors first center)
        (input.localizedCycleNeighbors second center) pattern := by
  constructor
  · rintro ⟨first', second', different', ringsEq', judged⟩
    have pairEq : ({first, second} : Finset (Finset input.Atom)) = {first', second'} :=
      ringsEq.symm.trans ringsEq'
    rcases pair_representations_eq_or_swap different pairEq with sameOrder | swapped
    · simpa only [← sameOrder.1, ← sameOrder.2] using judged
    · have reversed :=
        (SpiroOccurrencePattern.patternJudgment_symmetric same _ _ sameSymmetric pattern).mp
          judged
      simpa only [← swapped.1, ← swapped.2] using reversed
  · intro judged
    exact ⟨first, second, different, ringsEq, judged⟩

theorem declarativeLocalizedSpiroLigandPattern_subsingleton
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    (same : input.Atom → input.Atom → Prop)
    (sameSymmetric : ∀ {left right}, same left right → same right left)
    {left right : SpiroLigandPattern}
    (leftJudged : input.DeclarativeLocalizedSpiroLigandPattern center carrier same left)
    (rightJudged : input.DeclarativeLocalizedSpiroLigandPattern center carrier same right) :
    left = right := by
  obtain ⟨first, second, different, ringsEq, leftPattern⟩ := leftJudged
  obtain ⟨first', second', different', ringsEq', rightPattern⟩ := rightJudged
  have pairEq : ({first, second} : Finset (Finset input.Atom)) = {first', second'} :=
    ringsEq.symm.trans ringsEq'
  have alternatives := pair_representations_eq_or_swap different pairEq
  rcases alternatives with sameOrder | swapped
  · have rightPatternAt :
        SpiroOccurrencePattern.PatternJudgment same
          (input.localizedCycleNeighbors first center)
          (input.localizedCycleNeighbors second center) right := by
      simpa only [← sameOrder.1, ← sameOrder.2] using rightPattern
    exact SpiroOccurrencePattern.patternJudgment_subsingleton same _ _
      (topology.ringNeighbors_card input center carrier first (by simp [ringsEq]))
      (topology.ringNeighbors_disjoint input center carrier first second
        (by simp [ringsEq]) (by simp [ringsEq]) different)
      leftPattern rightPatternAt
  · have rightPatternSwapped :
        SpiroOccurrencePattern.PatternJudgment same
          (input.localizedCycleNeighbors second' center)
          (input.localizedCycleNeighbors first' center) right :=
      (SpiroOccurrencePattern.patternJudgment_symmetric same _ _ sameSymmetric right).mp
        rightPattern
    have rightPatternAt :
        SpiroOccurrencePattern.PatternJudgment same
          (input.localizedCycleNeighbors first center)
          (input.localizedCycleNeighbors second center) right := by
      simpa only [← swapped.1, ← swapped.2] using rightPatternSwapped
    exact SpiroOccurrencePattern.patternJudgment_subsingleton same _ _
      (topology.ringNeighbors_card input center carrier first (by simp [ringsEq]))
      (topology.ringNeighbors_disjoint input center carrier first second
        (by simp [ringsEq]) (by simp [ringsEq]) different)
      leftPattern rightPatternAt

/-- Whole-carrier specification classifier.  It may choose either order of the two rings, whose
irrelevance is proved by the symmetric occurrence-equivalence hypothesis. -/
noncomputable def localizedSpiroLigandPattern?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (same : input.Atom → input.Atom → Prop) : Option SpiroLigandPattern := by
  classical
  if paired : ∃ first second,
      first ≠ second ∧ carrier.rings = {first, second} then
    let first := paired.choose
    let second := paired.choose_spec.choose
    exact SpiroOccurrencePattern.classify? same
      (input.localizedCycleNeighbors first center)
      (input.localizedCycleNeighbors second center)
  else
    exact none

theorem localizedSpiroLigandPattern?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    (same : input.Atom → input.Atom → Prop)
    (sameSymmetric : ∀ {left right}, same left right → same right left)
    (pattern : SpiroLigandPattern) :
    input.localizedSpiroLigandPattern? center carrier same = some pattern ↔
      input.DeclarativeLocalizedSpiroLigandPattern center carrier same pattern := by
  classical
  have paired : ∃ first second,
      first ≠ second ∧ carrier.rings = {first, second} :=
    topology.exists_distinct_rings input center carrier
  let first := paired.choose
  let second := paired.choose_spec.choose
  have different : first ≠ second := paired.choose_spec.choose_spec.1
  have ringsEq : carrier.rings = {first, second} := paired.choose_spec.choose_spec.2
  have firstPresent : first ∈ carrier.rings := by simp [ringsEq]
  have secondPresent : second ∈ carrier.rings := by simp [ringsEq]
  unfold localizedSpiroLigandPattern?
  rw [dif_pos paired]
  change SpiroOccurrencePattern.classify? same
      (input.localizedCycleNeighbors first center)
      (input.localizedCycleNeighbors second center) = some pattern ↔ _
  rw [SpiroOccurrencePattern.classify?_eq_some_iff same _ _
    (topology.ringNeighbors_card input center carrier first firstPresent)
    (topology.ringNeighbors_disjoint input center carrier first second
      firstPresent secondPresent different)]
  exact (input.declarativeLocalizedSpiroLigandPattern_iff_of_ring_pair center carrier same
    sameSymmetric first second different ringsEq pattern).symm

theorem localizedSpiroLigandPattern?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    (same : input.Atom → input.Atom → Prop)
    (sameSymmetric : ∀ {left right}, same left right → same right left) :
    input.localizedSpiroLigandPattern? center carrier same = none ↔
      ∀ pattern, ¬input.DeclarativeLocalizedSpiroLigandPattern center carrier same pattern := by
  constructor
  · intro computed pattern judged
    have someEq := (input.localizedSpiroLigandPattern?_eq_some_iff center carrier topology same
      sameSymmetric pattern).mpr judged
    rw [computed] at someEq
    simp at someEq
  · intro absent
    cases computed : input.localizedSpiroLigandPattern? center carrier same with
    | none => rfl
    | some pattern =>
        exact False.elim (absent pattern
          ((input.localizedSpiroLigandPattern?_eq_some_iff center carrier topology same
            sameSymmetric pattern).mp computed))

/-- Every one of the four topological branch starts has a successfully constructed complete CIP
key. -/
def LocalizedSpiroBranchKeysResolved
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    {κ : Type} (key? : input.Atom → Option κ) : Prop :=
  ∀ ring, ring ∈ carrier.rings →
    ∀ occurrence, occurrence ∈ input.localizedCycleNeighbors ring center →
      ∃ key, key? occurrence = some key

theorem localizedSpiroBranchKeysResolved_iff_of_ring_pair
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    {κ : Type} (key? : input.Atom → Option κ)
    (first second : Finset input.Atom)
    (ringsEq : carrier.rings = {first, second}) :
    input.LocalizedSpiroBranchKeysResolved center carrier key? ↔
      SpiroOccurrencePattern.AllBranchKeysResolved key?
        (input.localizedCycleNeighbors first center)
        (input.localizedCycleNeighbors second center) := by
  constructor
  · intro resolved occurrence present
    rw [Finset.mem_union] at present
    rcases present with firstPresent | secondPresent
    · exact resolved first (by simp [ringsEq]) occurrence firstPresent
    · exact resolved second (by simp [ringsEq]) occurrence secondPresent
  · intro resolved ring ringPresent occurrence occurrencePresent
    rw [ringsEq] at ringPresent
    simp only [Finset.mem_insert, Finset.mem_singleton] at ringPresent
    rcases ringPresent with rfl | rfl
    · exact resolved occurrence (Finset.mem_union_left _ occurrencePresent)
    · exact resolved occurrence (Finset.mem_union_right _ occurrencePresent)

/-- Whole-carrier classifier driven by an actual partial complete-key builder. -/
noncomputable def localizedSpiroLigandPatternFromKeys?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    {κ : Type} (key? : input.Atom → Option κ)
    (keyEquivalent : κ → κ → Prop) : Option SpiroLigandPattern := by
  classical
  if paired : ∃ first second,
      first ≠ second ∧ carrier.rings = {first, second} then
    let first := paired.choose
    let second := paired.choose_spec.choose
    exact SpiroOccurrencePattern.classifyResolvedKeys? key? keyEquivalent
      (input.localizedCycleNeighbors first center)
      (input.localizedCycleNeighbors second center)
  else
    exact none

theorem localizedSpiroLigandPatternFromKeys?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    {κ : Type} (key? : input.Atom → Option κ)
    (keyEquivalent : κ → κ → Prop)
    (keyEquivalentSymmetric : ∀ {left right},
      keyEquivalent left right → keyEquivalent right left)
    (pattern : SpiroLigandPattern) :
    input.localizedSpiroLigandPatternFromKeys? center carrier key? keyEquivalent = some pattern ↔
      input.LocalizedSpiroBranchKeysResolved center carrier key? ∧
        input.DeclarativeLocalizedSpiroLigandPattern center carrier
          (SpiroOccurrencePattern.SameResolvedKey key? keyEquivalent) pattern := by
  classical
  have paired : ∃ first second,
      first ≠ second ∧ carrier.rings = {first, second} :=
    topology.exists_distinct_rings input center carrier
  let first := paired.choose
  let second := paired.choose_spec.choose
  have different : first ≠ second := paired.choose_spec.choose_spec.1
  have ringsEq : carrier.rings = {first, second} := paired.choose_spec.choose_spec.2
  have firstPresent : first ∈ carrier.rings := by simp [ringsEq]
  have secondPresent : second ∈ carrier.rings := by simp [ringsEq]
  unfold localizedSpiroLigandPatternFromKeys?
  rw [dif_pos paired]
  change SpiroOccurrencePattern.classifyResolvedKeys? key? keyEquivalent
      (input.localizedCycleNeighbors first center)
      (input.localizedCycleNeighbors second center) = some pattern ↔ _
  rw [SpiroOccurrencePattern.classifyResolvedKeys?_eq_some_iff key? keyEquivalent _ _
    (topology.ringNeighbors_card input center carrier first firstPresent)
    (topology.ringNeighbors_disjoint input center carrier first second
      firstPresent secondPresent different)]
  rw [← input.localizedSpiroBranchKeysResolved_iff_of_ring_pair center carrier key?
    first second ringsEq]
  rw [← input.declarativeLocalizedSpiroLigandPattern_iff_of_ring_pair center carrier
    (SpiroOccurrencePattern.SameResolvedKey key? keyEquivalent)
    (SpiroOccurrencePattern.sameResolvedKey_symmetric key? keyEquivalent
      keyEquivalentSymmetric)
    first second different ringsEq pattern]

theorem localizedSpiroLigandPatternFromKeys?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    {κ : Type} (key? : input.Atom → Option κ)
    (keyEquivalent : κ → κ → Prop)
    (keyEquivalentSymmetric : ∀ {left right},
      keyEquivalent left right → keyEquivalent right left) :
    input.localizedSpiroLigandPatternFromKeys? center carrier key? keyEquivalent = none ↔
      ¬input.LocalizedSpiroBranchKeysResolved center carrier key? ∨
        ∀ pattern, ¬input.DeclarativeLocalizedSpiroLigandPattern center carrier
          (SpiroOccurrencePattern.SameResolvedKey key? keyEquivalent) pattern := by
  constructor
  · intro computed
    by_cases resolved : input.LocalizedSpiroBranchKeysResolved center carrier key?
    · right
      intro pattern judged
      have someEq := (input.localizedSpiroLigandPatternFromKeys?_eq_some_iff center carrier
        topology key? keyEquivalent keyEquivalentSymmetric pattern).mpr ⟨resolved, judged⟩
      rw [computed] at someEq
      simp at someEq
    · exact Or.inl resolved
  · intro refused
    cases computed : input.localizedSpiroLigandPatternFromKeys? center carrier key?
        keyEquivalent with
    | none => rfl
    | some pattern =>
        have accepted := (input.localizedSpiroLigandPatternFromKeys?_eq_some_iff center carrier
          topology key? keyEquivalent keyEquivalentSymmetric pattern).mp computed
        rcases refused with unresolved | noPattern
        · exact False.elim (unresolved accepted.1)
        · exact False.elim (noPattern pattern accepted.2)

/-- Direct complete-comparator spelling of the guarded molecular classifier. -/
noncomputable def localizedSpiroLigandPatternFromComparator?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    {κ : Type} (key? : input.Atom → Option κ)
    (compare : κ → κ → Ordering) : Option SpiroLigandPattern :=
  input.localizedSpiroLigandPatternFromKeys? center carrier key?
    (SpiroOccurrencePattern.ComparatorTie compare)

theorem localizedSpiroLigandPatternFromComparator?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    {κ : Type} (key? : input.Atom → Option κ)
    (compare : κ → κ → Ordering) [Std.OrientedCmp compare]
    (pattern : SpiroLigandPattern) :
    input.localizedSpiroLigandPatternFromComparator? center carrier key? compare = some pattern ↔
      input.LocalizedSpiroBranchKeysResolved center carrier key? ∧
        input.DeclarativeLocalizedSpiroLigandPattern center carrier
          (SpiroOccurrencePattern.SameResolvedKey key?
            (SpiroOccurrencePattern.ComparatorTie compare)) pattern := by
  exact input.localizedSpiroLigandPatternFromKeys?_eq_some_iff center carrier topology key?
    (SpiroOccurrencePattern.ComparatorTie compare)
    (SpiroOccurrencePattern.comparatorTie_symmetric compare) pattern

theorem localizedSpiroLigandPatternFromComparator?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (topology : input.DeclarativeLocalizedSpiroCenter center carrier)
    {κ : Type} (key? : input.Atom → Option κ)
    (compare : κ → κ → Ordering) [Std.OrientedCmp compare] :
    input.localizedSpiroLigandPatternFromComparator? center carrier key? compare = none ↔
      ¬input.LocalizedSpiroBranchKeysResolved center carrier key? ∨
        ∀ pattern, ¬input.DeclarativeLocalizedSpiroLigandPattern center carrier
          (SpiroOccurrencePattern.SameResolvedKey key?
            (SpiroOccurrencePattern.ComparatorTie compare)) pattern := by
  exact input.localizedSpiroLigandPatternFromKeys?_eq_none_iff center carrier topology key?
    (SpiroOccurrencePattern.ComparatorTie compare)
    (SpiroOccurrencePattern.comparatorTie_symmetric compare)

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
