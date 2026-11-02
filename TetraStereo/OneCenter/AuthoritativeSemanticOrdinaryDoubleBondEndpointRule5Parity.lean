import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondEndpointRule3Through5

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Rule-5 parity derived at an ordinary-double-bond endpoint

An ordinary planar endpoint has two represented substituent occurrences after implicit-hydrogen
materialization.  This module selects the strict Rules-1a--5 senior occurrence and retains the
enantiomorphic Rule-5 bit which determines whether the final descriptor family is ordinary `Z/E`
or sequence `seqCis/seqTrans`.
-/

/-- Endpoint result needed by planar geometry: the represented reference atom, its exact
occurrence candidate, and whether the decisive priority was enantiomorphic Rule 5. -/
structure AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  candidate : source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate carrierFuel
  reference : source.AromaticCanonicalAtom
  enantiomorphic : Bool

/-- Executable two-substituent endpoint selector.  A tied comparison refuses assignment.  The
reverse comparison is checked explicitly, so the implementation does not assume comparator
antisymmetry at the executable boundary. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) :
    Option (source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel) := by
  classical
  exact match frame.ranked with
  | [left, right] =>
      let leftComparison :=
        source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
          left.2 right.2
      if leftSenior : leftComparison.ordering = Ordering.gt then do
        let reference ← left.1.occurrence.1.node.current?
        some { candidate := left
               reference
               enantiomorphic := leftComparison.pseudo }
      else
        let rightComparison :=
          source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
            right.2 left.2
        if rightSenior : rightComparison.ordering = Ordering.gt then do
          let reference ← right.1.occurrence.1.node.current?
          some { candidate := right
                 reference
                 enantiomorphic := rightComparison.pseudo }
        else none
  | _ => none

/-- Exact executable judgment, including the deliberate left-first branch of the selector. -/
def AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
      carrierFuel) : Prop :=
  match frame.ranked with
  | [left, right] =>
    (selection.candidate = left ∧
        left.1.occurrence.1.node.current? = some selection.reference ∧
        (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
          left.2 right.2).ordering = Ordering.gt ∧
        (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
          left.2 right.2).pseudo = selection.enantiomorphic) ∨
      ((source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
          left.2 right.2).ordering ≠ Ordering.gt ∧
        selection.candidate = right ∧
        right.1.occurrence.1.node.current? = some selection.reference ∧
        (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
          right.2 left.2).ordering = Ordering.gt ∧
        (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
          right.2 left.2).pseudo = selection.enantiomorphic)
  | _ => False

/-- Independent positive chemical meaning of an endpoint Rule-5 selection.  It does not retain
the executable's left-first implementation detail. -/
def DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
      carrierFuel) : Prop :=
  ∃ senior junior,
    (frame.ranked = [senior, junior] ∨ frame.ranked = [junior, senior]) ∧
      selection.candidate = senior ∧
      senior.1.occurrence.1.node.current? = some selection.reference ∧
      (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
        senior.2 junior.2).ordering = Ordering.gt ∧
      (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
        senior.2 junior.2).pseudo = selection.enantiomorphic

/-- Exact success boundary for automatic endpoint Rule-5 parity derivation. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
      carrierFuel) :
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame = some selection ↔
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
        frame selection := by
  classical
  rcases selection with ⟨selectedCandidate, selectedReference, selectedParity⟩
  unfold aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?
    AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
  generalize rankedEq : frame.ranked = ranked
  cases ranked with
  | nil => simp
  | cons left tail =>
      cases tail with
      | nil => simp
      | cons right rest =>
          cases rest with
          | cons third rest => simp
          | nil =>
              generalize leftComparisonEq :
                  source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
                    left.2 right.2 = leftComparison
              cases leftComparison with
              | mk leftOrdering leftPseudo =>
                cases leftOrdering with
                | gt =>
                    cases currentEq : left.1.occurrence.1.node.current? <;>
                      simp [leftComparisonEq, currentEq, eq_comm]
                | lt =>
                    generalize rightComparisonEq :
                        source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
                          right.2 left.2 = rightComparison
                    cases rightComparison with
                    | mk rightOrdering rightPseudo =>
                      cases rightOrdering <;>
                        cases currentEq : right.1.occurrence.1.node.current? <;>
                          simp [leftComparisonEq, rightComparisonEq, currentEq, eq_comm]
                | eq =>
                    generalize rightComparisonEq :
                        source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
                          right.2 left.2 = rightComparison
                    cases rightComparison with
                    | mk rightOrdering rightPseudo =>
                      cases rightOrdering <;>
                        cases currentEq : right.1.occurrence.1.node.current? <;>
                          simp [leftComparisonEq, rightComparisonEq, currentEq, eq_comm]

/-- The exact executable endpoint judgment always entails the independent chemical judgment. -/
theorem AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment.sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel)
    (judgment : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
      frame selection) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
      frame selection := by
  unfold AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment at judgment
  generalize rankedEq : frame.ranked = ranked at judgment
  cases ranked with
  | nil => contradiction
  | cons left tail =>
      cases tail with
      | nil => contradiction
      | cons right rest =>
          cases rest with
          | cons third rest => contradiction
          | nil =>
              rcases judgment with leftCase | rightCase
              · exact ⟨left, right, Or.inl rankedEq, leftCase.1, leftCase.2.1,
                  leftCase.2.2.1, leftCase.2.2.2⟩
              · exact ⟨right, left, Or.inr rankedEq, rightCase.2.1,
                  rightCase.2.2.1, rightCase.2.2.2.1, rightCase.2.2.2.2⟩

/-- The independent two-ligand endpoint judgment is sufficient for the executable selector.
Lawful orientation of the Rules-1a--5 comparator proves that when the senior ligand occupies the
second list position, the left-first branch cannot incorrectly claim the junior ligand. -/
theorem DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection.complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel)
    (judgment : source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
      frame selection) :
    source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
      frame selection := by
  obtain ⟨senior, junior, positioned, candidate, current, ordering, parity⟩ := judgment
  rcases positioned with positioned | positioned
  · unfold AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
    rw [positioned]
    exact Or.inl ⟨candidate, current, ordering, parity⟩
  · have seniorKeyGt :
        source.compareAromaticCanonicalOccurrenceRule3Through5Keys
          senior.2 junior.2 = Ordering.gt := by
      rw [← source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_ordering]
      exact ordering
    letI : Std.TransCmp source.compareAromaticCanonicalOccurrenceRule3Through5Keys :=
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys_transCmp
    have oriented := @Std.OrientedCmp.eq_swap _
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys _ senior.2 junior.2
    have juniorKeyLt :
        source.compareAromaticCanonicalOccurrenceRule3Through5Keys
          junior.2 senior.2 = Ordering.lt := by
      generalize reverseEq :
          source.compareAromaticCanonicalOccurrenceRule3Through5Keys
            junior.2 senior.2 = reverse at oriented
      cases reverse <;> simp_all
    have juniorNotSenior :
        (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
          junior.2 senior.2).ordering ≠ Ordering.gt := by
      rw [source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_ordering,
        juniorKeyLt]
      decide
    unfold AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
    rw [positioned]
    exact Or.inr ⟨juniorNotSenior, candidate, current, ordering, parity⟩

/-- Fully independent exact success theorem for automatic endpoint Rule-5 selection. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel) :
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame = some selection ↔
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
        frame selection := by
  constructor
  · intro computed
    exact (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff
      frame selection).mp computed |>.sound
  · intro judgment
    exact (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff
      frame selection).mpr judgment.complete

/-- Every independently selected two-substituent endpoint candidate is the strict Rules-1a--5
maximum in its frame. -/
theorem DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection.strictlySenior
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel)
    (judgment : source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
      frame selection) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
      frame.ranked selection.candidate := by
  obtain ⟨senior, junior, ranked | ranked, candidate, current, ordering, pseudo⟩ := judgment
  · rw [candidate]
    refine ⟨by simp [ranked], ?_⟩
    intro other present different
    simp [ranked] at present
    rcases present with rfl | rfl
    · exact False.elim (different rfl)
    · rw [← source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_ordering]
      exact ordering
  · rw [candidate]
    refine ⟨by simp [ranked], ?_⟩
    intro other present different
    simp [ranked] at present
    rcases present with rfl | rfl
    · rw [← source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_ordering]
      exact ordering
    · exact False.elim (different rfl)

/-- Every emitted automatic endpoint result is an independent Rule-5 selection. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel)
    (computed : source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame =
      some selection) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
      frame selection :=
  (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff
    frame selection).mp computed |>.sound

/-- With an independently derived frame, an emitted endpoint reference is real, represented,
distinct from the double-bond partner, and carries the exact decisive Rule-5 parity. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_reference_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel)
    (frameDerived :
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel endpoint partner view evaluationFuel frame)
    (selection : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection carrierFuel)
    (computed : source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame =
      some selection) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
        frame.ranked selection.candidate ∧
      selection.candidate.1.occurrence.1.node.current? = some selection.reference ∧
      selection.reference ≠ partner := by
  have selected := source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_sound
    frame selection computed
  have senior := selected.strictlySenior
  obtain ⟨selectedCandidate, junior, positioned, candidateEq, selectedCurrent,
    ordering, parity⟩ := selected
  have selectedCurrent' :
      selection.candidate.1.occurrence.1.node.current? = some selection.reference := by
    rw [candidateEq]
    exact selectedCurrent
  obtain ⟨reference, current, different⟩ :=
    source.exists_reference_of_declarativeEndpointStrictlySenior
      endpoint partner view evaluationFuel frame frameDerived selection.candidate senior
  rw [selectedCurrent'] at current
  injection current with identity
  subst reference
  exact ⟨senior, selectedCurrent', different⟩

/-- Exact fail-closed boundary for endpoint parity: refusal means that no executable two-ligand
selection judgment exists. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_none_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel) :
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame = none ↔
      ¬ ∃ selection,
        source.AromaticCanonicalOrdinaryDoubleBondEndpointRule5ExecutableJudgment
          frame selection := by
  constructor
  · intro refused ⟨selection, judgment⟩
    have emitted :=
      (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff
        frame selection).mpr judgment
    rw [refused] at emitted
    contradiction
  · intro absent
    cases computed : source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame with
    | none => rfl
    | some selection =>
        exfalso
        apply absent
        exact ⟨selection,
          (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff
            frame selection).mp computed⟩

/-- Independent exact refusal theorem: automatic endpoint selection returns `none` precisely
when no declarative two-ligand strict Rules-1a--5 selection exists. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_none_iff_no_declarative
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame carrierFuel) :
    source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame = none ↔
      ¬ ∃ selection,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection
          frame selection := by
  constructor
  · intro refused ⟨selection, judgment⟩
    have emitted :=
      (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
        frame selection).mpr judgment
    rw [refused] at emitted
    contradiction
  · intro absent
    cases computed : source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection? frame with
    | none => rfl
    | some selection =>
        exfalso
        apply absent
        exact ⟨selection,
          (source.aromaticCanonicalOrdinaryDoubleBondEndpointRule5Selection?_eq_some_iff_declarative
            frame selection).mp computed⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
