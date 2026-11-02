import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
# Saturated localized constitutional-to-Rule-5 pipeline

Rule 3 cannot be skipped merely because no geometry was supplied.  This module provides a first
closed molecular subdomain: every localized bond has order at most one, so no double-bond or
cumulene Rule-3 unit can occur.  Only after an exhaustive Rules-1a--2 tie and this checked Rule-3
nonapplicability witness does comparison enter the recursive uppercase-seed Rules 4a, 4b, and 5
implementation.
-/

namespace CertifiedLocalizedCIPInput

/-- Sufficient molecule-level Rule-3 nonapplicability condition for the localized covalent graph. -/
def SaturatedLocalizedMolecule (input : CertifiedLocalizedCIPInput) : Prop :=
  ∀ left right : input.Atom, input.moleculeGraph.bond left right ≤ 1

/-- Executable finite check of the saturated localized subdomain. -/
def saturatedLocalizedMolecule? (input : CertifiedLocalizedCIPInput) : Bool :=
  (List.finRange input.certified.input.molecule.atomCount).all fun left =>
    (List.finRange input.certified.input.molecule.atomCount).all fun right =>
      decide (input.moleculeGraph.bond left right ≤ 1)

@[simp] theorem saturatedLocalizedMolecule?_eq_true_iff
    (input : CertifiedLocalizedCIPInput) :
    input.saturatedLocalizedMolecule? = true ↔ input.SaturatedLocalizedMolecule := by
  simp [saturatedLocalizedMolecule?, SaturatedLocalizedMolecule]

/-- Rules-1a--2 followed, only on a complete tie, by proved Rule-3 nonapplicability and the
recursive uppercase-seed Rules-4a/4b/5 comparison. -/
def compareLocalizedSaturatedThroughRule5At?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  match input.compareRuleMajorConstitutionAt? center left right with
  | none => none
  | some constitutional =>
      match constitutional.outcome with
      | Ordering.lt => some { ordering := Ordering.lt }
      | Ordering.gt => some { ordering := Ordering.gt }
      | Ordering.eq =>
          if !input.saturatedLocalizedMolecule? then none else
            input.compareLocalizedRecursiveUppercaseRule45AfterPriorTieAt?
              center left right

/-- Independent comparison relation for the saturated localized subdomain. -/
def DeclarativeLocalizedSaturatedThroughRule5At
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison) : Prop :=
  (∃ trace,
    input.DeclarativeRuleMajorConstitutionalTrace center left right trace ∧
    cipTraceOutcome trace ≠ Ordering.eq ∧
    result = { ordering := cipTraceOutcome trace }) ∨
  (∃ trace,
    input.DeclarativeRuleMajorConstitutionalTrace center left right trace ∧
    cipTraceOutcome trace = Ordering.eq ∧
    input.SaturatedLocalizedMolecule ∧
    input.DeclarativeLocalizedRecursiveUppercaseRule45AfterPriorTieAt
      center left right result)

theorem compareLocalizedSaturatedThroughRule5At?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (result : ConstitutionalDescriptorHierarchyComparison)
    (computed : input.compareLocalizedSaturatedThroughRule5At?
      center left right = some result) :
    input.DeclarativeLocalizedSaturatedThroughRule5At
      center left right result := by
  unfold compareLocalizedSaturatedThroughRule5At? at computed
  cases constitutionalComputed :
      input.compareRuleMajorConstitutionAt? center left right with
  | none => simp [constitutionalComputed] at computed
  | some constitutional =>
      cases outcome : constitutional.outcome with
      | eq =>
        simp only [constitutionalComputed, outcome] at computed
        cases saturated : input.saturatedLocalizedMolecule? with
        | false =>
            simp only [saturated, Bool.not_false, if_pos] at computed
            contradiction
        | true =>
            simp only [saturated, Bool.not_true, Bool.false_eq_true,
              if_false] at computed
            exact Or.inr ⟨constitutional.trace,
              input.compareRuleMajorConstitutionAt?_sound_declarative_trace
                center left right constitutional constitutionalComputed,
              constitutional.sound.trans outcome,
              (input.saturatedLocalizedMolecule?_eq_true_iff).mp saturated,
              input.compareLocalizedRecursiveUppercaseRule45AfterPriorTieAt?_sound
                center left right result computed⟩
      | lt =>
        simp [constitutionalComputed, outcome] at computed
        subst result
        have traceStrict : cipTraceOutcome constitutional.trace ≠ Ordering.eq := by
          rw [constitutional.sound]
          simp [outcome]
        exact Or.inl ⟨constitutional.trace,
          input.compareRuleMajorConstitutionAt?_sound_declarative_trace
            center left right constitutional constitutionalComputed,
          traceStrict, by
            exact congrArg
              (fun ordering =>
                ({ ordering := ordering } :
                  ConstitutionalDescriptorHierarchyComparison))
              (outcome.symm.trans constitutional.sound.symm)⟩
      | gt =>
        simp [constitutionalComputed, outcome] at computed
        subst result
        have traceStrict : cipTraceOutcome constitutional.trace ≠ Ordering.eq := by
          rw [constitutional.sound]
          simp [outcome]
        exact Or.inl ⟨constitutional.trace,
          input.compareRuleMajorConstitutionAt?_sound_declarative_trace
            center left right constitutional constitutionalComputed,
          traceStrict, by
            exact congrArg
              (fun ordering =>
                ({ ordering := ordering } :
                  ConstitutionalDescriptorHierarchyComparison))
              (outcome.symm.trans constitutional.sound.symm)⟩

/-- The actual four-position stable sort using the complete saturated localized comparison. -/
def saturatedTrackedLigandOrderAt?
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : Option TrackedLocalizedLigandOrder :=
  sortFourLocalizedLigandsTracked
    (input.compareLocalizedSaturatedThroughRule5At? center)

/-- Every comparison equation retained by a tracked insertion can be replaced by its independent
molecule-to-comparison derivation. -/
inductive DeclarativeSaturatedTrackedLigandInsertion
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (candidate : Fin 4) :
    List (Fin 4) → TrackedLocalizedLigandInsertion → Prop
  | nil : DeclarativeSaturatedTrackedLigandInsertion input center candidate []
      { lowestFirst := [candidate], pseudoComparisons := 0 }
  | placeBefore {low remaining comparison}
      (compared : input.DeclarativeLocalizedSaturatedThroughRule5At
        center low candidate comparison)
      (higherLow : comparison.ordering = Ordering.gt) :
      DeclarativeSaturatedTrackedLigandInsertion input center candidate (low :: remaining)
        { lowestFirst := candidate :: low :: remaining
          pseudoComparisons := if comparison.pseudo then 1 else 0 }
  | placeAfter {low remaining comparison deeper}
      (compared : input.DeclarativeLocalizedSaturatedThroughRule5At
        center low candidate comparison)
      (lowerLow : comparison.ordering = Ordering.lt)
      (tail : DeclarativeSaturatedTrackedLigandInsertion
        input center candidate remaining deeper) :
      DeclarativeSaturatedTrackedLigandInsertion input center candidate (low :: remaining)
        { lowestFirst := low :: deeper.lowestFirst
          pseudoComparisons :=
            (if comparison.pseudo then 1 else 0) + deeper.pseudoComparisons }

theorem DeclarativeTrackedLocalizedLigandInsertion.toSaturated
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) {candidate : Fin 4}
    {existing : List (Fin 4)} {result : TrackedLocalizedLigandInsertion}
    (derivation : DeclarativeTrackedLocalizedLigandInsertion
      (input.compareLocalizedSaturatedThroughRule5At? center)
      candidate existing result) :
    input.DeclarativeSaturatedTrackedLigandInsertion center candidate existing result := by
  induction derivation with
  | nil => exact DeclarativeSaturatedTrackedLigandInsertion.nil
  | placeBefore compared higherLow =>
      exact DeclarativeSaturatedTrackedLigandInsertion.placeBefore
        (input.compareLocalizedSaturatedThroughRule5At?_sound
          center _ _ _ compared) higherLow
  | placeAfter compared lowerLow tail ih =>
      exact DeclarativeSaturatedTrackedLigandInsertion.placeAfter
        (input.compareLocalizedSaturatedThroughRule5At?_sound
          center _ _ _ compared) lowerLow ih

/-- Complete proof-relevant stable-sort derivation whose every comparison has independent
molecular semantics. -/
inductive DeclarativeSaturatedTrackedLigandSort
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) :
    List (Fin 4) → List (Fin 4) → ℕ →
      TrackedLocalizedLigandOrder → Prop
  | nil (lowestFirst : List (Fin 4)) (pseudoComparisons : ℕ) :
      DeclarativeSaturatedTrackedLigandSort input center [] lowestFirst pseudoComparisons
        { highestFirst := lowestFirst.reverse
          pseudoComparisons := pseudoComparisons }
  | cons {candidate candidates lowestFirst pseudoComparisons inserted result}
      (insertion : DeclarativeSaturatedTrackedLigandInsertion input center candidate
        lowestFirst inserted)
      (tail : DeclarativeSaturatedTrackedLigandSort input center candidates
        inserted.lowestFirst
        (pseudoComparisons + inserted.pseudoComparisons) result) :
      DeclarativeSaturatedTrackedLigandSort input center (candidate :: candidates)
        lowestFirst pseudoComparisons result

theorem DeclarativeTrackedLocalizedLigandSort.toSaturated
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    {candidates lowestFirst : List (Fin 4)} {pseudoComparisons : ℕ}
    {result : TrackedLocalizedLigandOrder}
    (derivation : DeclarativeTrackedLocalizedLigandSort
      (input.compareLocalizedSaturatedThroughRule5At? center)
      candidates lowestFirst pseudoComparisons result) :
    input.DeclarativeSaturatedTrackedLigandSort center candidates
      lowestFirst pseudoComparisons result := by
  induction derivation with
  | nil => exact DeclarativeSaturatedTrackedLigandSort.nil _ _
  | cons insertion tail ih =>
      exact DeclarativeSaturatedTrackedLigandSort.cons
        (CertifiedLocalizedCIPInput.DeclarativeTrackedLocalizedLigandInsertion.toSaturated
          input center insertion) ih

theorem saturatedTrackedLigandOrderAt?_sound
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (result : TrackedLocalizedLigandOrder)
    (computed : input.saturatedTrackedLigandOrderAt? center = some result) :
    input.DeclarativeSaturatedTrackedLigandSort center
      (List.finRange 4) [] 0 result := by
  exact CertifiedLocalizedCIPInput.DeclarativeTrackedLocalizedLigandSort.toSaturated
    input center (sortFourLocalizedLigandsTracked_sound
      (input.compareLocalizedSaturatedThroughRule5At? center) result computed)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
