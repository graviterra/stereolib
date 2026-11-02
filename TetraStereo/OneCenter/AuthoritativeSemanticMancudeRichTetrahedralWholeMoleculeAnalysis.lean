import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6RSPseudoTotality
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteTetrahedralExactOnceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Whole-molecule source analysis retaining tetrahedral descriptor case

The complete Rules 1a--6 source endpoint already returns the chemically significant four-way
descriptor type `R/S/r/s`.  This module lifts that endpoint over every canonical tetrahedral
center without projecting it back to bare `R/S`.  Success, refusal, uniqueness, and literal
count are characterized by the exact rich endpoint judgment.
-/

/-- Parameter-free source-canonical rich tetrahedral endpoint. -/
noncomputable def aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center

/-- Independent exact meaning of the parameter-free rich endpoint. -/
abbrev AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center descriptor

/-- Descriptor-free exact readiness of the parameter-free rich endpoint. -/
abbrev AromaticCanonicalConcreteRule3Through6RSPseudoReady
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  source.AromaticCanonicalScheduledRule3Through6RSPseudoReady
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center

theorem aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?_eq_some_iff
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
        carrierFuel ruleFuel center = some descriptor ↔
      source.AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
        carrierFuel ruleFuel center descriptor :=
  source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center descriptor

theorem aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?_isSome_iff_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
        carrierFuel ruleFuel center).isSome = true ↔
      source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
        carrierFuel ruleFuel center :=
  source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_isSome_iff_ready
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center

theorem aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?_eq_none_iff_not_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
        carrierFuel ruleFuel center = none ↔
      ¬source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
        carrierFuel ruleFuel center :=
  source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_iff_not_ready
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center

/-- One rich tetrahedral assignment retaining uppercase/lowercase descriptor case. -/
structure AromaticCanonicalRule3Through6RSPseudoAssignment
    (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  descriptor : LocalizedTetrahedralRSPseudoDescriptor
  deriving DecidableEq

/-- Analyze every canonical source tetrahedral center with the rich endpoint. -/
noncomputable def analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalRule3Through6RSPseudoAssignment :=
  source.aromaticCanonicalTetrahedralCenters.filterMap fun center =>
    (source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
      carrierFuel ruleFuel center).map fun descriptor => { center, descriptor }

/-- Exact list membership is the independent rich endpoint judgment. -/
theorem mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalRule3Through6RSPseudoAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
        carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
        carrierFuel ruleFuel assignment.center assignment.descriptor := by
  constructor
  · intro present
    rw [analyzeAromaticCanonicalConcreteRule3Through6RSPseudo,
      List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, observed⟩ := present
    cases computed : source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
        carrierFuel ruleFuel center with
    | none => simp [computed] at observed
    | some descriptor =>
        simp [computed] at observed
        subst assignment
        exact
          (source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?_eq_some_iff
            carrierFuel ruleFuel center descriptor).mp computed
  · intro judged
    rw [analyzeAromaticCanonicalConcreteRule3Through6RSPseudo,
      List.mem_filterMap]
    refine ⟨assignment.center,
      (source.mem_aromaticCanonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2, ?_⟩
    have computed :=
      (source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?_eq_some_iff
        carrierFuel ruleFuel assignment.center assignment.descriptor).mpr judged
    simp [computed]

/-- The rich whole-molecule tetrahedral result has no duplicate assignment. -/
theorem analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
      carrierFuel ruleFuel).Nodup := by
  unfold analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
  apply source.aromaticCanonicalTetrahedralCenters_nodup.filterMap
  intro left right assignment leftEmitted rightEmitted
  cases leftComputed : source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
      carrierFuel ruleFuel left with
  | none => simp [leftComputed] at leftEmitted
  | some leftDescriptor =>
      cases rightComputed : source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?
          carrierFuel ruleFuel right with
      | none => simp [rightComputed] at rightEmitted
      | some rightDescriptor =>
          simp [leftComputed] at leftEmitted
          simp [rightComputed] at rightEmitted
          exact
            (congrArg AromaticCanonicalRule3Through6RSPseudoAssignment.center
              leftEmitted).trans
            (congrArg AromaticCanonicalRule3Through6RSPseudoAssignment.center
              rightEmitted).symm

/-- A canonical center has an emitted rich assignment exactly when it is rich-endpoint ready. -/
theorem exists_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ assignment,
        assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
          carrierFuel ruleFuel ∧ assignment.center = center) ↔
      source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
        carrierFuel ruleFuel center := by
  constructor
  · rintro ⟨assignment, present, centerIdentity⟩
    have judged :=
      (source.mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff
        carrierFuel ruleFuel assignment).mp present
    refine ⟨assignment.descriptor, ?_⟩
    simpa [centerIdentity] using judged
  · rintro ⟨descriptor, judged⟩
    let assignment : source.AromaticCanonicalRule3Through6RSPseudoAssignment :=
      { center, descriptor }
    exact ⟨assignment,
      (source.mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff
        carrierFuel ruleFuel assignment).mpr judged, rfl⟩

/-- Refusal at one physical center is exactly failure of rich endpoint readiness. -/
theorem no_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_not_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (¬∃ assignment,
        assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
          carrierFuel ruleFuel ∧ assignment.center = center) ↔
      ¬source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
        carrierFuel ruleFuel center := by
  rw [source.exists_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready]

/-- Rich readiness gives one and only one assignment for the physical center. -/
theorem existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃! assignment,
        assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
          carrierFuel ruleFuel ∧ assignment.center = center) ↔
      source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
        carrierFuel ruleFuel center := by
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact
      (source.exists_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready
        carrierFuel ruleFuel center).mp ⟨assignment, property⟩
  · intro ready
    obtain ⟨assignment, assignmentPresent, assignmentCenter⟩ :=
      (source.exists_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready
        carrierFuel ruleFuel center).mpr ready
    refine ⟨assignment, ⟨assignmentPresent, assignmentCenter⟩, ?_⟩
    intro other ⟨otherPresent, otherCenter⟩
    have assignmentComputed :=
      (source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?_eq_some_iff
        carrierFuel ruleFuel assignment.center assignment.descriptor).mpr
        ((source.mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff
          carrierFuel ruleFuel assignment).mp assignmentPresent)
    have otherComputed :=
      (source.aromaticCanonicalConcreteRule3Through6RSPseudoDescriptor?_eq_some_iff
        carrierFuel ruleFuel other.center other.descriptor).mpr
        ((source.mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff
          carrierFuel ruleFuel other).mp otherPresent)
    have descriptorIdentity : other.descriptor = assignment.descriptor := by
      rw [otherCenter, ← assignmentCenter, assignmentComputed] at otherComputed
      exact Option.some.inj otherComputed.symm
    cases assignment
    cases other
    simp only at assignmentCenter otherCenter descriptorIdentity
    subst_vars
    rfl

/-- Literal count one is equivalent to rich endpoint readiness. -/
theorem exists_count_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_eq_one_iff_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ assignment,
        assignment.center = center ∧
          (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
            carrierFuel ruleFuel).count assignment = 1) ↔
      source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
        carrierFuel ruleFuel center := by
  constructor
  · rintro ⟨assignment, centerIdentity, countOne⟩
    apply
      (source.exists_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready
        carrierFuel ruleFuel center).mp
    refine ⟨assignment, ?_, centerIdentity⟩
    exact List.count_pos_iff.mp (by omega)
  · intro ready
    obtain ⟨assignment, property, _unique⟩ :=
      (source.existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready
        carrierFuel ruleFuel center).mpr ready
    refine ⟨assignment, property.2, ?_⟩
    rw [(source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_nodup
      carrierFuel ruleFuel).count]
    simp [property.1]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
