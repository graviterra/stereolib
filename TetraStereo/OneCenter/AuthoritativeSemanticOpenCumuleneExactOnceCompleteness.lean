import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneFiniteCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedCyclicCumuleneAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact-once completeness for source-canonical open cumulenes

Finite-fuel completeness supplies an output for every independently ready odd or even open
cumulene.  Here the output is tied back to its exact canonical physical-unit list, the two family
analyzers are proved duplicate-free, and existence is strengthened to uniqueness by physical-unit
identity.
-/

/-- A successful odd-route computation retains the exact canonical physical unit supplied to it. -/
theorem aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment)
    (computed : source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
      carrierFuel ruleFuel unit = some assignment) :
    assignment.unit = unit := by
  have mapIdentity :
      (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit).map (fun result => result.unit) =
        (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit).map (fun _ => unit) := by
    simp [aromaticCanonicalOddOpenCumuleneSpatialAssignment?]
  rw [computed] at mapIdentity
  exact Option.some.inj mapIdentity

/-- A successful even-route computation retains the exact canonical physical unit supplied to it. -/
theorem aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment)
    (computed : source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
      carrierFuel ruleFuel unit = some assignment) :
    assignment.unit = unit := by
  have mapIdentity :
      (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit).map (fun result => result.unit) =
        (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit).map (fun _ => unit) := by
    simp [aromaticCanonicalEvenOpenCumuleneAxialAssignment?]
  rw [computed] at mapIdentity
  exact Option.some.inj mapIdentity

/-- Canonical physical-unit uniqueness and per-unit `Option` determinism make the odd whole-source
result duplicate-free. -/
theorem analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
      carrierFuel ruleFuel).Nodup := by
  unfold analyzeAromaticCanonicalOddOpenCumuleneSpatial
  apply source.aromaticCanonicalOddOpenCumuleneUnits_nodup.filterMap
  intro left right assignment leftEmitted rightEmitted
  have leftUnit := source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
    carrierFuel ruleFuel left assignment (by simpa using leftEmitted)
  have rightUnit := source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
    carrierFuel ruleFuel right assignment (by simpa using rightEmitted)
  exact leftUnit.symm.trans rightUnit

/-- The even whole-source result is duplicate-free for the same exact physical-unit reason. -/
theorem analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
      carrierFuel ruleFuel).Nodup := by
  unfold analyzeAromaticCanonicalEvenOpenCumuleneAxial
  apply source.aromaticCanonicalEvenOpenCumuleneUnits_nodup.filterMap
  intro left right assignment leftEmitted rightEmitted
  have leftUnit := source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
    carrierFuel ruleFuel left assignment (by simpa using leftEmitted)
  have rightUnit := source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
    carrierFuel ruleFuel right assignment (by simpa using rightEmitted)
  exact leftUnit.symm.trans rightUnit

/-- Every independently ready odd physical unit has exactly one assignment in the whole-source
odd-route result. -/
theorem existsUnique_mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃! assignment,
      assignment ∈ source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
          carrierFuel ruleFuel ∧
        assignment.unit = unit := by
  obtain ⟨assignment, emitted⟩ :=
    source.exists_aromaticCanonicalOddOpenCumuleneSpatialAssignment_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  have assignmentUnit :=
    source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
      carrierFuel ruleFuel unit assignment emitted
  have assignmentPresent : assignment ∈
      source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel :=
    (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
      carrierFuel ruleFuel assignment).mpr ⟨unit, evidence.owner, emitted⟩
  refine ⟨assignment, ⟨assignmentPresent, assignmentUnit⟩, ?_⟩
  intro other ⟨otherPresent, otherUnit⟩
  obtain ⟨origin, _originOwner, otherEmitted⟩ :=
    (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
      carrierFuel ruleFuel other).mp otherPresent
  have originIdentity : origin = unit :=
    (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
      carrierFuel ruleFuel origin other otherEmitted).symm.trans otherUnit
  subst origin
  rw [emitted] at otherEmitted
  exact Option.some.inj otherEmitted.symm

/-- Every independently ready even physical unit has exactly one assignment in the whole-source
even-route result. -/
theorem existsUnique_mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃! assignment,
      assignment ∈ source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
          carrierFuel ruleFuel ∧
        assignment.unit = unit := by
  obtain ⟨assignment, emitted⟩ :=
    source.exists_aromaticCanonicalEvenOpenCumuleneAxialAssignment_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  have assignmentUnit :=
    source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
      carrierFuel ruleFuel unit assignment emitted
  have assignmentPresent : assignment ∈
      source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel :=
    (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
      carrierFuel ruleFuel assignment).mpr ⟨unit, evidence.owner, emitted⟩
  refine ⟨assignment, ⟨assignmentPresent, assignmentUnit⟩, ?_⟩
  intro other ⟨otherPresent, otherUnit⟩
  obtain ⟨origin, _originOwner, otherEmitted⟩ :=
    (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
      carrierFuel ruleFuel other).mp otherPresent
  have originIdentity : origin = unit :=
    (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
      carrierFuel ruleFuel origin other otherEmitted).symm.trans otherUnit
  subst origin
  rw [emitted] at otherEmitted
  exact Option.some.inj otherEmitted.symm

/-- The exact emitted odd assignment has literal list count one. -/
theorem exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      assignment.unit = unit ∧
        (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
          carrierFuel ruleFuel).count assignment = 1 := by
  obtain ⟨assignment, property, _unique⟩ :=
    source.existsUnique_mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  refine ⟨assignment, property.2, ?_⟩
  rw [(source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
    carrierFuel ruleFuel).count]
  simp [property.1]

/-- The exact emitted even assignment has literal list count one. -/
theorem exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      assignment.unit = unit ∧
        (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
          carrierFuel ruleFuel).count assignment = 1 := by
  obtain ⟨assignment, property, _unique⟩ :=
    source.existsUnique_mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  refine ⟨assignment, property.2, ?_⟩
  rw [(source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
    carrierFuel ruleFuel).count]
  simp [property.1]

/-! ## Exact-once transport into the complete represented source result -/

/-- Canonical injection of an odd-open-cumulene assignment into the five-branch source result. -/
def embedOddOpenCumuleneInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes :=
  .prior (.prior (.oddOpenCumulene assignment))

/-- Canonical injection of an even-open-cumulene assignment into the five-branch source result. -/
def embedEvenOpenCumuleneInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes :=
  .prior (.evenOpenCumulene assignment)

/-- Injection through the disjoint scheduler layers preserves the exact odd-family count. -/
theorem count_embedOddOpenCumuleneInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
      carrierFuel ruleFuel).count
        (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment) =
      (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
        carrierFuel ruleFuel).count assignment := by
  simp only [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
    List.map_append, List.map_map, List.count_append]
  have baseZero :
      List.count (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.prior)
          (source.analyzeAromaticCanonicalConcreteStereochemistry
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedOddOpenCumuleneInConcreteStereochemicalResult])
  have oddCount :
      List.count (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.oddOpenCumulene)
          (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
            carrierFuel ruleFuel)) =
        List.count assignment
          (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
            carrierFuel ruleFuel) := by
    exact List.count_map_of_injective _ _ (by
      intro left right equal
      cases equal
      rfl) assignment
  have evenZero :
      List.count (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.evenOpenCumulene)
          (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedOddOpenCumuleneInConcreteStereochemicalResult])
  have cyclicZero :
      List.count (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment)
        (List.map
          AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent
          source.aromaticCanonicalCyclicCumuleneComponents) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedOddOpenCumuleneInConcreteStereochemicalResult])
  rw [baseZero, oddCount, evenZero, cyclicZero]
  omega

/-- Injection through the disjoint scheduler layers preserves the exact even-family count. -/
theorem count_embedEvenOpenCumuleneInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
      carrierFuel ruleFuel).count
        (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment) =
      (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
        carrierFuel ruleFuel).count assignment := by
  simp only [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
    List.map_append, List.map_map, List.count_append]
  have priorZero :
      List.count (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior)
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedEvenOpenCumuleneInConcreteStereochemicalResult])
  have evenCount :
      List.count (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.evenOpenCumulene)
          (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
            carrierFuel ruleFuel)) =
        List.count assignment
          (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
            carrierFuel ruleFuel) := by
    exact List.count_map_of_injective _ _ (by
      intro left right equal
      cases equal
      rfl) assignment
  have cyclicZero :
      List.count (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment)
        (List.map
          AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent
          source.aromaticCanonicalCyclicCumuleneComponents) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedEvenOpenCumuleneInConcreteStereochemicalResult])
  rw [priorZero, evenCount, cyclicZero]
  omega

/-- Every independently ready odd unit occurs with literal count one in the five-branch source
result, not merely in the isolated family analyzer. -/
theorem exists_count_embeddedOddOpenCumulene_eq_one_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      assignment.unit = unit ∧
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
          carrierFuel ruleFuel).count
            (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment) = 1 := by
  obtain ⟨assignment, unitIdentity, countOne⟩ :=
    source.exists_count_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_one_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  exact ⟨assignment, unitIdentity, by
    rw [source.count_embedOddOpenCumuleneInConcreteStereochemicalResult]
    exact countOne⟩

/-- Every independently ready even unit occurs with literal count one in the five-branch source
result. -/
theorem exists_count_embeddedEvenOpenCumulene_eq_one_of_dependencies
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (terminals : source.AromaticCanonicalOpenCumuleneTerminals)
    (evidence : source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
      carrierFuel ruleFuel unit terminals) :
    ∃ assignment,
      assignment.unit = unit ∧
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
          carrierFuel ruleFuel).count
            (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment) = 1 := by
  obtain ⟨assignment, unitIdentity, countOne⟩ :=
    source.exists_count_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_one_of_dependencies
      carrierFuel ruleFuel unit terminals evidence
  exact ⟨assignment, unitIdentity, by
    rw [source.count_embedEvenOpenCumuleneInConcreteStereochemicalResult]
    exact countOne⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
