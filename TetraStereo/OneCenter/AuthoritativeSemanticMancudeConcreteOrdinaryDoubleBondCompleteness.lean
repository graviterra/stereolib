import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedCyclicCumuleneAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Concrete ordinary-double-bond completeness in the unified source scheduler

The generic ordinary-double-bond analyzer already proves finite-fuel completeness from chemical
dependency evidence.  This module specializes that result to the unique source-canonical
Rules-3--5 auxiliary fixed point and carries it through the disjoint unified scheduler.  Thus the
same dependency state used for tetrahedral descriptors is sufficient to produce exactly one
independently justified ordinary-double-bond assignment for every ready canonical bond.
-/

/-- Chemical readiness of one canonical individual double bond under the unique concrete
source-canonical dependency state. -/
abbrev AromaticCanonicalConcreteOrdinaryDoubleBondReady
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) : Prop :=
  source.AromaticCanonicalOrdinaryDoubleBondAutomaticDependencyEvidence
    carrierFuel bond
    (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.left)
    (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel bond.right)

/-- A chemically ready canonical bond produces a concrete assignment, and that same assignment
satisfies the independent endpoint Rules-1a--5, Rule-5 parity, rational geometry, and final
descriptor judgment. -/
theorem exists_aromaticCanonicalConcreteOrdinaryDoubleBondAssignment_and_judgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (ready : source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
      carrierFuel ruleFuel bond) :
    ∃ assignment,
      source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
          carrierFuel bond
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.right) = some assignment ∧
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment
          carrierFuel bond
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.left)
          (source.aromaticCanonicalConcreteDependencyViewAt
            carrierFuel ruleFuel bond.right) assignment := by
  obtain ⟨assignment, emitted⟩ :=
    source.exists_aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment_of_dependencies
      carrierFuel bond
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel bond.left)
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel bond.right) ready
  exact ⟨assignment, emitted,
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_sound
      carrierFuel bond
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel bond.left)
      (source.aromaticCanonicalConcreteDependencyViewAt
        carrierFuel ruleFuel bond.right) assignment emitted⟩

/-- A ready canonical physical bond occurs exactly once in the parameter-free concrete
ordinary-double-bond result. -/
theorem existsUnique_mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_of_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (ready : source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
      carrierFuel ruleFuel bond) :
    ∃! assignment,
      assignment ∈
          source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
            carrierFuel ruleFuel ∧
        assignment.bond = bond := by
  exact
    source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_of_dependencies
      carrierFuel
      (source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel)
      bond ready

/-- Exact identification of the ordinary-double-bond outputs belonging to one physical bond
inside the disjoint unified source result. -/
def AromaticCanonicalConcreteOrdinaryDoubleBondOccurrence
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (output : source.AromaticCanonicalConcreteStereochemicalAssignment) : Prop :=
  ∃ assignment,
    output = .ordinaryDoubleBond assignment ∧ assignment.bond = bond

/-- A ready canonical physical bond occurs exactly once even after its family result is embedded
in the unified tetrahedral-plus-ordinary-double-bond scheduler. -/
theorem existsUnique_mem_analyzeAromaticCanonicalConcreteStereochemistry_ordinaryDoubleBond_of_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (ready : source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
      carrierFuel ruleFuel bond) :
    ∃! output,
      output ∈ source.analyzeAromaticCanonicalConcreteStereochemistry
          carrierFuel ruleFuel ∧
        source.AromaticCanonicalConcreteOrdinaryDoubleBondOccurrence bond output := by
  obtain ⟨assignment, assignmentProperty, assignmentUnique⟩ :=
    source.existsUnique_mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_of_ready
      carrierFuel ruleFuel bond ready
  refine ⟨.ordinaryDoubleBond assignment, ?_, ?_⟩
  · refine ⟨?_, ⟨assignment, rfl, assignmentProperty.2⟩⟩
    simp [analyzeAromaticCanonicalConcreteStereochemistry, assignmentProperty.1]
  · intro other otherProperty
    rcases otherProperty.2 with ⟨otherAssignment, rfl, otherBond⟩
    apply congrArg AromaticCanonicalConcreteStereochemicalAssignment.ordinaryDoubleBond
    apply assignmentUnique
    refine ⟨?_, otherBond⟩
    simpa [analyzeAromaticCanonicalConcreteStereochemistry] using otherProperty.1

/-- Molecule-wide completeness for the concrete family analyzer: if each canonical individual
double bond is chemically ready, every one occurs exactly once. -/
theorem every_ready_aromaticCanonicalConcreteOrdinaryDoubleBond_occurs_exactly_once
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (ready : ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
        carrierFuel ruleFuel bond) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      ∃! assignment,
        assignment ∈
            source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
              carrierFuel ruleFuel ∧
          assignment.bond = bond := by
  intro bond owner
  exact
    source.existsUnique_mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_of_ready
      carrierFuel ruleFuel bond (ready bond owner)

/-- Molecule-wide completeness survives embedding in the unified source scheduler. -/
theorem every_ready_aromaticCanonicalConcreteOrdinaryDoubleBond_occurs_exactly_once_in_unified
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (ready : ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
        carrierFuel ruleFuel bond) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      ∃! output,
        output ∈ source.analyzeAromaticCanonicalConcreteStereochemistry
            carrierFuel ruleFuel ∧
          source.AromaticCanonicalConcreteOrdinaryDoubleBondOccurrence bond output := by
  intro bond owner
  exact
    source.existsUnique_mem_analyzeAromaticCanonicalConcreteStereochemistry_ordinaryDoubleBond_of_ready
      carrierFuel ruleFuel bond (ready bond owner)

/-! ## Literal exact-once transport into the five-branch source result -/

/-- A ready physical bond has a concrete family assignment with literal list count one. -/
theorem exists_count_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_eq_one_of_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (ready : source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
      carrierFuel ruleFuel bond) :
    ∃ assignment,
      assignment.bond = bond ∧
        (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
          carrierFuel ruleFuel).count assignment = 1 := by
  obtain ⟨assignment, property, _unique⟩ :=
    source.existsUnique_mem_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_of_ready
      carrierFuel ruleFuel bond ready
  refine ⟨assignment, property.2, ?_⟩
  rw [(source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_nodup
    carrierFuel ruleFuel).count]
  simp [property.1]

/-- Canonical injection of an ordinary-double-bond assignment through every later scheduler
extension. -/
def embedOrdinaryDoubleBondInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes :=
  .prior (.prior (.prior (.ordinaryDoubleBond assignment)))

/-- Injection through all disjoint scheduler layers preserves the exact ordinary-double-bond
family count. -/
theorem count_embedOrdinaryDoubleBondInConcreteStereochemicalResult
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
      carrierFuel ruleFuel).count
        (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment) =
      (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
        carrierFuel ruleFuel).count assignment := by
  simp only [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
    analyzeAromaticCanonicalConcreteStereochemistry,
    List.map_append, List.map_map, List.count_append]
  have tetrahedralZero :
      List.count (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.prior ∘
                AromaticCanonicalConcreteStereochemicalAssignment.tetrahedral)
          (source.analyzeAromaticCanonicalConcreteRule3Through6
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedOrdinaryDoubleBondInConcreteStereochemicalResult])
  have ordinaryDoubleBondCount :
      List.count (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.prior ∘
                AromaticCanonicalConcreteStereochemicalAssignment.ordinaryDoubleBond)
          (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
            carrierFuel ruleFuel)) =
        List.count assignment
          (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
            carrierFuel ruleFuel) := by
    exact List.count_map_of_injective _ _ (by
      intro left right equal
      cases equal
      rfl) assignment
  have oddOpenCumuleneZero :
      List.count (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.prior ∘
              AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.oddOpenCumulene)
          (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedOrdinaryDoubleBondInConcreteStereochemicalResult])
  have evenOpenCumuleneZero :
      List.count (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment)
        (List.map
          (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior ∘
            AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.evenOpenCumulene)
          (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
            carrierFuel ruleFuel)) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedOrdinaryDoubleBondInConcreteStereochemicalResult])
  have cyclicZero :
      List.count (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment)
        (List.map
          AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent
          source.aromaticCanonicalCyclicCumuleneComponents) = 0 :=
    List.count_eq_zero.mpr (by
      simp [embedOrdinaryDoubleBondInConcreteStereochemicalResult])
  rw [tetrahedralZero, ordinaryDoubleBondCount, oddOpenCumuleneZero,
    evenOpenCumuleneZero, cyclicZero]
  omega

/-- Every ready ordinary double bond occurs with literal count one in the actual five-branch
public source result. -/
theorem exists_count_embeddedOrdinaryDoubleBond_eq_one_of_ready
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (ready : source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
      carrierFuel ruleFuel bond) :
    ∃ assignment,
      assignment.bond = bond ∧
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
          carrierFuel ruleFuel).count
            (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment) = 1 := by
  obtain ⟨assignment, bondIdentity, countOne⟩ :=
    source.exists_count_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_eq_one_of_ready
      carrierFuel ruleFuel bond ready
  exact ⟨assignment, bondIdentity, by
    rw [source.count_embedOrdinaryDoubleBondInConcreteStereochemicalResult]
    exact countOne⟩

/-- Molecule-wide exact-once completeness for every ready ordinary double bond in the final
five-branch public result. -/
theorem every_ready_aromaticCanonicalConcreteOrdinaryDoubleBond_count_one_in_complete_result
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (ready : ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
        carrierFuel ruleFuel bond) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      ∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
            carrierFuel ruleFuel).count
              (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment) = 1 := by
  intro bond owner
  exact source.exists_count_embeddedOrdinaryDoubleBond_eq_one_of_ready
    carrierFuel ruleFuel bond (ready bond owner)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
