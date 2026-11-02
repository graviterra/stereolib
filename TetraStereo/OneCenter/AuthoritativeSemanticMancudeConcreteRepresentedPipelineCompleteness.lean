import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteTetrahedralExactOnceCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteOrdinaryDoubleBondCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneExactOnceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Conditional completeness of the complete represented source pipeline

This module assembles the family-local readiness theorems into one molecule-level contract at the
uniform finite Rules-3--6 bound. It covers every family represented by the current public result:
tetrahedral centers, ordinary double bonds, odd and even open cumulenes, and fully cyclic
cumulene parent-topology records.
-/

/-- Independent molecule-level readiness assumptions for every descriptor-bearing family in the
current public source result. Fully cyclic components need no extra readiness assumption because
their P-31 authority record is determined by source topology alone. -/
structure AromaticCanonicalRepresentedPipelineReadyAtBound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) : Prop where
  tetrahedral : ∀ center,
    source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound carrierFuel center
  ordinaryDoubleBond :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
        carrierFuel (2 * (carrierFuel + 1)) bond
  oddOpenCumulene :
    ∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
      ∃ terminals,
        source.AromaticCanonicalOddOpenCumuleneAutomaticDependencyEvidence
          carrierFuel (2 * (carrierFuel + 1)) unit terminals
  evenOpenCumulene :
    ∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
      ∃ terminals,
        source.AromaticCanonicalEvenOpenCumuleneAutomaticDependencyEvidence
          carrierFuel (2 * (carrierFuel + 1)) unit terminals

/-- Soundness plus literal exact-once coverage of every physical unit represented by the current
five-branch source result. -/
structure AromaticCanonicalRepresentedPipelineCompleteAtBound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) : Prop where
  emittedSound : ∀ result,
    result ∈ source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel (2 * (carrierFuel + 1)) →
      source.DeclarativeAromaticCanonicalConcreteStereochemicalWithCyclicCumulenesMember
        carrierFuel (2 * (carrierFuel + 1)) result
  tetrahedralExact : ∀ center,
    ∃ assignment,
      assignment.center = center ∧
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
          carrierFuel (2 * (carrierFuel + 1))).count
            (source.embedTetrahedralInConcreteStereochemicalResult assignment) = 1
  ordinaryDoubleBondExact :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      ∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
            carrierFuel (2 * (carrierFuel + 1))).count
              (source.embedOrdinaryDoubleBondInConcreteStereochemicalResult assignment) = 1
  oddOpenCumuleneExact :
    ∀ unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits,
      ∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
            carrierFuel (2 * (carrierFuel + 1))).count
              (source.embedOddOpenCumuleneInConcreteStereochemicalResult assignment) = 1
  evenOpenCumuleneExact :
    ∀ unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits,
      ∃ assignment,
        assignment.unit = unit ∧
          (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
            carrierFuel (2 * (carrierFuel + 1))).count
              (source.embedEvenOpenCumuleneInConcreteStereochemicalResult assignment) = 1
  fullyCyclicCumuleneExact :
    ∀ component ∈ source.aromaticCanonicalCyclicCumuleneComponents,
      (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel (2 * (carrierFuel + 1))).count
          (.fullyCyclicCumuleneParent component) = 1

private theorem filterMap_length_eq_of_total
    {α β : Type*} (values : List α) (f : α → Option β)
    (total : ∀ value ∈ values, ∃ result, f value = some result) :
    (values.filterMap f).length = values.length := by
  induction values with
  | nil => simp
  | cons head tail inductionHypothesis =>
      obtain ⟨result, computed⟩ := total head (by simp)
      have tailTotal : ∀ value ∈ tail, ∃ result, f value = some result := by
        intro value present
        exact total value (by simp [present])
      simp [computed, inductionHypothesis tailTotal]

/-- Under molecule-level readiness, no canonical tetrahedral center is dropped by `filterMap`. -/
theorem length_analyzeAromaticCanonicalConcreteRule3Through6_eq_centers_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    (source.analyzeAromaticCanonicalConcreteRule3Through6
      carrierFuel (2 * (carrierFuel + 1))).length =
        source.aromaticCanonicalTetrahedralCenters.length := by
  unfold analyzeAromaticCanonicalConcreteRule3Through6
    analyzeAromaticCanonicalScheduledRule3Through6
  apply filterMap_length_eq_of_total
  intro center _owner
  obtain ⟨descriptor, computed⟩ :=
    source.exists_aromaticCanonicalConcreteRule3Through6Descriptor?_at_bound
      carrierFuel center (ready.tetrahedral center)
  refine ⟨{ center, descriptor }, ?_⟩
  have scheduled :
      source.aromaticCanonicalScheduledRule3Through6Descriptor?
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel (2 * (carrierFuel + 1)))
        (2 * (carrierFuel + 1)) center = some descriptor :=
    computed
  simp [scheduled]

/-- Under molecule-level readiness, no canonical individual ordinary double bond is dropped. -/
theorem length_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_eq_carriers_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
      carrierFuel (2 * (carrierFuel + 1))).length =
        source.aromaticCanonicalIndividualDoubleBondCarriers.length := by
  unfold analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
    analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
  apply filterMap_length_eq_of_total
  intro bond owner
  exact source.exists_aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment_of_dependencies
    carrierFuel bond
    (source.aromaticCanonicalConcreteDependencyViewAt
      carrierFuel (2 * (carrierFuel + 1)) bond.left)
    (source.aromaticCanonicalConcreteDependencyViewAt
      carrierFuel (2 * (carrierFuel + 1)) bond.right)
    (ready.ordinaryDoubleBond bond owner)

/-- Under molecule-level readiness, no canonical odd-open-cumulene unit is dropped. -/
theorem length_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_units_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
      carrierFuel (2 * (carrierFuel + 1))).length =
        source.aromaticCanonicalOddOpenCumuleneUnits.length := by
  unfold analyzeAromaticCanonicalOddOpenCumuleneSpatial
  apply filterMap_length_eq_of_total
  intro unit owner
  obtain ⟨terminals, evidence⟩ := ready.oddOpenCumulene unit owner
  exact source.exists_aromaticCanonicalOddOpenCumuleneSpatialAssignment_of_dependencies
    carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence

/-- Under molecule-level readiness, no canonical even-open-cumulene unit is dropped. -/
theorem length_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_units_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
      carrierFuel (2 * (carrierFuel + 1))).length =
        source.aromaticCanonicalEvenOpenCumuleneUnits.length := by
  unfold analyzeAromaticCanonicalEvenOpenCumuleneAxial
  apply filterMap_length_eq_of_total
  intro unit owner
  obtain ⟨terminals, evidence⟩ := ready.evenOpenCumulene unit owner
  exact source.exists_aromaticCanonicalEvenOpenCumuleneAxialAssignment_of_dependencies
    carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence

/-- The public five-branch result is duplicate-free for arbitrary inputs and fuel. This is a
report-assembly theorem: constructor disjointness prevents cross-family collisions, while each
family retains its canonical physical identity. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
      carrierFuel ruleFuel).Nodup := by
  have tetrahedralNodup :
      ((source.analyzeAromaticCanonicalConcreteRule3Through6 carrierFuel ruleFuel).map
        AromaticCanonicalConcreteStereochemicalAssignment.tetrahedral).Nodup :=
    (source.analyzeAromaticCanonicalConcreteRule3Through6_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl)
  have ordinaryDoubleBondNodup :
      ((source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial
          carrierFuel ruleFuel).map
        AromaticCanonicalConcreteStereochemicalAssignment.ordinaryDoubleBond).Nodup :=
    (source.analyzeAromaticCanonicalConcreteOrdinaryDoubleBondAutomaticSpatial_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl)
  have baseNodup :
      (source.analyzeAromaticCanonicalConcreteStereochemistry
        carrierFuel ruleFuel).Nodup := by
    rw [analyzeAromaticCanonicalConcreteStereochemistry]
    exact tetrahedralNodup.append ordinaryDoubleBondNodup (by
      rw [List.disjoint_left]
      intro output tetrahedralPresent ordinaryDoubleBondPresent
      obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp tetrahedralPresent
      simp at ordinaryDoubleBondPresent)
  have oddNodup :
      ((source.analyzeAromaticCanonicalOddOpenCumuleneSpatial carrierFuel ruleFuel).map
        AromaticCanonicalConcreteStereochemicalAssignmentWithOddCumulene.oddOpenCumulene).Nodup :=
    (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl)
  have throughOddNodup :
      (source.analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene
        carrierFuel ruleFuel).Nodup := by
    rw [analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene]
    exact (baseNodup.map (by
      intro left right equal
      cases equal
      rfl)).append oddNodup (by
        rw [List.disjoint_left]
        intro output priorPresent oddPresent
        obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp priorPresent
        simp at oddPresent)
  have evenNodup :
      ((source.analyzeAromaticCanonicalEvenOpenCumuleneAxial carrierFuel ruleFuel).map
        AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes.evenOpenCumulene).Nodup :=
    (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
      carrierFuel ruleFuel).map (by
        intro left right equal
        cases equal
        rfl)
  have throughEvenNodup :
      (source.analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes
        carrierFuel ruleFuel).Nodup := by
    rw [analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes]
    exact (throughOddNodup.map (by
      intro left right equal
      cases equal
      rfl)).append evenNodup (by
        rw [List.disjoint_left]
        intro output priorPresent evenPresent
        obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp priorPresent
        simp at evenPresent)
  have cyclicNodup :
      (source.aromaticCanonicalCyclicCumuleneComponents.map
        AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.fullyCyclicCumuleneParent).Nodup :=
    source.aromaticCanonicalCyclicCumuleneComponents_nodup.map (by
      intro left right equal
      cases equal
      rfl)
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes]
  exact (throughEvenNodup.map (by
    intro left right equal
    cases equal
    rfl)).append cyclicNodup (by
      rw [List.disjoint_left]
      intro output priorPresent cyclicPresent
      obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp priorPresent
      simp at cyclicPresent)

/-- Under the molecule-level readiness contract, the public result length is exactly the sum of
the five canonical physical-unit enumerations. This rules out both silent omission and duplicate
reporting at the complete represented-pipeline boundary. -/
theorem length_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_eq_units_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
      carrierFuel (2 * (carrierFuel + 1))).length =
        source.aromaticCanonicalTetrahedralCenters.length +
          source.aromaticCanonicalIndividualDoubleBondCarriers.length +
          source.aromaticCanonicalOddOpenCumuleneUnits.length +
          source.aromaticCanonicalEvenOpenCumuleneUnits.length +
          source.aromaticCanonicalCyclicCumuleneComponents.length := by
  simp [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes,
    analyzeAromaticCanonicalConcreteStereochemistryWithOddCumulene,
    analyzeAromaticCanonicalConcreteStereochemistry,
    source.length_analyzeAromaticCanonicalConcreteRule3Through6_eq_centers_at_bound
      carrierFuel ready,
    source.length_analyzeAromaticCanonicalConcreteOrdinaryDoubleBond_eq_carriers_at_bound
      carrierFuel ready,
    source.length_analyzeAromaticCanonicalOddOpenCumuleneSpatial_eq_units_at_bound
      carrierFuel ready,
    source.length_analyzeAromaticCanonicalEvenOpenCumuleneAxial_eq_units_at_bound
      carrierFuel ready]
  omega

/-- Every represented physical unit occurs exactly once in the single public result, and every
result in that list satisfies the corresponding independent declarative judgment, provided the
four descriptor-bearing families satisfy their explicit molecule-level readiness obligations. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_complete_at_bound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    source.AromaticCanonicalRepresentedPipelineCompleteAtBound carrierFuel := by
  constructor
  · intro result present
    exact
      source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_member_sound
        carrierFuel (2 * (carrierFuel + 1)) result present
  · intro center
    exact source.exists_count_embeddedTetrahedral_eq_one_at_bound
      carrierFuel center (ready.tetrahedral center)
  · intro bond owner
    exact source.exists_count_embeddedOrdinaryDoubleBond_eq_one_of_ready
      carrierFuel (2 * (carrierFuel + 1)) bond
      (ready.ordinaryDoubleBond bond owner)
  · intro unit owner
    obtain ⟨terminals, evidence⟩ := ready.oddOpenCumulene unit owner
    exact source.exists_count_embeddedOddOpenCumulene_eq_one_of_dependencies
      carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence
  · intro unit owner
    obtain ⟨terminals, evidence⟩ := ready.evenOpenCumulene unit owner
    exact source.exists_count_embeddedEvenOpenCumulene_eq_one_of_dependencies
      carrierFuel (2 * (carrierFuel + 1)) unit terminals evidence
  · intro component owner
    exact
      source.count_fullyCyclicCumuleneParent_in_analyzeAromaticCanonicalConcreteStereochemistry_eq_one
        carrierFuel (2 * (carrierFuel + 1)) component
        ((source.mem_aromaticCanonicalCyclicCumuleneComponents_iff component).mp owner)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
