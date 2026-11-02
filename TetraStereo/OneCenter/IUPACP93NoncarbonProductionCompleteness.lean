import TetraStereo.OneCenter.IUPACRemaining71P93NoncarbonReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for all seven noncarbon P-93 provisions

The producer below factors each reviewed observation into an explicit source envelope and the
finite noncarbon configuration rule.  It does not invoke a reviewed `Judges` relation or an
authority-observation `ValidFor` predicate.  The oxide and oxo rows compute the representation
quotient with the independent functions in `P93NoncarbonTetrahedra`.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.NoncarbonTetrahedra

def P93NoncarbonFrameSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (frame : P93NoncarbonTetrahedralFrame) : Prop :=
  frame.StructurallyValidFor source ∧
    policy.TetrahedralArrangementObserved source frame.center frame.ligands

def P93NoncarbonAssignmentSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93NoncarbonTetrahedralAssignment policy) : Prop :=
  P93NoncarbonFrameSourceCore policy source assignment.frame ∧
    policy.DescriptorAuthorized source (.atomCenter assignment.frame.center)
      assignment.descriptor

def P93NoncarbonCitationBindingSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonCitationAuthorityObservation policy) : Prop :=
  match observation.citationRule.locant with
  | .none => observation.citation? = none
  | .numerical =>
      ∃ citation, observation.citation? = some citation ∧ citation.Valid ∧
        policy.CitationAuthorized source citation
          (.atomCenter observation.assignment.frame.center)
  | .letter => False

def P93NoncarbonCitationSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonCitationAuthorityObservation policy) : Prop :=
  P93NoncarbonAssignmentSourceCore policy source observation.assignment ∧
    (∃ atom, source.molecule.atoms[observation.assignment.frame.center]? = some atom ∧
      P93NoncarbonCentralElementFamilyMatches
        observation.citationRule.centralElement atom.element.atomicNumber) ∧
    P93NoncarbonCitationBindingSourceCore policy source observation ∧
    CitationConforms observation.citationRule

def P93NoncarbonOnicSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonOnicAuthorityObservation policy) : Prop :=
  P93NoncarbonAssignmentSourceCore policy source observation.assignment ∧
    P93NoncarbonElementAt source observation.assignment.frame.center
      (P93NoncarbonOnicAtomicNumber observation.family)

def P93NoncarbonOxideSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonOxideAuthorityObservation policy) : Prop :=
  P93NoncarbonAssignmentSourceCore policy source observation.assignment ∧
    P93NoncarbonElementAt source observation.assignment.frame.center
      (P93NoncarbonOxideAtomicNumber observation.family) ∧
    observation.oxygen ∈ observation.assignment.frame.ligands ∧
    P93NoncarbonElementAt source observation.oxygen 8 ∧
    P93AuthorityBinaryBond source observation.assignment.frame.center observation.oxygen ∧
    policy.OxideBondingVariantAuthorized source observation.assignment.frame.center
      observation.oxygen observation.family observation.firstBonding ∧
    policy.OxideBondingVariantAuthorized source observation.assignment.frame.center
      observation.oxygen observation.family observation.secondBonding ∧
    observation.firstBonding ≠ observation.secondBonding

def P93NoncarbonPhosphorusOxoSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy) : Prop :=
  P93NoncarbonAssignmentSourceCore policy source observation.assignment ∧
    P93NoncarbonElementAt source observation.assignment.frame.center 15 ∧
    observation.oxygen ∈ observation.assignment.frame.ligands ∧
    P93NoncarbonElementAt source observation.oxygen 8 ∧
    P93AuthorityBinaryBond source observation.assignment.frame.center observation.oxygen ∧
    policy.PhosphorusOxoVariantAuthorized source observation.assignment.frame.center
      observation.oxygen observation.family observation.firstWrittenAsDouble
        observation.firstCharges ∧
    policy.PhosphorusOxoVariantAuthorized source observation.assignment.frame.center
      observation.oxygen observation.family observation.secondWrittenAsDouble
        observation.secondCharges ∧
    (observation.firstWrittenAsDouble, observation.firstCharges) ≠
      (observation.secondWrittenAsDouble, observation.secondCharges)

def P93NoncarbonChalcogenOxoSourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonChalcogenOxoAuthorityObservation policy) : Prop :=
  P93NoncarbonAssignmentSourceCore policy source observation.assignment ∧
    (∃ atom : SemanticAtom,
      source.molecule.atoms[observation.assignment.frame.center]? = some atom ∧
      P93NoncarbonChalcogenOxoFamilyMatches observation.family atom.element.atomicNumber) ∧
    observation.oxygen ∈ observation.assignment.frame.ligands ∧
    P93NoncarbonElementAt source observation.oxygen 8 ∧
    P93AuthorityBinaryBond source observation.assignment.frame.center observation.oxygen ∧
    policy.ChalcogenOxoVariantAuthorized source observation.assignment.frame.center
      observation.oxygen observation.family observation.firstWrittenAsDouble
        observation.firstCharges ∧
    policy.ChalcogenOxoVariantAuthorized source observation.assignment.frame.center
      observation.oxygen observation.family observation.secondWrittenAsDouble
        observation.secondCharges ∧
    (observation.firstWrittenAsDouble, observation.firstCharges) ≠
      (observation.secondWrittenAsDouble, observation.secondCharges)

def P93NoncarbonGroup14SourceCore
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonGroup14AuthorityObservation policy) : Prop :=
  P93NoncarbonAssignmentSourceCore policy source observation.assignment ∧
    P93NoncarbonElementAt source observation.assignment.frame.center
      (P93NoncarbonGroup14AtomicNumber observation.family)

namespace Remaining71P93NoncarbonAuthorityRow

def ProductionJudges
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) :
    (row : Remaining71P93NoncarbonAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .otherElementTetrahedra, source, observation =>
      P93NoncarbonAssignmentSourceCore policy source observation
  | .otherElementGeneralMethodology, source, observation =>
      P93NoncarbonCitationSourceCore policy source observation
  | .azaniumPhosphanium, source, observation =>
      P93NoncarbonOnicSourceCore policy source observation
  | .aminePhosphaneOxides, source, observation =>
      P93NoncarbonOxideSourceCore policy source observation ∧
        oxideLigandCount observation.family observation.firstBonding =
          oxideLigandCount observation.family observation.secondBonding
  | .phosphatesPhosphonates, source, observation =>
      P93NoncarbonPhosphorusOxoSourceCore policy source observation ∧
        phosphorusOxoEffectiveBondOrder observation.family
            observation.firstWrittenAsDouble =
          phosphorusOxoEffectiveBondOrder observation.family
            observation.secondWrittenAsDouble ∧
        SameConfigurationIgnoringFormalCharges
          observation.firstCharges observation.secondCharges
  | .sulfatesSulfonates, source, observation =>
      P93NoncarbonChalcogenOxoSourceCore policy source observation ∧
        UsesPhosphateConfigurationTreatment observation.family ∧
        phosphorusOxoEffectiveBondOrder .related observation.firstWrittenAsDouble =
          phosphorusOxoEffectiveBondOrder .related observation.secondWrittenAsDouble ∧
        SameConfigurationIgnoringFormalCharges
          observation.firstCharges observation.secondCharges
  | .group14Noncarbon, source, observation =>
      P93NoncarbonGroup14SourceCore policy source observation ∧
        UsesCarbonTetrahedralMethod observation.family

theorem production_eq_reference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (row : Remaining71P93NoncarbonAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row <;>
    rfl

theorem reference_applicable_of_judged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (row : Remaining71P93NoncarbonAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row with
  | otherElementTetrahedra => exact ⟨observation, judged⟩
  | otherElementGeneralMethodology => exact ⟨observation.assignment, judged.1⟩
  | azaniumPhosphanium => exact ⟨observation, judged⟩
  | aminePhosphaneOxides | phosphatesPhosphonates |
      sulfatesSulfonates | group14Noncarbon => exact ⟨observation, judged.1⟩

end Remaining71P93NoncarbonAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93NoncarbonAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93NoncarbonAuthorityRow.reference_applicable_of_judged
