import TetraStereo.UniversalProof.ComputedOpenCumulenePipelineProofs.ComputedOpenCumuleneReadiness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteRepresentedPipelineCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeChemicalInput

/-- Construct the existing represented-pipeline readiness without independent cumulene terminal
witnesses. Tetrahedral, individual-double-bond and cumulene endpoint/geometry readiness stay explicit.
This is the current represented-family domain, not all chemically admitted systems. -/
noncomputable def representedPipelineReadiness_of_computedCumulenes
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (tetrahedral : ∀ center,
      source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound carrierFuel center)
    (ordinary : ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
        carrierFuel (2 * (carrierFuel + 1)) bond)
    (cumulenes : source.AromaticCanonicalOpenCumuleneComputedReadiness
      carrierFuel (2 * (carrierFuel + 1))) :
    source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel where
  tetrahedral := tetrahedral
  ordinaryDoubleBond := ordinary
  oddOpenCumulene :=
    (source.exists_terminalEvidence_of_computedReadiness
      carrierFuel (2 * (carrierFuel + 1)) cumulenes).1
  evenOpenCumulene :=
    (source.exists_terminalEvidence_of_computedReadiness
      carrierFuel (2 * (carrierFuel + 1)) cumulenes).2

/-- Feed computed cumulene terminals through the actual five-family represented analyzer's
soundness and exact-once theorem. This preserves all remaining chemical and geometry hypotheses. -/
theorem representedPipelineComplete_of_computedCumulenes
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (tetrahedral : ∀ center,
      source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound carrierFuel center)
    (ordinary : ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      source.AromaticCanonicalConcreteOrdinaryDoubleBondReady
        carrierFuel (2 * (carrierFuel + 1)) bond)
    (cumulenes : source.AromaticCanonicalOpenCumuleneComputedReadiness
      carrierFuel (2 * (carrierFuel + 1))) :
    source.AromaticCanonicalRepresentedPipelineCompleteAtBound carrierFuel :=
  source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_complete_at_bound
    carrierFuel (source.representedPipelineReadiness_of_computedCumulenes
      carrierFuel tetrahedral ordinary cumulenes)

end TetraStereo.OneCenter.AuthoritativeChemicalInput
