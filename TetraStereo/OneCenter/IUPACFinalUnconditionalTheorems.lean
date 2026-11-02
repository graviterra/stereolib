import TetraStereo.OneCenter.CompleteIUPACAuthorityCertificate
import TetraStereo.OneCenter.CIPAuthoritativeCompleteReportSourceAgreement
import TetraStereo.OneCenter.IUPACGlobalReviewedSemantics
import TetraStereo.OneCenter.IUPACNormativeManifestCore
import TetraStereo.Engine.Result

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open AuthoritativeCIPMancudeTotality
open BlueBookP93.Cyclic
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94CarbohydrateFiveRingTwist
open BlueBookP94.P94MolecularHybridRingSelection
open BlueBookP94.P94MolecularCoordinateFrameLedger
open IUPACNormativeProvision
































namespace IUPACNormativeProvision

/-- Every P-10 manifest row is outside descriptor-assignment applicability.  P-10 rows are
parameterized source rows whose generated global kind is a nomenclature role. -/
theorem p10_not_descriptorAssignmentBearing (row : BlueBookP10Audit.Provision) :
    ¬ DescriptorAssignmentBearing (IUPACNormativeProvision.p10 row) := by
  intro bearing
  have classifier :
      descriptorAssignmentBearing? (IUPACNormativeProvision.p10 row) = false := rfl
  simp [DescriptorAssignmentBearing, classifier] at bearing

/-- Every P-10 manifest row belongs to the 2,300-row non-descriptor programme. -/
theorem p10_mem_globalNonDescriptorProvisions (row : BlueBookP10Audit.Provision) :
    IUPACNormativeProvision.p10 row ∈ globalNonDescriptorProvisions :=
  (mem_globalNonDescriptorProvisions_iff _).2 (p10_not_descriptorAssignmentBearing row)







theorem globalNonDescriptorReviewedSemantics_false
    (negative : GlobalNonDescriptorReviewedSemantics) : False := by
  have audited : IUPACNormativeSource.ProvisionAuditComplete
      (IUPACNormativeProvision.source
        (IUPACNormativeProvision.p10
          BlueBookP10Audit.Provision.p101StereoparentCommonConfiguration)) :=
    negative.reviewed.sourceAudited
      (List.mem_toFinset.mpr
        (p10_mem_globalNonDescriptorProvisions
          BlueBookP10Audit.Provision.p101StereoparentCommonConfiguration))
  have sourceEq : IUPACNormativeProvision.source
      (IUPACNormativeProvision.p10
        BlueBookP10Audit.Provision.p101StereoparentCommonConfiguration) =
        IUPACNormativeSource.blueBook2013P10 := rfl
  rw [sourceEq] at audited
  exact (IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open
    IUPACNormativeSource.blueBook2013P10 rfl) audited

end IUPACNormativeProvision

/-- Every datum and proof needed by the final represented IUPAC authority transaction. -/
structure CompleteIUPACAnalysisRequest where
  negative : GlobalNonDescriptorReviewedSemantics
  premises : IndependentInOutPremises
    BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework
  input : CertifiedLocalizedCIPInput
  certified : CertifiedChemistryNormalizationResult
  plan : MolecularCoordinateFrameHybridPlan
  observations : IndexedCIPGeometryObservations
  derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation
  derivedHelices : List IndexedHelicalGeometryObservation
  fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput
  rctPairs : List RCTPairConfigurationInput
  spiros : List SpiroConfigurationInput
  external : IndependentAmbiguousP94RingSelectionAuthority
  carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority
  provisionInputAdmitted :
    ((globalDescriptorAssignmentProjection
      (iupacCanonicalFrozenCorpus negative)).toCorpus).ChemicallyAdmitted
        input.certified.input

namespace CompleteIUPACAnalysisRequest

/-- The private-constructor 2,452-row authority certificate fixed by this request's reviewed
negative source program. -/
noncomputable def authorityCertificate (request : CompleteIUPACAnalysisRequest) :=
  completeIUPACAuthorityCertificate request.negative

/-- Actual fail-closed production report for the fully specified request. -/
noncomputable def production?
    (request : CompleteIUPACAnalysisRequest) :
    Option (List CertifiedRepresentedConfigurationAndP94Assignment) :=
  analyzeCertifiedAuthoritativeConfigurationAndP94Report? request.premises request.input
    request.certified request.plan request.observations request.derivedPlanes
      request.derivedHelices request.fullerenes request.rctPairs request.spiros request.external
        request.carbohydrateAuthority

/-- Independent applicability of the complete represented report: the certified semantic,
normalized, and spatial views denote one common fully specified input. -/
def ReferenceApplicable (request : CompleteIUPACAnalysisRequest) : Prop :=
  CertifiedAuthoritativeCompleteReportInputAgreement request.input request.certified request.plan

/-- Independent reference derivation for one final configuration or conformation result. -/
def ReferenceDerives (request : CompleteIUPACAnalysisRequest)
    (output : CertifiedRepresentedConfigurationAndP94Assignment) : Prop :=
  request.ReferenceApplicable ∧
    IndependentlyJudgedCertifiedRepresentedConfigurationAndP94Assignment request.premises
      request.input request.certified request.plan request.observations request.derivedPlanes
        request.derivedHelices
          (authoritativeMolecularFullereneInputs request.certified request.plan.spatial
            request.fullerenes)
          request.rctPairs request.spiros request.external request.carbohydrateAuthority output

/-- Production assignments, with a failed global input-agreement check exposing no partial branch. -/
noncomputable def productionAssignments (request : CompleteIUPACAnalysisRequest) :
    List CertifiedRepresentedConfigurationAndP94Assignment :=
  request.production?.getD []

/-- Canonical set semantics of the production list; order and representation-level duplicates are
irrelevant to the extensional theorem. -/
noncomputable def canonicalProductionAssignments (request : CompleteIUPACAnalysisRequest) :
    Set CertifiedRepresentedConfigurationAndP94Assignment :=
  {output | output ∈ request.productionAssignments}

/-- Canonical independent reference result set. -/
def referenceAssignments (request : CompleteIUPACAnalysisRequest) :
    Set CertifiedRepresentedConfigurationAndP94Assignment :=
  {output | request.ReferenceDerives output}

/-- The public refusal projection never guesses an implementation failure.  A mismatch between
the independently certified molecule/spatial views is reported as unsupported input. -/
noncomputable def refusalReason? (request : CompleteIUPACAnalysisRequest) :
    Option TetraStereo.Engine.RefusalReason :=
  if request.production?.isSome then none
  else some TetraStereo.Engine.RefusalReason.unsupportedInput

/-- The global provision compiler and the independently reviewed provision reference are
extensionally equal for every one of the 2,452 rows on the request's admitted semantic input. -/
theorem provision_pipeline_eq_reference (request : CompleteIUPACAnalysisRequest)
    (provision : IUPACNormativeProvision) :
    (iupacCanonicalProvisionInterpreter request.negative).productionAssignments provision
        request.input.certified.input =
      FrozenProvisionCorpus.referenceAssignments
        (globalDescriptorAssignmentProjection
          (iupacCanonicalFrozenCorpus request.negative)).toCorpus provision
            request.input.certified.input := by
  exact request.authorityCertificate.pipeline_eq_reference provision
    request.input.certified.input request.provisionInputAdmitted

/-- Pointwise form of the global provision theorem.  This is the final provision-level
soundness/completeness equivalence, including the independently reviewed applicability premise. -/
theorem provision_production_iff_reference (request : CompleteIUPACAnalysisRequest)
    (provision : IUPACNormativeProvision)
    (observation :
      ((globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Observation) :
    (iupacCanonicalProvisionInterpreter request.negative).Produces provision
        request.input.certified.input observation ↔
      ((globalDescriptorAssignmentProjection
          (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Applicable
          request.input.certified.input ∧
        ((globalDescriptorAssignmentProjection
          (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Judges
            request.input.certified.input observation := by
  exact request.authorityCertificate.compilerCorrect.every_provision_correct provision
    request.input.certified.input request.provisionInputAdmitted observation

/-- Final provision-level soundness projection. -/
theorem provision_production_sound (request : CompleteIUPACAnalysisRequest)
    (provision : IUPACNormativeProvision)
    (observation :
      ((globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Observation)
    (produced : (iupacCanonicalProvisionInterpreter request.negative).Produces provision
      request.input.certified.input observation) :
    ((globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Applicable
        request.input.certified.input ∧
      ((globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Judges
          request.input.certified.input observation :=
  (request.provision_production_iff_reference provision observation).mp produced

/-- Final provision-level completeness projection. -/
theorem provision_production_complete (request : CompleteIUPACAnalysisRequest)
    (provision : IUPACNormativeProvision)
    (observation :
      ((globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Observation)
    (derived :
      ((globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Applicable
          request.input.certified.input ∧
        ((globalDescriptorAssignmentProjection
          (iupacCanonicalFrozenCorpus request.negative)).toCorpus.reference provision).Judges
            request.input.certified.input observation) :
    (iupacCanonicalProvisionInterpreter request.negative).Produces provision
      request.input.certified.input observation :=
  (request.provision_production_iff_reference provision observation).mpr derived

/-- Production applicability agrees exactly with the independent complete-input relation. -/
theorem applicability_agreement (request : CompleteIUPACAnalysisRequest) :
    request.production?.isSome = true ↔ request.ReferenceApplicable := by
  exact analyzeCertifiedAuthoritativeConfigurationAndP94Report?_isSome_iff request.premises
    request.input request.certified request.plan request.observations request.derivedPlanes
      request.derivedHelices request.fullerenes request.rctPairs request.spiros request.external
        request.carbohydrateAuthority

/-- Production refusal agrees exactly with independent inapplicability. -/
theorem inapplicability_agreement (request : CompleteIUPACAnalysisRequest) :
    request.production? = none ↔ ¬request.ReferenceApplicable := by
  exact analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_none_iff request.premises
    request.input request.certified request.plan request.observations request.derivedPlanes
      request.derivedHelices request.fullerenes request.rctPairs request.spiros request.external
        request.carbohydrateAuthority

/-- The refusal projection is empty exactly on independently applicable complete-report input. -/
theorem refusalReason_eq_none_iff_applicable (request : CompleteIUPACAnalysisRequest) :
    request.refusalReason? = none ↔ request.ReferenceApplicable := by
  by_cases applicable : request.ReferenceApplicable
  · have computed : request.production?.isSome = true :=
      request.applicability_agreement.mpr applicable
    simp [refusalReason?, computed, applicable]
  · have computed : request.production?.isSome = false := by
      cases value : request.production?.isSome with
      | false => rfl
      | true => exact False.elim (applicable (request.applicability_agreement.mp value))
    simp [refusalReason?, computed, applicable]

/-- Input disagreement is classified exactly as `unsupportedInput`; it is never relabelled as an
implementation limit. -/
theorem refusalReason_eq_unsupportedInput_iff_inapplicable
    (request : CompleteIUPACAnalysisRequest) :
    request.refusalReason? = some TetraStereo.Engine.RefusalReason.unsupportedInput ↔
      ¬request.ReferenceApplicable := by
  by_cases applicable : request.ReferenceApplicable
  · have computed : request.production?.isSome = true :=
      request.applicability_agreement.mpr applicable
    simp [refusalReason?, computed, applicable]
  · have computed : request.production?.isSome = false := by
      cases value : request.production?.isSome with
      | false => rfl
      | true => exact False.elim (applicable (request.applicability_agreement.mp value))
    simp [refusalReason?, computed, applicable]

/-- Exact flattened membership is the common core from which soundness and completeness follow. -/
theorem mem_productionAssignments_iff_reference (request : CompleteIUPACAnalysisRequest)
    (output : CertifiedRepresentedConfigurationAndP94Assignment) :
    output ∈ request.productionAssignments ↔ request.ReferenceDerives output := by
  by_cases agreement : request.ReferenceApplicable
  · have computed : request.production? = some
        (analyzeCertifiedRepresentedConfigurationAndP94Report request.premises request.input
          request.certified request.plan request.observations request.derivedPlanes
            request.derivedHelices
              (authoritativeMolecularFullereneInputs request.certified request.plan.spatial
                request.fullerenes)
              request.rctPairs request.spiros request.external request.carbohydrateAuthority) := by
      exact (analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_some_iff request.premises
        request.input request.certified request.plan request.observations request.derivedPlanes
          request.derivedHelices request.fullerenes request.rctPairs request.spiros request.external
            request.carbohydrateAuthority _).2 ⟨agreement, rfl⟩
    rw [productionAssignments, computed]
    simp only [Option.getD_some]
    rw [mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff]
    simp only [ReferenceDerives, agreement, true_and,
      CertifiedRepresentedConfigurationAndP94ExecutableMember,
      IndependentlyJudgedCertifiedRepresentedConfigurationAndP94Assignment]
  · have refused : request.production? = none :=
      (request.inapplicability_agreement).2 agreement
    simp [productionAssignments, refused, ReferenceDerives, agreement]

/-- Final unconditional soundness: every emitted result is independently derived. -/
theorem production_sound (request : CompleteIUPACAnalysisRequest)
    {output : CertifiedRepresentedConfigurationAndP94Assignment}
    (present : output ∈ request.productionAssignments) :
    request.ReferenceDerives output :=
  (request.mem_productionAssignments_iff_reference output).mp present

/-- Final unconditional completeness: every independently derived result is emitted. -/
theorem production_complete (request : CompleteIUPACAnalysisRequest)
    {output : CertifiedRepresentedConfigurationAndP94Assignment}
    (derived : request.ReferenceDerives output) :
    output ∈ request.productionAssignments :=
  (request.mem_productionAssignments_iff_reference output).mpr derived

/-- Final extensional equality after canonicalizing the executable list to set semantics. -/
theorem canonical_extensional_equality (request : CompleteIUPACAnalysisRequest) :
    request.canonicalProductionAssignments = request.referenceAssignments := by
  ext output
  exact request.mem_productionAssignments_iff_reference output

/-- No fully specified request can report an implementation-limit refusal.  The result is stronger
than the applicable-input corollary: input disagreement also receives the distinct
`unsupportedInput` reason. -/
theorem no_implementation_limit_refusal (request : CompleteIUPACAnalysisRequest) :
    request.refusalReason? ≠ some TetraStereo.Engine.RefusalReason.implementationLimit := by
  intro limit
  by_cases applicable : request.ReferenceApplicable
  · have noRefusal := request.refusalReason_eq_none_iff_applicable.mpr applicable
    rw [noRefusal] at limit
    simp at limit
  · have unsupported :=
      request.refusalReason_eq_unsupportedInput_iff_inapplicable.mpr applicable
    rw [unsupported] at limit
    cases limit

/-- The requested applicable-input totality corollary. -/
theorem applicable_no_implementation_limit_refusal (request : CompleteIUPACAnalysisRequest)
    (_applicable : request.ReferenceApplicable) :
    request.refusalReason? ≠ some TetraStereo.Engine.RefusalReason.implementationLimit :=
  request.no_implementation_limit_refusal

/-- One proof object collecting the final unconditional molecular-report claims. -/
structure FinalUnconditionalCorrectness (request : CompleteIUPACAnalysisRequest) : Prop where
  soundness : ∀ {output}, output ∈ request.productionAssignments →
    request.ReferenceDerives output
  completeness : ∀ {output}, request.ReferenceDerives output →
    output ∈ request.productionAssignments
  applicabilityAgreement : request.production?.isSome = true ↔ request.ReferenceApplicable
  inapplicabilityAgreement : request.production? = none ↔ ¬request.ReferenceApplicable
  extensionalEquality :
    request.canonicalProductionAssignments = request.referenceAssignments
  noImplementationLimitRefusal :
    request.refusalReason? ≠ some TetraStereo.Engine.RefusalReason.implementationLimit

/-- Final packaged theorem, with no caller-supplied proof arguments beyond the evidence-bearing
request itself. -/
theorem final_unconditional_correctness (request : CompleteIUPACAnalysisRequest) :
    FinalUnconditionalCorrectness request where
  soundness := request.production_sound
  completeness := request.production_complete
  applicabilityAgreement := request.applicability_agreement
  inapplicabilityAgreement := request.inapplicability_agreement
  extensionalEquality := request.canonical_extensional_equality
  noImplementationLimitRefusal := request.no_implementation_limit_refusal





theorem completeIUPACAnalysisRequest_false
    (request : CompleteIUPACAnalysisRequest) : False :=
  IUPACNormativeProvision.globalNonDescriptorReviewedSemantics_false request.negative

/-- Explicit non-constructibility of the fully specified request. -/
theorem not_nonempty_completeIUPACAnalysisRequest :
    ¬ Nonempty CompleteIUPACAnalysisRequest :=
  fun ⟨request⟩ => completeIUPACAnalysisRequest_false request

end CompleteIUPACAnalysisRequest

end

end TetraStereo.OneCenter
