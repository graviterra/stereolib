import TetraStereo.OneCenter.CIPRepresentedConfigurationAndP94ReportPipeline
import TetraStereo.OneCenter.P93MolecularFullereneExteriorOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open AuthoritativeCIPMancudeTotality
open BlueBookP93.Cyclic
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94CarbohydrateFiveRingTwist
open BlueBookP94.P94MolecularHybridRingSelection
open BlueBookP94.P94MolecularCoordinateFrameLedger

/-!
# Fail-closed source agreement for the complete represented report

The complete report consumes a localized semantic source carrier and a normalized raw molecule.
Returning all non-lambda families while silently dropping lambda-spiro results on a source mismatch
would be a partial success. This module instead makes semantic source identity a global admission
condition and proves exact success and refusal.
-/

/-- The normalization result and localized source carrier denote exactly the same semantic
molecule. -/
def CertifiedAuthoritativeCompleteReportSourceAgreement
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult) : Prop :=
  certified.result.parsed.toSemanticMolecule? = some input.certified.input.molecule




def CertifiedAuthoritativeCompleteReportInputAgreement
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan) : Prop :=
  CertifiedAuthoritativeCompleteReportSourceAgreement input certified ∧
    input.certified.input.spatial? = some plan.spatial

/-- Canonical molecule-validated fullerene inputs used by the authoritative report. -/
noncomputable def authoritativeMolecularFullereneInputs
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (inputs : List ExteriorDerivedMolecularFullereneConfigurationInput) :
    List FullereneConfigurationInput :=
  validatedMolecularFullereneConfigurationInputs certified.result.parsed
    (validatedSymmetryDerivedMolecularFullereneConfigurationInputs
      certified.result.parsed
        (validatedExteriorDerivedMolecularFullereneConfigurationInputs
          certified.result.parsed spatial inputs))

/-- Fail-closed total entry point for the authoritative configuration/P-94 report. No branch is
returned unless the two certified source views agree globally. -/
noncomputable def analyzeCertifiedAuthoritativeConfigurationAndP94Report?
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    Option (List CertifiedRepresentedConfigurationAndP94Assignment) := by
  classical
  exact
    if CertifiedAuthoritativeCompleteReportInputAgreement input certified plan then
      some (analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
        observations derivedPlanes derivedHelices
          (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
          carbohydrateAuthority)
    else none

/-- Success returns exactly the complete report and proves global molecule/spatial input agreement. -/
theorem analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_some_iff
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (results : List CertifiedRepresentedConfigurationAndP94Assignment) :
    analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority = some results ↔
      CertifiedAuthoritativeCompleteReportInputAgreement input certified plan ∧
        results = analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified
          plan observations derivedPlanes derivedHelices
            (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
            carbohydrateAuthority := by
  by_cases agreement : CertifiedAuthoritativeCompleteReportInputAgreement input certified plan <;>
    simp [analyzeCertifiedAuthoritativeConfigurationAndP94Report?, agreement, eq_comm]

/-- Explicit strengthened contract: success is exactly molecule-plus-spatial input agreement and
the exact authoritative combined report. -/
theorem analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_some_iff_inputAgreement
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (results : List CertifiedRepresentedConfigurationAndP94Assignment) :
    analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority = some results ↔
      CertifiedAuthoritativeCompleteReportInputAgreement input certified plan ∧
        results = analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified
          plan observations derivedPlanes derivedHelices
            (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
            carbohydrateAuthority :=
  analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_some_iff premises input certified plan
    observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
      carbohydrateAuthority results

/-- Refusal is exactly molecule or spatial disagreement; no family-specific failure is hidden here. -/
theorem analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_none_iff
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority = none ↔
      ¬CertifiedAuthoritativeCompleteReportInputAgreement input certified plan := by
  by_cases agreement : CertifiedAuthoritativeCompleteReportInputAgreement input certified plan <;>
    simp [analyzeCertifiedAuthoritativeConfigurationAndP94Report?, agreement]

/-- Executable success is equivalent to the independent complete-input agreement proposition. -/
theorem analyzeCertifiedAuthoritativeConfigurationAndP94Report?_isSome_iff
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority).isSome = true ↔
      CertifiedAuthoritativeCompleteReportInputAgreement input certified plan := by
  by_cases agreement : CertifiedAuthoritativeCompleteReportInputAgreement input certified plan <;>
    simp [analyzeCertifiedAuthoritativeConfigurationAndP94Report?, agreement]

/-- Every successfully returned complete report remains globally duplicate-free. -/
theorem analyzeCertifiedAuthoritativeConfigurationAndP94Report?_some_nodup
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (results : List CertifiedRepresentedConfigurationAndP94Assignment)
    (computed : analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified
      plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
        carbohydrateAuthority = some results) :
    results.Nodup := by
  have exactResult :=
    (analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_some_iff premises input certified
      plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
        carbohydrateAuthority results).mp computed
  rw [exactResult.2]
  exact analyzeCertifiedRepresentedConfigurationAndP94Report_nodup premises input certified plan
    observations derivedPlanes derivedHelices
      (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
      carbohydrateAuthority

/-- A member of a successful report simultaneously carries global molecule/spatial identity, its exact
authoritative configuration or P-94 judgment, and expanded Rules-1a--6 comparison totality. -/
theorem
    analyzeCertifiedAuthoritativeConfigurationAndP94Report?_some_member_judged_and_expandedOccurrenceComparisonsTotal
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed)
    (state : OccurrenceAuxState)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (results : List CertifiedRepresentedConfigurationAndP94Assignment)
    (computed : analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified
      plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
        carbohydrateAuthority = some results)
    (output : CertifiedRepresentedConfigurationAndP94Assignment)
    (present : output ∈ results) :
    CertifiedAuthoritativeCompleteReportInputAgreement input certified plan ∧
      IndependentlyJudgedCertifiedRepresentedConfigurationAndP94Assignment premises input certified
          plan observations derivedPlanes derivedHelices
            (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
            carbohydrateAuthority output ∧
        AuthoritativeCIPOccurrenceCompleteness.ExpandedOccurrenceRule6ComparisonsTotal certified
          state := by
  have exactResult :=
    (analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_some_iff premises input certified
      plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
        carbohydrateAuthority results).mp computed
  have member : output ∈
      analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
        observations derivedPlanes derivedHelices
          (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
          carbohydrateAuthority := by
    rw [← exactResult.2]
    exact present
  have judgedAndTotal :=
    analyzeCertifiedRepresentedConfigurationAndP94Report_member_judged_and_expandedOccurrenceComparisonsTotal
      premises input certified kekule state plan observations derivedPlanes derivedHelices
        (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
          carbohydrateAuthority output member
  exact ⟨exactResult.1, judgedAndTotal⟩

/-- Intermediate exact fullerene semantics after the oriented-map symmetry boundary has admitted
the strict source records into the molecule-backed cage layer. -/
theorem
    fullerene_mem_analyzeCertifiedAuthoritativeConfigurationAndP94Report?_iff_molecularJudgment
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : FullereneConfigurationAssignment) :
    (∃ results,
      analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified plan
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
            carbohydrateAuthority = some results ∧
        (.configuration (.prior (.prior (.fullerene assignment))) :
          CertifiedRepresentedConfigurationAndP94Assignment) ∈ results) ↔
      CertifiedAuthoritativeCompleteReportInputAgreement input certified plan ∧
        MolecularFullereneConfigurationAssignmentJudgment
          certified.result.parsed
            (validatedSymmetryDerivedMolecularFullereneConfigurationInputs
              certified.result.parsed
                (validatedExteriorDerivedMolecularFullereneConfigurationInputs
                  certified.result.parsed plan.spatial fullerenes))
          assignment := by
  constructor
  · rintro ⟨results, computed, present⟩
    have exactResult :=
      (analyzeCertifiedAuthoritativeConfigurationAndP94Report?_eq_some_iff premises input certified
        plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority results).mp computed
    have lowerPresent :
        (.configuration (.prior (.prior (.fullerene assignment))) :
          CertifiedRepresentedConfigurationAndP94Assignment) ∈
          analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
            observations derivedPlanes derivedHelices
              (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
                carbohydrateAuthority := by
      rw [← exactResult.2]
      exact present
    have publicJudged :=
      (configuration_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff premises input
        certified plan observations derivedPlanes derivedHelices
          (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
            carbohydrateAuthority
            (.prior (.prior (.fullerene assignment)))).mp lowerPresent
    have conflictFree :
        ConflictFreeFullereneConfigurationAssignmentJudgment
          (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) assignment := by
      simpa [AuthoritativeRepresentedConfigurationFamilyPublicJudgment] using publicJudged
    have molecularJudged :
        MolecularFullereneConfigurationAssignmentJudgment
          certified.result.parsed
            (validatedSymmetryDerivedMolecularFullereneConfigurationInputs
              certified.result.parsed
                (validatedExteriorDerivedMolecularFullereneConfigurationInputs
                  certified.result.parsed plan.spatial fullerenes))
          assignment :=
      (molecularFullereneConfigurationAssignmentJudgment_iff_conflictFree
        certified.result.parsed
          (validatedSymmetryDerivedMolecularFullereneConfigurationInputs
            certified.result.parsed
              (validatedExteriorDerivedMolecularFullereneConfigurationInputs
                certified.result.parsed plan.spatial fullerenes))
        assignment).mpr
          (by simpa [authoritativeMolecularFullereneInputs] using conflictFree)
    exact ⟨exactResult.1, molecularJudged⟩
  · rintro ⟨agreement, molecularJudged⟩
    let results := analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified
      plan observations derivedPlanes derivedHelices
        (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
          carbohydrateAuthority
    refine ⟨results, ?_, ?_⟩
    · simp [analyzeCertifiedAuthoritativeConfigurationAndP94Report?, agreement, results]
    · apply (configuration_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff premises
        input certified plan observations derivedPlanes derivedHelices
          (authoritativeMolecularFullereneInputs certified plan.spatial fullerenes) rctPairs spiros external
            carbohydrateAuthority (.prior (.prior (.fullerene assignment)))).mpr
      have conflictFree :=
        (molecularFullereneConfigurationAssignmentJudgment_iff_conflictFree
          certified.result.parsed
            (validatedSymmetryDerivedMolecularFullereneConfigurationInputs
              certified.result.parsed
                (validatedExteriorDerivedMolecularFullereneConfigurationInputs
                  certified.result.parsed plan.spatial fullerenes))
          assignment).mp molecularJudged
      simpa [AuthoritativeRepresentedConfigurationFamilyPublicJudgment,
        authoritativeMolecularFullereneInputs] using conflictFree

/-- Exact end-to-end fullerene branch semantics.  A fullerene assignment occurs in a successful
authoritative report exactly when the global molecule/spatial sources agree and one supplied
strict record has a checked all-carbon cubic cage, coherent oriented face map, total substitution
evidence, an exactly symmetry-derived P-93.5.6 cage test, a locally justified descriptor payload,
and agreement with every other admitted record naming the same cage. -/
theorem
    fullerene_mem_analyzeCertifiedAuthoritativeConfigurationAndP94Report?_iff_symmetryDerivedJudgment
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : FullereneConfigurationAssignment) :
    (∃ results,
      analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified plan
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
            carbohydrateAuthority = some results ∧
        (.configuration (.prior (.prior (.fullerene assignment))) :
          CertifiedRepresentedConfigurationAndP94Assignment) ∈ results) ↔
      CertifiedAuthoritativeCompleteReportInputAgreement input certified plan ∧
        SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
          certified.result.parsed
            (validatedExteriorDerivedMolecularFullereneConfigurationInputs
              certified.result.parsed plan.spatial fullerenes)
          assignment := by
  rw [fullerene_mem_analyzeCertifiedAuthoritativeConfigurationAndP94Report?_iff_molecularJudgment]
  exact and_congr_right fun _agreement =>
    (symmetryDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_molecular
      certified.result.parsed
        (validatedExteriorDerivedMolecularFullereneConfigurationInputs
          certified.result.parsed plan.spatial fullerenes)
      assignment).symm

/-- Exact final fullerene branch semantics.  A nested fullerene assignment is emitted exactly when
the global molecular/spatial sources agree and one supplied source record survives the molecular
cage, oriented-symmetry, and exterior-oriented numbered-face judgments.  Exact supporting
coordinates remain a checked consistency specialization whenever they apply. -/
theorem
    fullerene_mem_analyzeCertifiedAuthoritativeConfigurationAndP94Report?_iff_exteriorDerivedJudgment
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List ExteriorDerivedMolecularFullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : FullereneConfigurationAssignment) :
    (∃ results,
      analyzeCertifiedAuthoritativeConfigurationAndP94Report? premises input certified plan
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
            carbohydrateAuthority = some results ∧
        (.configuration (.prior (.prior (.fullerene assignment))) :
          CertifiedRepresentedConfigurationAndP94Assignment) ∈ results) ↔
      CertifiedAuthoritativeCompleteReportInputAgreement input certified plan ∧
        ExteriorDerivedMolecularFullereneConfigurationAssignmentJudgment
          certified.result.parsed plan.spatial fullerenes assignment := by
  rw [fullerene_mem_analyzeCertifiedAuthoritativeConfigurationAndP94Report?_iff_symmetryDerivedJudgment]
  exact and_congr_right fun _agreement =>
    (exteriorDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_symmetry
      certified.result.parsed plan.spatial fullerenes assignment).symm

end

end TetraStereo.OneCenter
