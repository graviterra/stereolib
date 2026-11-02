import TetraStereo.OneCenter.CIPAuthoritativeRepresentedConfigurationFamilyPipeline
import TetraStereo.OneCenter.P94MolecularCoordinateFrameCompleteTransaction

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open AuthoritativeCIPMancudeTotality
open BlueBookP93.Cyclic
open BlueBookP94.CoordinateTwistInOut
open BlueBookP94.P94CarbohydrateFiveRingTwist
open BlueBookP94.P94MolecularHybridRingSelection
open BlueBookP94.P94MolecularCoordinateFrameLedger
open BlueBookP94.P94MolecularCoordinateFrameCompleteTransaction











/-- One final represented result is either an absolute/relative configuration result from the
complete represented configuration endpoint, or a P-94 conformational assignment from the audited
coordinate-frame transaction. -/
inductive CertifiedRepresentedConfigurationAndP94Assignment where
  | configuration (assignment : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment)
  | conformation (assignment : P94ConformationAssignment)
  deriving DecidableEq, Repr

/-- Exact executable meaning of either branch of the combined report. -/
def CertifiedRepresentedConfigurationAndP94ExecutableMember
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    CertifiedRepresentedConfigurationAndP94Assignment → Prop
  | .configuration assignment =>
      AuthoritativeRepresentedConfigurationFamilyPublicJudgment input certified plan.spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros assignment
  | .conformation assignment =>
      IndependentCoordinateFrameAssignment premises certified.result.parsed plan external
        carbohydrateAuthority assignment

/-- Constructor-specific independent semantics for every result in the combined report. -/
def IndependentlyJudgedCertifiedRepresentedConfigurationAndP94Assignment
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    CertifiedRepresentedConfigurationAndP94Assignment → Prop
  | .configuration assignment =>
      AuthoritativeRepresentedConfigurationFamilyPublicJudgment input certified
        plan.spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros assignment
  | .conformation assignment =>
      IndependentCoordinateFrameAssignment premises certified.result.parsed plan external
        carbohydrateAuthority assignment

/-- Single shared-spatial report for every currently represented configuration family and every
assignment in the audited complete coordinate-frame P-94 transaction. -/
def analyzeCertifiedRepresentedConfigurationAndP94Report
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List CertifiedRepresentedConfigurationAndP94Assignment :=
  (analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies input certified
      plan.spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros).map
      .configuration ++
    (coordinateFrameCompleteTransaction premises certified plan external
      carbohydrateAuthority).assignments.map .conformation

/-- The configuration constructor is preserved exactly in both directions. -/
theorem configuration_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) :
    .configuration assignment ∈
        analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
            carbohydrateAuthority ↔
      AuthoritativeRepresentedConfigurationFamilyPublicJudgment input certified plan.spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros assignment := by
  simp [analyzeCertifiedRepresentedConfigurationAndP94Report,
    mem_analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_iff_publicJudgment]

/-- Explicitly named migration certificate: the combined report's configuration branch is
characterized by the authoritative total-semantic/conflict-aware public judgment. -/
theorem
    configuration_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff_authoritativePublicJudgment
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : CertifiedDerivedSpatialFullereneRCTAndSpiroAssignment) :
    .configuration assignment ∈
        analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
            carbohydrateAuthority ↔
      AuthoritativeRepresentedConfigurationFamilyPublicJudgment input certified plan.spatial
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros assignment :=
  configuration_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff premises input
    certified plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
      carbohydrateAuthority assignment

/-- The conformation constructor is present exactly for the independent P-94 coordinate-frame
assignment relation. -/
theorem conformation_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    .conformation assignment ∈
        analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
            carbohydrateAuthority ↔
      IndependentCoordinateFrameAssignment premises certified.result.parsed plan external
        carbohydrateAuthority assignment := by
  simp only [analyzeCertifiedRepresentedConfigurationAndP94Report, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨configuration, _present, impossible⟩ | ⟨conformation, present, equality⟩)
    · cases impossible
    · cases equality
      exact
        (coordinateFrameCompleteTransaction_assignments_mem_iff_independent premises certified plan
          external carbohydrateAuthority assignment).mp present
  · intro independent
    exact Or.inr ⟨assignment,
      (coordinateFrameCompleteTransaction_assignments_mem_iff_independent premises certified plan
        external carbohydrateAuthority assignment).mpr independent,
      rfl⟩

/-- Flattened membership is exact for the executable meaning of either disjoint result branch. -/
theorem mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (output : CertifiedRepresentedConfigurationAndP94Assignment) :
    output ∈ analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority ↔
      CertifiedRepresentedConfigurationAndP94ExecutableMember premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority output := by
  cases output with
  | configuration assignment =>
      exact configuration_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff premises
        input certified plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros
          external carbohydrateAuthority assignment
  | conformation assignment =>
      exact conformation_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff premises
        input certified plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros
          external carbohydrateAuthority assignment

/-- Each branch is internally duplicate-free and the constructors are disjoint, so the combined
report is globally duplicate-free without erasing any legitimate cross-kind result. -/
theorem analyzeCertifiedRepresentedConfigurationAndP94Report_nodup
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
      observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
        carbohydrateAuthority).Nodup := by
  rw [analyzeCertifiedRepresentedConfigurationAndP94Report]
  apply List.Nodup.append
  · exact
      (analyzeCertifiedNormalizedWithAuthoritativeRepresentedConfigurationFamilies_nodup input
        certified
        plan.spatial observations derivedPlanes derivedHelices fullerenes rctPairs spiros).map
          (by intro left right equality; cases equality; rfl)
  · exact
      (coordinateFrameCompleteTransaction_assignments_nodup premises certified plan external
        carbohydrateAuthority).map (by intro left right equality; cases equality; rfl)
  · rw [List.disjoint_left]
    intro output configurationPresent conformationPresent
    obtain ⟨assignment, _present, rfl⟩ := List.mem_map.mp configurationPresent
    simp at conformationPresent

/-- Every emitted combined-report member satisfies its independent configuration or conformation
judgment. -/
theorem analyzeCertifiedRepresentedConfigurationAndP94Report_member_judged
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (output : CertifiedRepresentedConfigurationAndP94Assignment)
    (present : output ∈
      analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority) :
    IndependentlyJudgedCertifiedRepresentedConfigurationAndP94Assignment premises input certified
      plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
        carbohydrateAuthority output := by
  cases output with
  | configuration assignment =>
      exact
        (configuration_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff premises input
          certified plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros
            external carbohydrateAuthority assignment).mp present
  | conformation assignment =>
      exact
        (conformation_mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff premises input
          certified plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros
            external carbohydrateAuthority assignment).mp present

/-- Global duplicate-freedom turns exact flattened membership into literal multiplicity one. -/
theorem count_analyzeCertifiedRepresentedConfigurationAndP94Report_eq_one_iff
    (premises : IndependentInOutPremises
      BlueBookP94.P94MolecularBicyclicFramework.ThetaFramework)
    (input : CertifiedLocalizedCIPInput)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (output : CertifiedRepresentedConfigurationAndP94Assignment) :
    List.count output
        (analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
          observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
            carbohydrateAuthority) = 1 ↔
      CertifiedRepresentedConfigurationAndP94ExecutableMember premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority output := by
  rw [← mem_analyzeCertifiedRepresentedConfigurationAndP94Report_iff]
  constructor
  · intro countOne
    exact List.count_pos_iff.mp (by omega)
  · exact List.count_eq_one_of_mem
      (analyzeCertifiedRepresentedConfigurationAndP94Report_nodup premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority)

/-- End-to-end correctness of the shared report. Every result has its independent family judgment;
the certified molecule also has total uncapped Rules-1a--6 comparison over every generated
occurrence-ligand pair on the exact expanded ranking graph. -/
theorem
    analyzeCertifiedRepresentedConfigurationAndP94Report_member_judged_and_expandedOccurrenceComparisonsTotal
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
    (fullerenes : List FullereneConfigurationInput)
    (rctPairs : List RCTPairConfigurationInput)
    (spiros : List SpiroConfigurationInput)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (output : CertifiedRepresentedConfigurationAndP94Assignment)
    (present : output ∈
      analyzeCertifiedRepresentedConfigurationAndP94Report premises input certified plan
        observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority) :
    IndependentlyJudgedCertifiedRepresentedConfigurationAndP94Assignment premises input certified
        plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority output ∧
      AuthoritativeCIPOccurrenceCompleteness.ExpandedOccurrenceRule6ComparisonsTotal certified
        state := by
  exact
    ⟨analyzeCertifiedRepresentedConfigurationAndP94Report_member_judged premises input certified
        plan observations derivedPlanes derivedHelices fullerenes rctPairs spiros external
          carbohydrateAuthority output present,
      AuthoritativeCIPOccurrenceCompleteness.expandedOccurrenceRule6ComparisonsTotal_of_chemical_applicability
        certified kekule state⟩

end

end TetraStereo.OneCenter
