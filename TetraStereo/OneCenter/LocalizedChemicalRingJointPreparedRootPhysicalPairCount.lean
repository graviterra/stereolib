import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPriorTie
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorMirrorTransport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorClassification
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Physical classification of the actual prepared root on finite single-bond molecular
inputs, including rings. Prior ties and physical enantiomorphic pairs are equivalent;
all label and key transport is derived. The absolute letter is the exact coordinate
reading in the independently defined retained-key order of the actual generated state.
This does not identify the auxiliary reference policy with a complete IUPAC specification. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPairCount

open CertifiedLocalizedCIPInput DeclarativeCIP
open MultiCenterMolecule (PairwiseProperDistinguishable)
open RootedTetrahedralBranchSymmetry (MirrorTransport Enantiomorphic)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointPreparedRootInput (root_reached root_data)
open LocalizedChemicalRingJointPreparedRootEmptyContext (ordinaryGeometryRank)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry letterOfSign)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedMarkedRetainedOrdinaryRanking (rawStateKeys)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (c : input.detectedMultiCenterMolecule.Center)
  (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
  (rootAddress : data.target.1.address = [])
  (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c)

abbrev rootKeys : Fin 4 → CompleteLigandRule5Key :=
  rawStateKeys input single
    (sideState input mol (canonicalCenterRoot c.1.val) (inputGeometry input) [] false)
    data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl

include agreement admissible supported charge calibrated rootAddress properDistinct in
theorem priorPair_iff_enantiomorphic (left right : Fin 4) :
    CompletePriorPair (rootKeys input mol single c data) left right ↔
      Enantiomorphic input.detectedMultiCenterMolecule cfg c (data.ligandOf left) (data.ligandOf right) := by
  constructor
  · rintro ⟨distinct, tied⟩
    have different : data.ligandOf left ≠ data.ligandOf right :=
      fun equal => distinct (data.ligandOf.injective equal)
    exact ⟨different,
      LocalizedChemicalRingJointPreparedRootPriorMirrorTransport.mirrorTransport_of_priorTie
        input mol agreement admissible supported single charge cfg calibrated c
        (canonicalCenterRoot c.1.val) data (root_reached input mol agreement c) rootAddress rfl
        properDistinct left right distinct tied,
      properDistinct _ _ different⟩
  · intro physical
    refine ⟨fun equal => physical.1 (congrArg data.ligandOf equal), ?_⟩
    exact LocalizedChemicalRingJointPreparedRootPhysicalPriorTie.priorTie_of_mirrorTransport
      input mol agreement admissible supported single cfg calibrated c data rootAddress
      left right physical.2.1

include agreement admissible supported charge calibrated rootAddress properDistinct in
theorem priorPairCount_eq_physical :
    completeRule5PairCount (rootKeys input mol single c data) =
      physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg c := by
  change sourceEnantiomorphicPairCount (CompletePriorPair (rootKeys input mol single c data)) = _
  calc
    _ = sourceEnantiomorphicPairCount (fun i j => Enantiomorphic
        input.detectedMultiCenterMolecule cfg c (data.ligandOf i) (data.ligandOf j)) :=
      sourceEnantiomorphicPairCount_congr_of_forall _ _
        (priorPair_iff_enantiomorphic input mol agreement admissible supported single charge cfg
          calibrated c data rootAddress properDistinct)
    _ = physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg c :=
      sourceEnantiomorphicPairCount_perm _
        (physicalEnantiomorphic_symmetric input.detectedMultiCenterMolecule cfg c) data.ligandOf

include agreement admissible supported charge calibrated in
theorem assignCenter_eq_physical_classification
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c) :
    ∃ (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
      (_rootAddress : data.target.1.address = []),
      preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val =
        some (classifyTetrahedralRSPseudo
          (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
            permHandedness (ordinaryGeometryRank input single mol c
              (canonicalCenterRoot c.1.val) data false)))
          (physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg c)) := by
  obtain ⟨data, rootAddress, classified⟩ :=
    LocalizedChemicalRingJointPreparedRootPriorClassification.assignCenter_eq_prior_classification
      input mol agreement admissible supported single charge cfg calibrated c properDistinct
  refine ⟨data, rootAddress, ?_⟩
  have count := priorPairCount_eq_physical input mol agreement admissible supported single charge
    cfg calibrated c data rootAddress properDistinct
  simpa only [rootKeys] using (classified.trans (congrArg
    (fun n => some (classifyTetrahedralRSPseudo
      (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
        permHandedness (ordinaryGeometryRank input single mol c
          (canonicalCenterRoot c.1.val) data false))) n)) count))

include agreement admissible supported single charge calibrated in
theorem assignCenter_success_lowercase_iff
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c) :
    ∃ descriptor,
      preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val =
        some descriptor ∧
      (descriptor.IsLowercase ↔ physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg c = 1) := by
  obtain ⟨data, rootAddress, classified⟩ := assignCenter_eq_physical_classification input mol
    agreement admissible supported single charge cfg calibrated c properDistinct
  exact ⟨_, classified, isLowercase_classify_iff _ _⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPairCount

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPairCount.priorPair_iff_enantiomorphic
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPairCount.priorPairCount_eq_physical
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPairCount.assignCenter_eq_physical_classification
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPairCount.assignCenter_success_lowercase_iff
