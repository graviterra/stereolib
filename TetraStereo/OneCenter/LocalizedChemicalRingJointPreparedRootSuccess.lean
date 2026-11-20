import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranch
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceProper
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootEmptyContext
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual original-root success for physically properly distinguishable branches, with
arbitrary rings and stereochemically dependent non-root centers. The actual generated key
ties are reconstructed and physically corrected; successful sorting and descriptor execution
are conclusions. The letter formula uses ordinary mathematical keys on actual generated
auxiliary evidence. It does not assert full IUPAC faithfulness of the experimental retained
reference policy or a physical enantiomorphic-pair characterization of lowercase. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess

open CertifiedLocalizedCIPInput
open MultiCenterMolecule (PairwiseProperDistinguishable)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedRootWitness (root_matched_of_tie)
open LocalizedChemicalRingJointPreparedRootSourceProper (sourceProper_of_queryBranches)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection (SourceProper)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedRootInput (root_reached root_data)
open LocalizedChemicalRingJointPreparedRootEmptyContext (ordinaryGeometryRank geometryRank_nil)
open LocalizedChemicalRingPhysicalSense (inputGeometry letterOfSign)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter? preparedDescriptor?)
open LocalizedGenericMarkedRecalculation (structuralDepth caseFromMirror?)
open LocalizedMarkedReachableConfigurations (Reached)
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

include agreement admissible supported charge calibrated in
/-- An actual generated root-key tie is source-proper, with all reference identities retained.
No correction oracle, branch certificate, label matching or reader-success premise remains. -/
theorem root_tie_sourceProper
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (rootAddress : data.target.1.address = []) (references : List input.Atom) (reflected : Bool)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right) :
    SourceProper input cfg data.target references (referenceAt input mol c node data left)
      (referenceAt input mol c node data right) := by
  obtain ⟨w⟩ := root_matched_of_tie input mol single charge c node data rootAddress
    (sideState input mol node (inputGeometry input) references reflected) references left right tie
  apply sourceProper_of_queryBranches input mol agreement admissible supported single charge cfg
    calibrated node reached c data references reflected left right _ _
    (fun same => distinct
      (LocalizedChemicalRingProperRotationConsensus.referenceAt_injective input mol c node data same)) w
  intro p valid d query payload actual
  exact Classical.choice (LocalizedChemicalRingJointPreparedRootBranch.query_branch
    input mol single c node data rootAddress
    (sideState input mol node (inputGeometry input) references reflected) references
    left right distinct tie p valid d query payload actual)

include agreement admissible supported charge calibrated in
/-- A root with physically distinct branches has the actual independent-key coordinate reading.
The root itself carries no inherited marks; internal reference populations are unrestricted. -/
theorem root_descriptor_eq_ordinary_signs
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] [] node =
      caseFromMirror?
        (some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
          permHandedness (ordinaryGeometryRank input single mol c node data false))))
        (some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c *
          permHandedness (ordinaryGeometryRank input single mol c node data true))).swap) := by
  have h := LocalizedChemicalRingJointPreparedRootAssignment.descriptor_eq_signs
    input mol agreement admissible supported single cfg c node data rootAddress current
    properDistinct []
    (root_tie_sourceProper input mol agreement admissible supported single charge cfg calibrated
      c node data reached rootAddress []) (calibrated c)
  simpa only [List.map_nil, geometryRank_nil] using h

include agreement admissible supported single charge calibrated in
/-- **Actual assignment succeeds at every properly distinguishable detected root.**
Arbitrary finite single-bond rings and arbitrary calibrated non-root centers are admitted.
All occurrence metadata, recursive labels, comparisons, sorting and execution are derived. -/
theorem assignCenter_success (c : input.detectedMultiCenterMolecule.Center)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c) :
    ∃ label, preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val =
      some label := by
  obtain ⟨data, rootAddress⟩ := root_data input mol agreement admissible supported single c
  have h := root_descriptor_eq_ordinary_signs input mol agreement admissible supported single
    charge cfg calibrated c (canonicalCenterRoot c.1.val) data (root_reached input mol agreement c)
    rootAddress rfl properDistinct
  change preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) c.1.val = _ at h
  rw [h]
  exact ⟨_, rfl⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess.root_tie_sourceProper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess.root_descriptor_eq_ordinary_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess.assignCenter_success
