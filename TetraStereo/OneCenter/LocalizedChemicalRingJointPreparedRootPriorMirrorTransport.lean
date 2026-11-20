import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceKeyAlgebra
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualArmReadSource
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! An actual original-root prior tie between physically distinct branches yields an
independent physical mirror transport. Actual semantic reader locality, reflected generated
labels, full-key separation and the one-state splice tie are all derived here. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorMirrorTransport

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointPreparedRootEmptyContext (refinedKey_nil)
open LocalizedChemicalRingJointPreparedRootArmLocality
open LocalizedChemicalRingJointPreparedRootBranchSelector
open LocalizedChemicalRingJointPreparedActualArmReadSource
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingReferenceConsensusReflection (mirrorFact rawStateDescriptorMap_mirror)
open LocalizedRecursiveAuxiliaryPhysicalDomain
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open MultiCenterMolecule (PairwiseProperDistinguishable)
open RootedTetrahedralBranchSymmetry (MirrorTransport)

noncomputable section
open scoped Classical

theorem mirrorTransport_of_priorTie
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg c)
    (left right : Fin 4) (distinct : left ≠ right)
    (priorTie :
      (ofLex (rawStateKeys input single (sideState input mol node (inputGeometry input) [] false)
        data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left)).1 =
      (ofLex (rawStateKeys input single (sideState input mol node (inputGeometry input) [] false)
        data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right)).1) :
    MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right) := by
  let state0 := sideState input mol node (inputGeometry input) [] false
  let state1 := sideState input mol node (inputGeometry input) [] true
  let stateS := rootSplice input (referenceAt input mol c node data left) state0 state1
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  have reflected : state1 = state0.map mirrorFact := by
    simpa [state0, state1, sideState] using
      (LocalizedChemicalRingJointPreparedReflection.generated_mirror input mol
        (structuralDepth mol node) (inputGeometry input) node [])
  have different : rawStateKeys input single state0 data.target data.real unit rfl left ≠
      rawStateKeys input single state0 data.target data.real unit rfl right := by
    intro equal
    have full : slotKeys input mol single c node data state0 [] left =
        slotKeys input mol single c node data state0 [] right := by
      unfold slotKeys
      rw [refinedKey_nil, refinedKey_nil]
      exact congrArg (fun key => toLex (key, ([] : LocalizedChemicalRingJointMarkerKey.JointMarker))) equal
    have proper := LocalizedChemicalRingJointPreparedRootSuccess.root_tie_sourceProper
      input mol agreement admissible supported single charge cfg calibrated c node data reached
      rootAddress [] false left right distinct full
    have transport := LocalizedChemicalRingJointPreparedRootPhysicalTransport.properTransport_of_sourceProper
      input mol c node data cfg rootAddress current [] left right proper
    exact properDistinct _ _ (fun equality => distinct (data.ligandOf.injective equality)) transport
  have localLeft (W D : Nat) :
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input stateS)
        unit ((rootFrame input mol single c node data stateS).actualArmGraphs left) W D =
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input state0)
        unit ((rootFrame input mol single c node data stateS).actualArmGraphs left) W D := by
    apply retainedCompleteLigandRule5KeyAt_congr input.moleculeGraph _
      (fun _ _ _ first second =>
        (toOfficialSourceTree ((rootFrame input mol single c node data stateS).stages left).a.tree).declarativeAddressing.parent_unique first second)
      _ _ unit ?_ W D
    intro graphNode steps occurrence real ancestors context
    exact rootSplice_consult_left input mol single c node data rootAddress state0 state1 stateS
      left occurrence (arm_read_consult input mol single c node data stateS left rootAddress
        graphNode steps occurrence real ancestors context)
  have localRight (W D : Nat) :
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input stateS)
        unit ((rootFrame input mol single c node data stateS).actualArmGraphs right) W D =
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input state0).reflect
        unit ((rootFrame input mol single c node data stateS).actualArmGraphs right) W D := by
    rw [← rawStateDescriptorMap_mirror, ← reflected]
    apply retainedCompleteLigandRule5KeyAt_congr input.moleculeGraph _
      (fun _ _ _ first second =>
        (toOfficialSourceTree ((rootFrame input mol single c node data stateS).stages right).a.tree).declarativeAddressing.parent_unique first second)
      _ _ unit ?_ W D
    intro graphNode steps occurrence real ancestors context
    exact rootSplice_consult_right input mol single c node data rootAddress state0 state1 stateS
      left right distinct occurrence (arm_read_consult input mol single c node data stateS right rootAddress
        graphNode steps occurrence real ancestors context)
  have equal := LocalizedChemicalRingJointPreparedRootSpliceKeyAlgebra.rawKeys_eq_of_arm_locality
    input mol single c node data state0 stateS left right priorTie different localLeft localRight
  have tie : slotKeys input mol single c node data stateS [] left =
      slotKeys input mol single c node data stateS [] right := by
    unfold slotKeys
    rw [refinedKey_nil, refinedKey_nil]
    exact congrArg (fun key => toLex (key, ([] : LocalizedChemicalRingJointMarkerKey.JointMarker))) equal
  exact mirrorTransport_of_rootSplice_tie input mol agreement admissible supported single charge
    c node data reached rootAddress current cfg calibrated left right distinct tie

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorMirrorTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPriorMirrorTransport.mirrorTransport_of_priorTie
