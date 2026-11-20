import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryWitness
import TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice
import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSplicedMirrorWitness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A concrete selector for splicing two states at distinct original-root arms. Selection
uses the full occurrence history's first atom after the root. Shared atoms in molecular
rings therefore do not identify distinct arm occurrences. All selector laws and descriptor-map
readback are derived; no key or label correspondence is assumed. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingRawStateSplice
open LocalizedChemicalRingJointPreparedCrossGeometryWitness (branchMosaicMap)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)

noncomputable section
open scoped Classical

def rootSelect {n : Nat} (atom : Fin n) (key : CanonicalOccurrenceKey) : Bool :=
  decide (key.history.reverse.tail.head? = some atom.val)

def rootSplice (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (left right : OccurrenceAuxState) : OccurrenceAuxState :=
  splice (rootSelect atom) left right

theorem singleton_prefix_iff_head {α : Type*} (atom : α) (path : List α) :
    [atom] <+: path ↔ path.head? = some atom := by
  cases path with
  | nil => simp
  | cons first rest => simp [eq_comm]

theorem rootSelect_rawOccurrenceKey {n : Nat} (atom : Fin n)
    (unit : OccurrenceUnit (Fin n)) :
    rootSelect atom (rawOccurrenceKey unit) = decide ([atom] <+: unit.path) := by
  unfold rootSelect rawOccurrenceKey
  simp only [List.map_reverse, List.reverse_reverse, List.map_cons, List.tail_cons,
    List.head?_map, singleton_prefix_iff_head]
  cases unit.path.head? <;> simp [Fin.val_inj]

theorem rootSplice_descriptorMap (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (left right : OccurrenceAuxState) :
    rawStateDescriptorMap input (rootSplice input atom left right) =
      branchMosaicMap input [atom] (rawStateDescriptorMap input left)
        (rawStateDescriptorMap input right) := by
  funext unit
  unfold rootSplice
  rw [rawStateDescriptorMap_splice, rootSelect_rawOccurrenceKey]
  simp only [branchMosaicMap, decide_eq_true_eq]

theorem rootSelect_path {n : Nat} (atom root : Fin n) (path : List (Fin n)) :
    rootSelect atom (canonicalOccurrenceKey (rawPathNode root path)) =
      decide (path.head? = some atom) := by
  change rootSelect atom (rawOccurrenceKey (⟨root, path⟩ : OccurrenceUnit (Fin n))) = _
  rw [rootSelect_rawOccurrenceKey]
  simp only [singleton_prefix_iff_head]

theorem boundaryPath_of_root (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (rootAddress : target.1.address = [])
    (path : List input.Atom) : boundaryPath target path = path := by
  have equality := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
    ((input.mem_localizedOccurrences_iff _ _).mp target.2) rootAddress
  have nodeEq := congrArg (fun occurrence => occurrence.node) equality
  change target.1.node = OfficialCIPNode.root target.1.root at nodeEq
  simp [boundaryPath, nodeEq, OfficialCIPNode.root]

theorem rootSelect_boundary_left (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (rootAddress : target.1.address = [])
    (atom : input.Atom) (path : List input.Atom) (head : path.head? = some atom) :
    rootSelect atom (canonicalOccurrenceKey
      (rawPathNode target.1.root (boundaryPath target path))) = true := by
  rw [boundaryPath_of_root input target rootAddress, rootSelect_path, head]
  simp

theorem rootSelect_boundary_right (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (rootAddress : target.1.address = [])
    (left right : input.Atom) (distinct : left ≠ right)
    (path : List input.Atom) (head : path.head? = some right) :
    rootSelect left (canonicalOccurrenceKey
      (rawPathNode target.1.root (boundaryPath target path))) = false := by
  rw [boundaryPath_of_root input target rootAddress, rootSelect_path, head]
  simp [Ne.symm distinct]

/-- All path-selection and recursive query premises are discharged. The only comparison
input is a tie in the concrete spliced root state; arm-key locality supplies this input. -/
theorem mirrorTransport_of_rootSplice_tie
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : LocalizedChemicalRingInheritedRefusalCases.OccurrenceData input mol c node)
    (reached : LocalizedMarkedReachableConfigurations.Reached mol node)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates
        input input.detectedMultiCenterMolecule cfg d)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie :
      let entry := LocalizedChemicalRingInheritedRefusalCases.referenceAt input mol c node data left
      let stateL := LocalizedChemicalRingJointPreparedCorrectionWitness.originalState
        input mol node (LocalizedChemicalRingPhysicalSense.inputGeometry input) []
      let stateR := LocalizedChemicalRingJointPreparedCorrectionWitness.originalState
        input mol node (LocalizedGenericMarkedRecalculation.mirror
          (LocalizedChemicalRingPhysicalSense.inputGeometry input)) []
      LocalizedChemicalRingJointMarkerFrameExecution.slotKeys input mol single c node data
          (rootSplice input entry stateL stateR) [] left =
        LocalizedChemicalRingJointMarkerFrameExecution.slotKeys input mol single c node data
          (rootSplice input entry stateL stateR) [] right) :
    RootedTetrahedralBranchSymmetry.MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right) := by
  apply LocalizedChemicalRingJointPreparedSplicedMirrorWitness.mirrorTransport_of_spliced_tie
    input mol agreement admissible supported single charge c node data reached rootAddress
    left right distinct cfg calibrated current
    (rootSelect (LocalizedChemicalRingInheritedRefusalCases.referenceAt input mol c node data left))
  · exact rootSelect_boundary_left input data.target rootAddress _
  · apply rootSelect_boundary_right input data.target rootAddress
    intro equality
    exact distinct (LocalizedChemicalRingProperRotationConsensus.referenceAt_injective
      input mol c node data equality)
  · exact tie

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector.rootSelect_rawOccurrenceKey
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector.rootSplice_descriptorMap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector.rootSelect_path
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector.boundaryPath_of_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector.rootSelect_boundary_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector.rootSelect_boundary_right
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector.mirrorTransport_of_rootSplice_tie
