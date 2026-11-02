import TetraStereo.OneCenter.LocalizedOrderedTerminalTwinRefusal
import TetraStereo.OneCenter.LocalizedActualOrderedRootDeclarativeDescriptor
import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralAssignment
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Physical domain for a general complete ordered molecular report

This domain retains the existing arbitrary-depth finite acyclic single-bond physical class.
One distinguished root has pairwise properly distinguishable branches; every other detected
centre is constitutionally rigid with calibrated physical coordinates or has physical terminal
twins.  There is no reference-count restriction, atom-count bound, comparison-depth bound,
runtime-success premise, or atomic-number-injectivity requirement.

The actual root frame below is constructed from the graph.  It is not a field of the domain.
-/

namespace TetraStereo.OneCenter
open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry
open Rule4aTableBridge.ActualCentrePhysicalSetup
open DeclarativeCIP

/-- Physical hypotheses on the actual certified graph, detected inventory and configuration. -/
structure OrderedTreePhysicalDomain (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center) : Prop where
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  acyclic : input.certified.moleculeGraph.Acyclic
  constantCharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords
  centers : ActualGeneralRigidPhysicalDomain input.certified
    input.certified.detectedMultiCenterMolecule cfg root
  rootDistinct : ∀ i j : Fin 4, i ≠ j →
    ¬ ProperTransport input.certified.detectedMultiCenterMolecule cfg root i j
  rootCoordinates : input.certified.ActualCanonicalRootCoordinates
    (⟨root.1, root.2⟩ : input.certified.TetrahedralCenter)

noncomputable section
namespace OrderedTreePhysicalDomain
variable {input : LocalizedUniversalReference.Input}
  {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
  {root : input.certified.detectedMultiCenterMolecule.Center}
  (domain : OrderedTreePhysicalDomain input cfg root)

abbrev rootCenter (_domain : OrderedTreePhysicalDomain input cfg root) :
    input.certified.TetrahedralCenter := ⟨root.1, root.2⟩

include domain

theorem exists_rootFrame :
    ∃ frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input root) = some frame := by
  obtain ⟨frame, _, computed, _⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      domain.singleBonded domain.acyclic (globalCarrierFuel_adequate input)
      (ActualReaderPhysicalBranchInverse.topTarget input root)
      (ActualReaderPhysicalBranchInverse.topTarget_current input root) root rfl
  exact ⟨frame, computed⟩

def setup : Rule4aTableBridge.ActualCentrePhysicalSetup input where
  c := root
  frame := Classical.choose domain.exists_rootFrame
  frameComputed := Classical.choose_spec domain.exists_rootFrame
  singleBonded := domain.singleBonded
  acyclic := domain.acyclic
  hcharge := domain.constantCharge
  noDouble := domain.noDouble
  cfg := cfg
  physicalDomain := domain.centers
  center := ⟨root.1, root.2⟩
  hcenter := rfl

/-- A general physical root has a unique independently justified final assignment.  The successor
own-map theorem replaces this named production auxiliary interpretation with the ordered map. -/
theorem root_assignment :
    ∃ label : LocalizedAuxiliaryLabel,
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input root) = some label ∧
      FinalTetrahedralAssignment (geoProblem (input := input))
        (actualReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter) label ∧
      ∀ other, FinalTetrahedralAssignment (geoProblem (input := input))
        (actualReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter) other →
          other = label := by
  obtain ⟨rs, state, judgment, unique⟩ :=
    domain.setup.orderedReferenceState_top_descriptorJudgment
      domain.rootDistinct domain.rootCoordinates
  let label := classifyTetrahedralRSPseudo rs domain.setup.declarativeRule5PairCount
  have assigned : FinalTetrahedralAssignment (geoProblem (input := input))
      (actualReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter) label :=
    ⟨rs, judgment, rfl⟩
  have uniqueLabel := finalTetrahedralAssignment_existsUnique (geoProblem (input := input))
    (actualReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter)
    rs judgment unique
  exact ⟨label, state, assigned, fun other h => uniqueLabel.unique h assigned⟩

/-- The root's case is exactly the independent physical enantiomorphic-pair criterion. -/
theorem root_lowercase_iff_physical :
    ∃ label : LocalizedTetrahedralRSPseudoDescriptor,
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input root) = some label ∧
      (label.IsLowercase ↔
        physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg root = 1) :=
  domain.setup.exists_orderedReferenceState_descriptor_lowercase_iff_physicalCount
    domain.rootDistinct domain.rootCoordinates

/-- All supported terminal-twin centres refuse in the ordered fixed point at their own final
occurrence, independently of which centre was chosen as the distinguished physical root. -/
theorem terminalTwin_final_none
    (center : input.certified.TetrahedralCenter)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
      (input.certified.localizedFinalOccurrenceExecutable
        (LocalizedUniversalReference.carrierFuel input) center) = none := by
  rw [input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence]
  let c : input.certified.detectedMultiCenterMolecule.Center := ⟨center.1, center.2⟩
  apply orderedReferenceState_eq_none_of_globalTwinCenter input domain.singleBonded domain.acyclic
    input.certified.detectedMultiCenterMolecule rfl c
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (ActualReaderPhysicalBranchInverse.topTarget_current input c)
  · rw [ActualReaderPhysicalBranchInverse.topTarget_root]
    exact input.certified.isTetrahedralCenter_of_physicalLigandEquiv
      input.certified.detectedMultiCenterMolecule rfl c
  · exact twin

end OrderedTreePhysicalDomain
end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.exists_rootFrame
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.setup
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.root_assignment
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.root_lowercase_iff_physical
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.terminalTwin_final_none
