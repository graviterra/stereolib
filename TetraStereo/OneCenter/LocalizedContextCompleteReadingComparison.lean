import TetraStereo.OneCenter.LocalizedRuleMajorActualCompleteReadingComparison
import TetraStereo.OneCenter.LocalizedContextRule4aCanonicalBridge
import TetraStereo.OneCenter.LocalizedContextRule4bCanonicalBridge
import TetraStereo.OneCenter.LocalizedContextRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedContextNoReferenceRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedContextStereoReadback
import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.DeclarativeCIPObservedCompleteReadingSignature
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Actual rule-major scalar comparisons at arbitrary retained-root contexts. Each side uses its
own realized contextual tree, but both observed keys retain the same outer molecular unit. Earlier
Rule-1a and Rule-4a ties remain explicit for the later cross-stage prefix proof. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4cObservationBridge
noncomputable section
open scoped Classical

private theorem molecule_bond_le_one {input : CertifiedLocalizedCIPInput}
    (singleBonded : input.moleculeGraph.SimpleBonded) :
    ∀ atom other, input.moleculeGraph.bond atom other ≤ 1 := by
  intro atom other
  rcases Nat.eq_zero_or_pos (input.moleculeGraph.bond atom other) with zero | positive
  · rw [zero]
    exact Nat.zero_le 1
  · exact le_of_eq (singleBonded atom other positive)

private theorem rootTree_lookup {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    tree.decoratedSubtreeAt? [] = some tree := by
  rw [decoratedSubtreeAt?]

section Generic

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {unit : DetectedOccurrence input.moleculeGraph}

/-- Actual Rule-4b scalar order agrees with the independently projected contextual Rule-4b
component. The readback and local observer equations are the only semantic inputs. -/
theorem contextTrees_ruleMajor_scalar4b_compare
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {leftReference rightReference : RS}
    {fuelLeft fuelRight : Nat}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input (.rule4b leftReference) read
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input (.rule4b rightReference) read
      fuelRight right keyRight)
    (readbackLeft : ContextTreeRankReadback left descriptorMap unit)
    (readbackRight : ContextTreeRankReadback right descriptorMap unit)
    (observationsLeft : ∀ rule node actual, left.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit.1.root
        rule node = priorityValue rule (armObservation rule actual))
    (observationsRight : ∀ rule node actual, right.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit.1.root
        rule node = priorityValue rule (armObservation rule actual))
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyLeft) (scalar4b keyRight) =
      compare
        (observedRule4bComponent (ruleMajorTreeGraph left)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit.1.root)
          (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph left)
            (senseOf leftReference)) W D (ruleMajorTreeGraph left).root)
        (observedRule4bComponent (ruleMajorTreeGraph right)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit.1.root)
          (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph right)
            (senseOf rightReference)) W D (ruleMajorTreeGraph right).root) := by
  let graphLeft := ruleMajorTreeGraph left
  let graphRight := ruleMajorTreeGraph right
  let observeLeft := contextualNodeObservation input.moleculeGraph graphLeft unit.1.root
  let observeRight := contextualNodeObservation input.moleculeGraph graphRight unit.1.root
  let evidenceLeft := readingEvidence input.moleculeGraph descriptorMap unit graphLeft
    (senseOf leftReference)
  let evidenceRight := readingEvidence input.moleculeGraph descriptorMap unit graphRight
    (senseOf rightReference)
  have hsingle := molecule_bond_le_one singleBonded
  have maskLeft := rule4abOnly_readingEvidence_of_single input.moleculeGraph descriptorMap unit
    graphLeft hsingle (senseOf leftReference)
  have maskRight := rule4abOnly_readingEvidence_of_single input.moleculeGraph descriptorMap unit
    graphRight hsingle (senseOf rightReference)
  have fullLeft := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceLeft
  have fullRight := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceRight
  have realizesLeft := LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft
  have realizesRight := LocalizedRuleMajorSortTrace.realizes_of_trace traceRight
  have bridgeLeft := contextTree_node_bridge4b left observeLeft observationsLeft readbackLeft
    maskLeft widthLeft depthLeft graphLeft.root left keyLeft traceLeft (rootTree_lookup left)
  have bridgeRight := contextTree_node_bridge4b right observeRight observationsRight readbackRight
    maskRight widthRight depthRight graphRight.root right keyRight traceRight (rootTree_lookup right)
  exact compare_of_pathFirstDifference
    (ordinaryKeyWithObservations_stereo_wellShaped graphLeft observeLeft evidenceLeft W D
      .rule4bLikeUnlikeDescriptorPairs graphLeft.root)
    (ordinaryKeyWithObservations_stereo_wellShaped graphRight observeRight evidenceRight W D
      .rule4bLikeUnlikeDescriptorPairs graphRight.root)
    bridgeLeft.2.2 bridgeRight.2.2
    (fun outcome => rule4b_pathFirstDifference_iff fullLeft.tableMatch fullRight.tableMatch
      realizesLeft realizesRight tied tied4a outcome)

/-- Actual Rule-4c scalar order agrees with the independently projected contextual Rule-4c
component, using the Rule-4c evidence mask at each side. -/
theorem contextTrees_ruleMajor_scalar4c_compare
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {leftReference rightReference : RS}
    {fuelLeft fuelRight : Nat}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input (.rule4c leftReference) read
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input (.rule4c rightReference) read
      fuelRight right keyRight)
    (readbackLeft : ContextTreeRankReadback left descriptorMap unit)
    (readbackRight : ContextTreeRankReadback right descriptorMap unit)
    (observationsLeft : ∀ rule node actual, left.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit.1.root
        rule node = priorityValue rule (armObservation rule actual))
    (observationsRight : ∀ rule node actual, right.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit.1.root
        rule node = priorityValue rule (armObservation rule actual))
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c keyLeft) (scalar4c keyRight) =
      compare
        (observedRule4cComponent (ruleMajorTreeGraph left)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit.1.root)
          (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph left)
            (senseOf leftReference)) W D (ruleMajorTreeGraph left).root)
        (observedRule4cComponent (ruleMajorTreeGraph right)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit.1.root)
          (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph right)
            (senseOf rightReference)) W D (ruleMajorTreeGraph right).root) := by
  let graphLeft := ruleMajorTreeGraph left
  let graphRight := ruleMajorTreeGraph right
  let observeLeft := contextualNodeObservation input.moleculeGraph graphLeft unit.1.root
  let observeRight := contextualNodeObservation input.moleculeGraph graphRight unit.1.root
  let evidenceLeft := readingEvidence4c input.moleculeGraph descriptorMap unit graphLeft
    (senseOf leftReference)
  let evidenceRight := readingEvidence4c input.moleculeGraph descriptorMap unit graphRight
    (senseOf rightReference)
  have hsingle := molecule_bond_le_one singleBonded
  have maskLeft := rule4abcOnly_readingEvidence4c_of_single input.moleculeGraph descriptorMap unit
    graphLeft hsingle (senseOf leftReference)
  have maskRight := rule4abcOnly_readingEvidence4c_of_single input.moleculeGraph descriptorMap unit
    graphRight hsingle (senseOf rightReference)
  have fullLeft := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceLeft
  have fullRight := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceRight
  have realizesLeft := LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft
  have realizesRight := LocalizedRuleMajorSortTrace.realizes_of_trace traceRight
  have bridgeLeft := contextTree_node_bridge4c left observeLeft observationsLeft readbackLeft
    maskLeft widthLeft depthLeft graphLeft.root left keyLeft traceLeft (rootTree_lookup left)
  have bridgeRight := contextTree_node_bridge4c right observeRight observationsRight readbackRight
    maskRight widthRight depthRight graphRight.root right keyRight traceRight (rootTree_lookup right)
  exact compare_of_pathFirstDifference
    (ordinaryKeyWithObservations_stereo_wellShaped graphLeft observeLeft evidenceLeft W D
      .rule4cPseudoasymmetricDescriptor graphLeft.root)
    (ordinaryKeyWithObservations_stereo_wellShaped graphRight observeRight evidenceRight W D
      .rule4cPseudoasymmetricDescriptor graphRight.root)
    bridgeLeft.2.2.2 bridgeRight.2.2.2
    (fun outcome => rule4c_pathFirstDifference_iff fullLeft.tableMatch fullRight.tableMatch
      fullLeft.labelMatch fullRight.labelMatch realizesLeft realizesRight tied tied4a outcome)

/-- With no uppercase reference, the actual second scalar is compared against the genuine
contextual pseudoasymmetric Rule-4c component; lowercase `r` and `s` observations remain active. -/
theorem contextTrees_ruleMajor_noReference4c_compare
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {fuelLeft fuelRight : Nat}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input .rule4cNoReference read
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input .rule4cNoReference read
      fuelRight right keyRight)
    (readbackLeft : ContextTreeRankReadback left descriptorMap unit)
    (readbackRight : ContextTreeRankReadback right descriptorMap unit)
    (observationsLeft : ∀ rule node actual, left.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit.1.root
        rule node = priorityValue rule (armObservation rule actual))
    (observationsRight : ∀ rule node actual, right.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit.1.root
        rule node = priorityValue rule (armObservation rule actual))
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyLeft) (scalar4b keyRight) =
      compare
        (observedRule4cComponent (ruleMajorTreeGraph left)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit.1.root)
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph left)) W D (ruleMajorTreeGraph left).root)
        (observedRule4cComponent (ruleMajorTreeGraph right)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit.1.root)
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph right)) W D (ruleMajorTreeGraph right).root) := by
  let graphLeft := ruleMajorTreeGraph left
  let graphRight := ruleMajorTreeGraph right
  let observeLeft := contextualNodeObservation input.moleculeGraph graphLeft unit.1.root
  let observeRight := contextualNodeObservation input.moleculeGraph graphRight unit.1.root
  let evidenceLeft := noReferenceEvidence4c input.moleculeGraph descriptorMap unit graphLeft
  let evidenceRight := noReferenceEvidence4c input.moleculeGraph descriptorMap unit graphRight
  have hsingle := molecule_bond_le_one singleBonded
  have maskLeft := rule4acOnly_noReferenceEvidence4c_of_single input.moleculeGraph descriptorMap
    unit graphLeft hsingle
  have maskRight := rule4acOnly_noReferenceEvidence4c_of_single input.moleculeGraph descriptorMap
    unit graphRight hsingle
  have fullLeft := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceLeft
  have fullRight := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceRight
  have realizesLeft := LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft
  have realizesRight := LocalizedRuleMajorSortTrace.realizes_of_trace traceRight
  have bridgeLeft := contextTree_node_bridge_noReference4c left observeLeft observationsLeft
    readbackLeft maskLeft widthLeft depthLeft graphLeft.root left keyLeft traceLeft
    (rootTree_lookup left)
  have bridgeRight := contextTree_node_bridge_noReference4c right observeRight observationsRight
    readbackRight maskRight widthRight depthRight graphRight.root right keyRight traceRight
    (rootTree_lookup right)
  exact compare_of_pathFirstDifference
    (ordinaryKeyWithObservations_stereo_wellShaped graphLeft observeLeft evidenceLeft W D
      .rule4cPseudoasymmetricDescriptor graphLeft.root)
    (ordinaryKeyWithObservations_stereo_wellShaped graphRight observeRight evidenceRight W D
      .rule4cPseudoasymmetricDescriptor graphRight.root)
    bridgeLeft.2.2 bridgeRight.2.2
    (fun outcome => noReference4c_pathFirstDifference_iff fullLeft.tableMatch fullRight.tableMatch
      fullLeft.labelMatch fullRight.labelMatch realizesLeft realizesRight tied tied4a outcome)

end Generic

section Generated

variable (input : LocalizedRuleMajorReference.Input)
  (singleBonded : input.certified.moleculeGraph.SimpleBonded)
  (acyclic : input.certified.moleculeGraph.Acyclic)
  (target : input.certified.LocalizedRerootCursor
    (input.certified.certified.input.molecule.atomCount + 1))
  (unit : DetectedOccurrence input.certified.moleculeGraph)
  (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)

include input singleBonded acyclic target unit targetUnit

private theorem generated_observations
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    {stage : LocalizedCumulativeRule45Stage} {fuel : Nat}
    {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input.certified stage
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) fuel tree key)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree)
        unit.1.root rule node = priorityValue rule (armObservation rule actual) := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace (trace)
  have rootEq := contextTree_outerRoot_eq_unitRoot singleBonded acyclic target unit targetUnit
    tree rootChild
  intro rule node actual lookup
  rw [← rootEq]
  exact contextualTree_nodeObservation singleBonded acyclic tree realizes rule node actual lookup

/-- Generated-reader specialization for actual Rule-4b traces at an arbitrary actual child. -/
theorem generatedContextTrees_ruleMajor_scalar4b_compare
    {fuelLeft fuelRight : Nat}
    {leftReference rightReference : RS}
    (left right : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    {keyLeft : input.certified.LocalizedRerootCumulativeRule45Key}
    {keyRight : input.certified.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input.certified (.rule4b leftReference)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input.certified (.rule4b rightReference)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelRight right keyRight)
    (leftChild : left.source ∈ input.certified.executableLocalizedRerootChildren target)
    (rightChild : right.source ∈ input.certified.executableLocalizedRerootChildren target)
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyLeft) (scalar4b keyRight) =
      compare
        (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph left)
          W D (some (senseOf leftReference)))).1
        (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph right)
          W D (some (senseOf rightReference)))).1 := by
  have readbackLeft := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit left (LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft) leftChild
  have readbackRight := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit right (LocalizedRuleMajorSortTrace.realizes_of_trace traceRight) rightChild
  have observationsLeft := generated_observations input singleBonded acyclic target unit targetUnit
    left traceLeft leftChild
  have observationsRight := generated_observations input singleBonded acyclic target unit targetUnit
    right traceRight rightChild
  have comparison := contextTrees_ruleMajor_scalar4b_compare singleBonded left right traceLeft
    traceRight readbackLeft readbackRight observationsLeft observationsRight widthLeft depthLeft
    widthRight depthRight tied tied4a
  simpa [contextualCompleteReadingAt] using comparison

/-- Generated-reader specialization for actual Rule-4c traces at an arbitrary actual child. -/
theorem generatedContextTrees_ruleMajor_scalar4c_compare
    {fuelLeft fuelRight : Nat}
    {leftReference rightReference : RS}
    (left right : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    {keyLeft : input.certified.LocalizedRerootCumulativeRule45Key}
    {keyRight : input.certified.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input.certified (.rule4c leftReference)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input.certified (.rule4c rightReference)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelRight right keyRight)
    (leftChild : left.source ∈ input.certified.executableLocalizedRerootChildren target)
    (rightChild : right.source ∈ input.certified.executableLocalizedRerootChildren target)
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c keyLeft) (scalar4c keyRight) =
      compare
        (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph left)
          W D (some (senseOf leftReference)))).2
        (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph right)
          W D (some (senseOf rightReference)))).2 := by
  have readbackLeft := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit left (LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft) leftChild
  have readbackRight := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit right (LocalizedRuleMajorSortTrace.realizes_of_trace traceRight) rightChild
  have observationsLeft := generated_observations input singleBonded acyclic target unit targetUnit
    left traceLeft leftChild
  have observationsRight := generated_observations input singleBonded acyclic target unit targetUnit
    right traceRight rightChild
  have comparison := contextTrees_ruleMajor_scalar4c_compare singleBonded left right traceLeft
    traceRight readbackLeft readbackRight observationsLeft observationsRight widthLeft depthLeft
    widthRight depthRight tied tied4a
  simpa [contextualCompleteReadingAt] using comparison

/-- Generated no-reference specialization keeps the true pseudoasymmetric observation even when
the uppercase reference population is empty. -/
theorem generatedContextTrees_ruleMajor_noReference4c_compare
    {fuelLeft fuelRight : Nat}
    (left right : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    {keyLeft : input.certified.LocalizedRerootCumulativeRule45Key}
    {keyRight : input.certified.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input.certified .rule4cNoReference
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input.certified .rule4cNoReference
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelRight right keyRight)
    (leftChild : left.source ∈ input.certified.executableLocalizedRerootChildren target)
    (rightChild : right.source ∈ input.certified.executableLocalizedRerootChildren target)
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyLeft) (scalar4b keyRight) =
      compare
        (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph left)
          W D none)).2
        (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph right)
          W D none)).2 := by
  have readbackLeft := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit left (LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft) leftChild
  have readbackRight := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit right (LocalizedRuleMajorSortTrace.realizes_of_trace traceRight) rightChild
  have observationsLeft := generated_observations input singleBonded acyclic target unit targetUnit
    left traceLeft leftChild
  have observationsRight := generated_observations input singleBonded acyclic target unit targetUnit
    right traceRight rightChild
  have comparison := contextTrees_ruleMajor_noReference4c_compare singleBonded left right
    traceLeft traceRight readbackLeft readbackRight observationsLeft observationsRight
    widthLeft depthLeft widthRight depthRight tied tied4a
  simpa [contextualCompleteReadingAt] using comparison

end Generated
end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTrees_ruleMajor_scalar4b_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTrees_ruleMajor_scalar4c_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTrees_ruleMajor_noReference4c_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextTrees_ruleMajor_scalar4b_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextTrees_ruleMajor_scalar4c_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextTrees_ruleMajor_noReference4c_compare
