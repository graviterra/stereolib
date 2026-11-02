import TetraStereo.OneCenter.LocalizedRetainedContextObservationReadback
import TetraStereo.OneCenter.LocalizedActualRule4aNodeReadback
import TetraStereo.OneCenter.LocalizedActualArmReadback
import TetraStereo.OneCenter.DeclarativeCIPRetainedStereoEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Retained Rule-4a readback bundle

`rankEvidence` records an unavailable reading as an absent Rule-4a label (`⊥`). That is the
right code for missing real data, and it is the wrong code for a ring-duplicate address: the
duplicate is on the hierarchy, its localized label is `none`, and the actual Rule-4a priority
of that label is the present zero. `retainedRankEvidence` keeps the real unavailable row at
`⊥` and writes the present nonstereogenic code on ring duplicates.

`RetainedContextTreeRankReadback` is the shared bundle for that stage. Every realized node is
either an available real atom or an actual ring duplicate whose reading is `unavailable` and
whose localized label is `none`. Readings that the descriptor map returns are tetrahedral.
Rule 3 is absent, and Rules 4b, 4c, and 5 stay masked, because the molecule is simple-bonded.
The bundle does not assume `Acyclic` and does not assume every node is available.

The nodewise facts are the public label theorem of
`LocalizedRetainedContextObservationReadback`. This file does not rebuild the walk or the
reader.
-/

namespace TetraStereo.OneCenter
namespace RetainedContextStereoReadback

open CertifiedLocalizedCIPInput
open DeclarativeCIP
open LocalizedCumulativeDecoratedTree
open MolecularEvidenceTree
open Rule4aTableBridge
noncomputable section
open scoped Classical

universe u

/-- Real available data, or an actual ring duplicate whose reading is unavailable.
The ring branch stores the localized label `none`, which is the label of `.unavailable`. -/
inductive RetainedRankNodeStatus
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (graph : RootedDigraph Atom) (node : graph.Node) : Prop where
  | realAvailable
      (real : (graph.label node).provenance = .realAtom)
      (available : occurrenceReading molecule descriptorMap unit graph node ≠ .unavailable)
  | ringDuplicate
      (distance : ℕ)
      (duplicate : (graph.label node).provenance = .ringDuplicate distance)
      (unavailable : occurrenceReading molecule descriptorMap unit graph node = .unavailable)
      (noneLabel :
        (occurrenceReading molecule descriptorMap unit graph node).toLocalizedLabel = none)

/-- Upgrade the public real-or-ring split. Ring provenance forces the unavailable reading and
the localized label `none`; those are not extra chemical assumptions. -/
theorem RetainedRankNodeStatus.of_split
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (graph : RootedDigraph Atom) (node : graph.Node)
    (split :
      ((graph.label node).provenance = .realAtom ∧
        occurrenceReading molecule descriptorMap unit graph node ≠ .unavailable) ∨
      ∃ distance, (graph.label node).provenance = .ringDuplicate distance) :
    RetainedRankNodeStatus molecule descriptorMap unit graph node := by
  rcases split with ⟨real, available⟩ | ⟨distance, duplicate⟩
  · exact .realAvailable real available
  · exact .ringDuplicate distance duplicate
      (occurrenceReading_of_ringDuplicate molecule descriptorMap unit graph node distance
        duplicate)
      (by
        rw [occurrenceReading_of_ringDuplicate molecule descriptorMap unit graph node distance
          duplicate]
        rfl)

/-- On a ring duplicate the pre-retained Rule-4a label is bottom. The old nil equality, which
identifies that label with the present priority code, does not hold. -/
theorem stereoLabel_rankEvidence_rule4a_ringDuplicate_eq_bot
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graph : RootedDigraph input.Atom) (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (rankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node = ⊥ := by
  have unavailable := occurrenceReading_of_ringDuplicate input.moleculeGraph descriptorMap unit
    graph node distance duplicate
  unfold stereoLabel stereoValue rankEvidence rule4aObservation
  rw [unavailable]
  rfl

/-- Retained Rule 4a at a ring duplicate is the present code of priority zero. -/
theorem stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_code
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graph : RootedDigraph input.Atom) (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (retainedRankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node =
      ((code StereogenicUnitKind.nonstereogenic.priority : StereoCode) : StereoLabel) := by
  rw [stereoLabel_retainedRankEvidence_rule4a_ringDuplicate input.moleculeGraph descriptorMap
      unit graph node distance duplicate, code_eq_encode]

/-- The same present code is the kind priority of the unavailable reading. -/
theorem stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_kindPriority
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graph : RootedDigraph input.Atom) (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (retainedRankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node =
      ((code (occurrenceReading input.moleculeGraph descriptorMap unit graph node).kindPriority :
        StereoCode) : StereoLabel) := by
  rw [stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_code descriptorMap unit graph
      node distance duplicate,
    occurrenceReading_of_ringDuplicate input.moleculeGraph descriptorMap unit graph node
      distance duplicate]
  rfl

/-- The retained ring label is present, so it is not the old bottom label. -/
theorem stereoLabel_rankEvidence_ne_retainedRankEvidence_rule4a_ringDuplicate
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graph : RootedDigraph input.Atom) (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (rankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node ≠
      stereoLabel graph (retainedRankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node := by
  intro same
  rw [stereoLabel_rankEvidence_rule4a_ringDuplicate_eq_bot descriptorMap unit graph node distance
      duplicate,
    stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_code descriptorMap unit graph node
      distance duplicate] at same
  cases same

/-- An available real node keeps the ordinary present kind code under retained evidence. -/
theorem stereoLabel_retainedRankEvidence_rule4a_real_available
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graph : RootedDigraph input.Atom) (node : graph.Node)
    (real : (graph.label node).provenance = .realAtom)
    (available : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠
      .unavailable) :
    stereoLabel graph (retainedRankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node =
      ((code (occurrenceReading input.moleculeGraph descriptorMap unit graph node).kindPriority :
        StereoCode) : StereoLabel) := by
  unfold stereoLabel
  rw [retainedRankEvidence_eq_rankEvidence_of_not_ringDuplicate input.moleculeGraph descriptorMap
      unit graph node (not_ringDuplicate_of_realAtom graph node real)]
  simpa [stereoLabel] using
    stereoLabel_rankEvidence_rule4a descriptorMap unit graph node available

/-- Actual labels, tetrahedral readings, the real-or-ring split, and the Rule-4a-only mask.
Rule 3 is one of the masked columns. -/
structure RetainedContextTreeRankReadback
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  label : ∀ (node : (ruleMajorTreeGraph tree).Node)
      (actual : LocalizedCumulativeDecoratedTree input carrierFuel),
      subtreeAt? tree node.1 = some actual →
        actual.label =
          (occurrenceReading input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph tree) node).toLocalizedLabel
  tetrahedral : ∀ node : (ruleMajorTreeGraph tree).Node,
      (occurrenceReading input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) node).IsTetrahedral
  nodeStatus : ∀ node : (ruleMajorTreeGraph tree).Node,
      RetainedRankNodeStatus input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) node
  rule4aOnly : Rule4aOnly (ruleMajorTreeGraph tree)
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))

theorem RetainedContextTreeRankReadback.rule3_eq_bot
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    (node : (ruleMajorTreeGraph tree).Node) :
    stereoLabel (ruleMajorTreeGraph tree)
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        .rule3DoubleBondGeometry node = ⊥ :=
  hyp.rule4aOnly .rule3DoubleBondGeometry (by
    intro eq
    cases eq) node

/-- Declarative provenance of a realized node is the official source provenance. This is the
erasure already used to state the public label theorem; it is not a second walk. -/
private theorem retainedGraphLabel_eq_source
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (node : (ruleMajorTreeGraph tree).Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree node.1 = some actual) :
    (ruleMajorTreeGraph tree).label node =
      actual.source.occurrence.1.node.toDeclarativeLabel := by
  have erased : (toOfficialSourceTree tree).subtreeAt? node.1 =
      some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, lookup]
    rfl
  have raw := (toOfficialSourceTree tree).declarativeLabel_eq_of_subtreeAt?
    (toOfficialSourceTree actual) node erased
  rw [show (ruleMajorTreeGraph tree).label node =
      (toOfficialSourceTree tree).declarativeLabel node from rfl, raw, toOfficialSourceTree_source]

/-- A realized simple-bonded child of a detected target has the retained rank bundle.
The reader is the molecular reader at that target. Real nodes are available. Every other
carrier node is a ring duplicate with localized label `none`. -/
theorem retainedContextTreeRankReadback_of_molecularReader
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input
      (input.molecularReader descriptorMap target.occurrence) tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target) :
    RetainedContextTreeRankReadback tree descriptorMap unit := by
  let graph := ruleMajorTreeGraph tree
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node actual lookup
    exact (input.retainedRealizedTree_label_eq_occurrenceReading descriptorMap singleBonded
      target unit targetUnit tree realizes rootChild node actual lookup).1
  · intro node
    exact occurrenceReading_tetrahedral_of_map input.moleculeGraph descriptorMap unit graph
      tetrahedralMap node
  · intro node
    obtain ⟨_erased, erasedLookup⟩ :=
      (toOfficialSourceTree tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
        node.1 node.2
    rw [toOfficialSourceTree_subtreeAt?_eq, Option.map_eq_some_iff] at erasedLookup
    obtain ⟨actual, lookup, _erasedEq⟩ := erasedLookup
    have fact := input.retainedRealizedTree_label_eq_occurrenceReading descriptorMap
      singleBonded target unit targetUnit tree realizes rootChild node actual lookup
    by_cases readingUnavailable :
        occurrenceReading input.moleculeGraph descriptorMap unit graph node = .unavailable
    · have notReal : (graph.label node).provenance ≠ .realAtom := by
        intro real
        exact (fact.2.1).1 real readingUnavailable
      obtain ⟨distance, officialRing, _sourceUnavailable⟩ := fact.2.2 notReal
      have graphRing : ((ruleMajorTreeGraph tree).label node).provenance =
          .ringDuplicate distance := by
        have labelEq := retainedGraphLabel_eq_source tree node lookup
        rw [labelEq, OfficialCIPNode.toDeclarativeLabel, officialRing]
        rfl
      exact .ringDuplicate distance graphRing readingUnavailable (by
        rw [readingUnavailable]
        rfl)
    · have available : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠
          .unavailable := readingUnavailable
      exact .realAvailable ((fact.2.1).2 available) available
  · exact rule4aOnly_retainedRankEvidence_of_simpleBonded input.moleculeGraph descriptorMap unit
      graph singleBonded

/-- The generated dependency reader is the molecular reader, so the same bundle holds for it. -/
theorem retainedGeneratedContextTreeRankReadback
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedRuleMajorReference.carrierFuel input))
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) tree)
    (rootChild : tree.source ∈
      input.certified.executableLocalizedRerootChildren target) :
    RetainedContextTreeRankReadback tree (LocalizedRuleMajorReference.descriptorMap input) unit := by
  have readerEq := LocalizedRuleMajorReference.molecularReader_eq_generatedReader_of_simpleBonded
    input singleBonded target.occurrence
  have realizes' : LocalizedCumulativeTreeRealizes input.certified
      (input.certified.molecularReader (LocalizedRuleMajorReference.descriptorMap input)
        target.occurrence) tree := by
    rw [← readerEq] at realizes
    exact realizes
  exact retainedContextTreeRankReadback_of_molecularReader
    (LocalizedRuleMajorReference.descriptorMap input)
    (fun occurrence value observed =>
      LocalizedRuleMajorReference.descriptorMap_tetrahedral input occurrence value observed)
    singleBonded target unit targetUnit tree realizes' rootChild

end
end RetainedContextStereoReadback
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.RetainedContextTreeRankReadback
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.RetainedRankNodeStatus.of_split
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.stereoLabel_rankEvidence_rule4a_ringDuplicate_eq_bot
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_code
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_kindPriority
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.stereoLabel_rankEvidence_ne_retainedRankEvidence_rule4a_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.stereoLabel_retainedRankEvidence_rule4a_real_available
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.RetainedContextTreeRankReadback.rule3_eq_bot
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.retainedContextTreeRankReadback_of_molecularReader
assert_kernel_only TetraStereo.OneCenter.RetainedContextStereoReadback.retainedGeneratedContextTreeRankReadback
