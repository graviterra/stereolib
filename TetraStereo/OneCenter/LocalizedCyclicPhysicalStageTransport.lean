import TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport
import TetraStereo.OneCenter.LocalizedRetainedContextAllOccurrences
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidenceNaturality
import TetraStereo.OneCenter.LocalizedRetainedContextObservationReadback
import TetraStereo.OneCenter.LocalizedRetainedCutAutomorphism
import TetraStereo.OneCenter.LocalizedCyclicRootArmReachability
import TetraStereo.OneCenter.LocalizedCyclicPhysicalNodeReflection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! # Actual cyclic mirror transport for retained Rule-4a stage observations

This module turns an actual graph automorphism carrying one compiled root ligand cursor to
another into pointwise reflected generated-reader agreement on the actual retained stage tree.
The physical mirror wrapper lives at the root setup seam; this file's core consumes the exact
`DetectedBranchTransport` and current successful compiled trees.
-/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicPhysicalStageTransport

open CertifiedLocalizedCIPInput
open DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier
open DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open LocalizedRuleMajorReference
open LocalizedCyclicGeneralRigidLabelCovariance
open LocalizedCyclicPhysicalBranchReaderTransport
open LocalizedCyclicRootArmReachability
open LocalizedCyclicPhysicalNodeReflection
open RootedTetrahedralBranchSymmetry
open Rule4aTableBridge
open LocalizedCumulativeDecoratedTree

noncomputable section

/-- `ReadsAgree` transports along an actual rooted graph isomorphism. Ancestor atom paths are
preserved by the isomorphism, so the same source-context occurrence is queried on both sides. -/
theorem readsAgree_of_iso
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    {molecule : MoleculeGraph Atom}
    {left right : RootedDigraph Atom}
    (e : molecule.Aut)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (iso : RootedDigraph.Iso left right)
    (reads : ReadsAgree molecule e imageMap sourceMap unit left) :
    ReadsAgree molecule e imageMap sourceMap unit right := by
  intro node steps occ real stepsEq occurrenceEq
  let sourceNode := iso.toEquiv.symm node
  have realSource : (left.label sourceNode).provenance = .realAtom := by
    rw [iso.map_label sourceNode]
    simp [sourceNode] at real ⊢
    exact real
  have sourceSteps : ancestorAtoms left sourceNode = some steps := by
    rw [ancestorAtoms_iso iso sourceNode]
    simpa [sourceNode] using stepsEq
  exact reads sourceNode steps occ realSource sourceSteps occurrenceEq

/-- A transported stage build determines the Rule-1a equality required by the actual
generated-reader transport. This projects the source-level constitutional observable theorem. -/
theorem rule1aTie_of_ruleMajorBuild_observable_transport
    {input : LocalizedRuleMajorReference.Input}
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {e : input.certified.moleculeGraph.Aut}
    {left : input.certified.LocalizedRerootCursor (LocalizedRuleMajorReference.carrierFuel input)}
    (aligned : input.certified.cursorPreviousRootAligned left)
    {stage stage' : LocalizedCumulativeRule45Stage}
    {read read' : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input) → Option LocalizedAuxiliaryLabel}
    {fuel fuel' : Nat} {key key' : input.certified.LocalizedRerootCumulativeRule45Key}
    (built : input.certified.buildRuleMajorCumulativeWithRead? stage read fuel left = some key)
    (built' : input.certified.buildRuleMajorCumulativeWithRead? stage' read' fuel'
      (input.certified.transportCursor singleBonded e left) = some key') :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      key.constitutional.rule1a key'.constitutional.rule1a = Ordering.eq := by
  have observable := ruleMajorBuild_observable_transport input.certified singleBonded e aligned
    built built'
  have layerEq := congrArg LocalizedConstitutionalObservable.rule1a observable
  simp only [constitutionalObservable] at observable
  simp only [constitutionalObservable] at layerEq
  exact (compareSparseLayers_compareNat_eq_iff _ _).mpr layerEq

private theorem actualSubtree_at_stageNode
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (node : (ruleMajorTreeGraph tree).Node) :
    ∃ actual, tree.decoratedSubtreeAt? node.1 = some actual := by
  let sourceTree := toOfficialSourceTree tree
  obtain ⟨erased, erasedLookup⟩ :=
    sourceTree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses node.1 node.2
  have mappedLookup : (tree.decoratedSubtreeAt? node.1).map toOfficialSourceTree = some erased := by
    have h := toOfficialSourceTree_subtreeAt? tree node.1
    rw [← h]
    exact erasedLookup
  obtain ⟨actual, lookup, _eq⟩ := Option.map_eq_some_iff.mp mappedLookup
  exact ⟨actual, lookup⟩

private theorem stageNode_label_eq_source
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (node : (ruleMajorTreeGraph tree).Node)
    {actual : LocalizedCumulativeDecoratedTree input fuel}
    (lookup : tree.decoratedSubtreeAt? node.1 = some actual) :
    (ruleMajorTreeGraph tree).label node =
      actual.source.occurrence.1.node.toDeclarativeLabel := by
  let sourceTree := toOfficialSourceTree tree
  have erasedLookup : sourceTree.subtreeAt? node.1 = some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt? tree node.1, lookup]
    rfl
  have labelEq := sourceTree.declarativeLabel_eq_of_subtreeAt?
    (toOfficialSourceTree actual) node erasedLookup
  change sourceTree.declarativeLabel node = _
  rw [labelEq, toOfficialSourceTree_source]

private theorem descriptorMap_eq_of_actualState
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (occurrence : Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1) :
    descriptorMap input unit = (referenceState input occurrence).map localizedAuxiliaryDescriptor := by
  have chosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded
    unit.1 occurrence).2 unitEq
  simp [descriptorMap, chosen]

private theorem subtreeAt?_eq_decoratedSubtreeAt?
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (address : List Nat) :
    subtreeAt? tree address = tree.decoratedSubtreeAt? address := by
  induction address generalizing tree with
  | nil => rfl
  | cons slot rest ih =>
      rw [subtreeAt?_cons, decoratedSubtreeAt?]
      cases tree.children[slot]? with
      | none => rfl
      | some child => exact ih child

private theorem occurrenceUnit_ext
    {Atom : Type*} {a b : OccurrenceUnit Atom} (rootEq : a.root = b.root)
    (pathEq : a.path = b.path) : a = b := by
  cases a
  cases b
  simp_all

private theorem descriptorMap_reflect_of_actualStateMirror
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (occurrence : Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1)
    (states : (referenceState input occurrence = none ∧
        referenceState input (input.certified.transportOccurrence singleBonded e occurrence) = none) ∨
      ∃ raw : RS, referenceState input occurrence = some (.chiral raw) ∧
        referenceState input (input.certified.transportOccurrence singleBonded e occurrence) =
          some (.chiral (RS.swap raw))) :
    descriptorMap input (mapDetected input.certified.moleculeGraph e unit) =
      (descriptorMap input).reflect unit := by
  have imageUnitEq : input.certified.molecularFrameUnit
      (input.certified.transportOccurrence singleBonded e occurrence).1 =
      (mapDetected input.certified.moleculeGraph e unit).1 := by
    rw [input.certified.molecularFrameUnit_transport singleBonded e occurrence, unitEq]
    rfl
  have chosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded
    unit.1 occurrence).2 unitEq
  have imageChosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded
    (mapDetected input.certified.moleculeGraph e unit).1
    (input.certified.transportOccurrence singleBonded e occurrence)).2 imageUnitEq
  rcases states with ⟨sourceNone, imageNone⟩ | ⟨raw, sourceState, imageState⟩
  · simp [descriptorMap, chosen, imageChosen, sourceNone, imageNone, DescriptorMap.reflect]
  · cases raw <;> simp [descriptorMap, chosen, imageChosen, sourceState, imageState,
      DescriptorMap.reflect, localizedAuxiliaryDescriptor, Descriptor.reflect, RS.swap]

variable {input : LocalizedRuleMajorReference.Input}
  {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  {cfg : input.certified.detectedMultiCenterMolecule.Configuration}

/-- The current Rule-4a stage graph records the physical mirror action at every actual reached
reader address. The source occurrence for each query is reconstructed from the retained cursor
frame and the exact ancestor walk; the branch transport supplies its generated state. -/
theorem actualRootArmGraph_readsAgree
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (rootReal : target.1.node.provenance = .realAtom)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (e : input.certified.moleculeGraph.Aut)
    {sourceSlot targetSlot : Fin 4}
    (slotDistinct : sourceSlot ≠ targetSlot)
    (transport : input.certified.DetectedBranchTransport e cfg frames.center
      (frames.detectedLigandPermutation sourceSlot)
      (frames.detectedLigandPermutation targetSlot) true) :
    ReadsAgree input.certified.moleculeGraph e (descriptorMap input) (descriptorMap input).reflect
      unit (frames.actualArmGraphs sourceSlot) := by
  let armL := (frames.stages sourceSlot).a
  let armR := (frames.stages targetSlot).a
  have cursorSent := LocalizedCyclicRootArmReachability.rootSlot_transport singleBonded frames
    rootAddress rootReal e transport
  have builtRAtTransport : input.certified.buildRuleMajorCumulativeWithRead? .rule4a
      (contextOccurrenceRead input target) (2 * (carrierFuel input + 1))
      (input.certified.transportCursor singleBonded e (frames.frame.cursorAt sourceSlot)) =
      some armR.key := by
    have h := congrArg
      (fun c => input.certified.buildRuleMajorCumulativeWithRead? .rule4a
        (contextOccurrenceRead input target) (2 * (carrierFuel input + 1)) c)
      cursorSent
    calc
      _ = input.certified.buildRuleMajorCumulativeWithRead? .rule4a
          (contextOccurrenceRead input target) (2 * (carrierFuel input + 1))
          (frames.frame.cursorAt targetSlot) := h
      _ = some armR.key := armR.built
  have tie := rule1aTie_of_ruleMajorBuild_observable_transport singleBonded
    (LocalizedCyclicGeneralRigidLabelCovariance.frames_cursor_aligned frames sourceSlot)
    armL.built builtRAtTransport
  let rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input) :=
    { occurrence := target, previous? := none }
  have armDistinct : armL.tree.source.occurrence ≠ armR.tree.source.occurrence := by
    intro same
    have currents := congrArg
      (fun occurrence : Occurrence input => occurrence.1.node.current?)
      (by simpa [armL.sourceEq, armR.sourceEq] using same)
    change (frames.frame.cursorAt sourceSlot).occurrence.1.node.current? =
      (frames.frame.cursorAt targetSlot).occurrence.1.node.current? at currents
    rw [frames.ligandAt sourceSlot, frames.ligandAt targetSlot] at currents
    have ligandEq := input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective
      frames.center (Option.some.inj currents)
    exact slotDistinct (frames.detectedLigandPermutation.injective ligandEq)
  let imageOccurrence := input.certified.transportOccurrence singleBonded e
      (frames.frame.cursorAt sourceSlot).occurrence
  have imageReaderEq : input.certified.molecularReader (descriptorMap input) target =
      contextOccurrenceRead input target := by
    simpa [contextOccurrenceRead] using
      (molecularReader_eq_generatedReader_of_simpleBonded input singleBonded target)
  let molecularArm : input.certified.RuleMajorContextArm (carrierFuel input) .rule4a
      (input.certified.molecularReader (descriptorMap input) target)
      (frames.frame.cursorAt sourceSlot) :=
    { tree := armL.tree
      key := armL.key
      sourceEq := armL.sourceEq
      built := by rw [imageReaderEq]; exact armL.built
      trace := by rw [imageReaderEq]; exact armL.trace }
  intro node steps occ nodeReal ancestorEq contextEq
  obtain ⟨actual, lookup⟩ := actualSubtree_at_stageNode armL.tree node
  have actualNodeReal : actual.source.occurrence.1.node.provenance = .realAtom := by
    let sourceTree := toOfficialSourceTree armL.tree
    have hlookup : sourceTree.subtreeAt? node.1 = some (toOfficialSourceTree actual) := by
      have h := toOfficialSourceTree_subtreeAt? armL.tree node.1
      rw [lookup] at h
      simpa using h
    have hlabel := sourceTree.declarativeLabel_eq_of_subtreeAt?
      (toOfficialSourceTree actual) node hlookup
    have hprov : ((ruleMajorTreeGraph armL.tree).label node).provenance =
        (toOfficialSourceTree actual).source.provenance.toDeclarative := by
      change (sourceTree.declarativeLabel node).provenance = _
      rw [hlabel]
      rfl
    have hreal : ((ruleMajorTreeGraph armL.tree).label node).provenance = .realAtom := by
      change ((frames.actualArmGraphs sourceSlot).label node).provenance = .realAtom
      exact nodeReal
    rw [hprov, toOfficialSourceTree_source] at hreal
    cases h : actual.source.occurrence.1.node.provenance with
    | realAtom => rfl
    | multipleBondDuplicate distance =>
        rw [h, OfficialCIPNodeProvenance.toDeclarative] at hreal
        cases hreal
    | ringDuplicate distance =>
        rw [h, OfficialCIPNodeProvenance.toDeclarative] at hreal
        cases hreal
    | placeholder kind distance =>
        cases kind with
        | phantom =>
            rw [h, OfficialCIPNodeProvenance.toDeclarative] at hreal
            cases hreal
        | lonePair =>
            rw [h, OfficialCIPNodeProvenance.toDeclarative] at hreal
            cases hreal
        | auxiliary =>
            rw [h, OfficialCIPNodeProvenance.toDeclarative] at hreal
            cases hreal
  have rootChild : armL.tree.source ∈ input.certified.executableLocalizedRerootChildren rootCursor := by
    rw [armL.sourceEq]
    simpa [rootCursor] using frames.childAt sourceSlot
  obtain ⟨walkSteps, walkEq, walkRoot, walkPath⟩ :=
    input.certified.retainedCursorFrame_eq_ancestorWalk singleBonded rootCursor armL.tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace molecularArm.trace) rootChild node actual
      (by simpa [subtreeAt?_eq_decoratedSubtreeAt?] using lookup)
  have stepsWalk : walkSteps = steps := by
    have walkAncestors : ancestorAtoms (frames.actualArmGraphs sourceSlot) node = some walkSteps := by
      change ancestorAtoms (ruleMajorTreeGraph armL.tree) node = some walkSteps
      simpa [retainedOccurrenceSteps_eq_ancestorAtoms] using walkEq
    exact Option.some.inj (walkAncestors.symm.trans ancestorEq)
  have contextUnit : occ.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩ := by
    unfold contextOccurrence at contextEq
    dsimp only [contextOccurrence] at contextEq
    split at contextEq
    · exact (congrArg Subtype.val (Option.some.inj contextEq)).symm
    · simp at contextEq
  have actualUnitEq : input.certified.molecularFrameUnit actual.source.occurrence.1 = occ.1 := by
    apply occurrenceUnit_ext
    · calc
        (input.certified.molecularFrameUnit actual.source.occurrence.1).root =
            (input.certified.molecularFrameUnit rootCursor.occurrence.1).root := walkRoot
        _ = unit.1.root := by simpa [rootCursor] using congrArg OccurrenceUnit.root targetUnit
        _ = occ.1.root := (congrArg OccurrenceUnit.root contextUnit).symm
    · calc
        (input.certified.molecularFrameUnit actual.source.occurrence.1).path =
            rerootWalk (input.certified.molecularFrameUnit rootCursor.occurrence.1).root
              (input.certified.molecularFrameUnit rootCursor.occurrence.1).path walkSteps := walkPath
        _ = rerootWalk unit.1.root unit.1.path walkSteps := by
          simp only [rootCursor]
          rw [targetUnit]
        _ = rerootWalk unit.1.root unit.1.path steps := by rw [stepsWalk]
        _ = occ.1.path := (congrArg OccurrenceUnit.path contextUnit).symm
  have ⟨inside, nonroot, rooted, dependency⟩ :=
    LocalizedCyclicRootArmReachability.arm_subtree_branch_facts frames rootAddress rootReal
      sourceSlot armL lookup
  obtain ⟨atom, current⟩ := input.certified.localizedRerootCursor_current_exists actual.source
  have reached := LocalizedCyclicRootArmReachability.arm_subtree_ligandBranchReaches
    singleBonded frames rootAddress rootReal sourceSlot armL lookup actualNodeReal atom current
  have occAtomEq : occ.1.atom = atom := by
    have derived := (input.certified.mem_localizedOccurrences_iff (carrierFuel input)
      actual.source.occurrence.1).mp actual.source.occurrence.2
    have head := input.certified.declarativeLocalizedOccurrence_node_history_head_eq_current derived
    rw [current] at head
    have last := input.certified.carrierOccurrence_history_getLast_eq_root singleBonded
      actual.source.occurrence
    have atomEq := input.certified.molecularFrameUnit_atom_eq_current
      actual.source.occurrence.1 head last
    calc
      occ.1.atom = (input.certified.molecularFrameUnit actual.source.occurrence.1).atom :=
        (congrArg OccurrenceUnit.atom actualUnitEq).symm
      _ = atom := atomEq
  have reachedUnit : LigandBranchReaches input.certified.detectedMultiCenterMolecule
      frames.center (frames.detectedLigandPermutation sourceSlot) occ.1.atom := by
    rw [occAtomEq]
    exact reached
  have states := state_mirror_of_actualRootArmRule1aTie singleBonded charge frames rootAddress
    rootReal slotDistinct cfg domain e transport tie actual.source.occurrence actualNodeReal occ
    actualUnitEq inside nonroot rooted reachedUnit
  exact descriptorMap_reflect_of_actualStateMirror input singleBonded e occ
    actual.source.occurrence actualUnitEq states

/-- Transfer the actual stage-tree reading relation to the faithful canonical predecessor cut. -/
theorem canonicalCut_readsAgree_of_actualRootArm
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (rootReal : target.1.node.provenance = .realAtom)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (e : input.certified.moleculeGraph.Aut)
    {sourceSlot targetSlot : Fin 4}
    (slotDistinct : sourceSlot ≠ targetSlot)
    (transport : input.certified.DetectedBranchTransport e cfg frames.center
      (frames.detectedLigandPermutation sourceSlot)
      (frames.detectedLigandPermutation targetSlot) true) :
    ReadsAgree input.certified.moleculeGraph e (descriptorMap input) (descriptorMap input).reflect
      unit (frames.canonicalCutGraphs singleBonded sourceSlot) := by
  let cut := frames.canonicalLigandCut singleBonded sourceSlot
  let iso : RootedDigraph.Iso (frames.canonicalCutGraphs singleBonded sourceSlot)
      (frames.actualArmGraphs sourceSlot) := Classical.choice cut.faithful
  exact readsAgree_of_iso e (descriptorMap input) (descriptorMap input).reflect unit iso.symm
    (actualRootArmGraph_readsAgree singleBonded charge frames rootAddress rootReal domain
      e slotDistinct transport)

end
end LocalizedCyclicPhysicalStageTransport
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport.readsAgree_of_iso
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport.rule1aTie_of_ruleMajorBuild_observable_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport.actualRootArmGraph_readsAgree
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport.canonicalCut_readsAgree_of_actualRootArm
