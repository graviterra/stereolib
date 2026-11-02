import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport
import TetraStereo.OneCenter.LocalizedRetainedRule4aCanonicalBridge
import TetraStereo.OneCenter.LocalizedActualOrderedRootIndependentPriority
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Recursive physical transport of actual auxiliary states in a root arm

Fix the evaluator's own final-root frame of a detected center, two distinct root slots `i, j`, and
one physical branch transport `e` from ligand `α i` to `α j` with mirror flag `μ`
(`DetectedBranchTransport`). The physical domain is `RecursiveAuxiliaryPhysicalDomain`: every
non-root detected center is a terminal twin or has calibrated coordinates. **No constitutional
rigidity is assumed.**

`Law z` says that the actual generated state at the transported occurrence is the source state
read through `retainedPhysicalLetter μ`: uppercase `R/S` swaps under a mirror, lowercase `r/s`
is fixed and `none` is fixed. `Reach z` says that `z` is the occurrence of an actual cursor reached
by executable reroot steps from the root slot `i`.

`law_of_reach` proves `Reach z → Law z` for every occurrence, by well-founded induction on the
actual dependency relation `LocalizedDepthDependency`. Rings, overlapping branches, non-rigid
auxiliary centers, Rule-4/5-decided auxiliary orders, lowercase auxiliary labels and refusals are
all inside the induction.

One step at a real detected non-root `y` (`law_of_calibrated`):

1. The source outcome is the actual retained outcome on the canonical predecessor cuts.
2. The hybrid map `H` agrees with the image map at every read by construction. On the three
   outward cuts it equals the actual map, because every read there is the unit of an actual
   occurrence reached outward from the slot, hence a strict dependency in the same root arm, where
   the induction hypothesis holds (`outward_readsAgree`).
3. The parent cut is constitutionally separated from the outward cuts inside a Rule-1a tied root
   arm (`parentSlot_separated_of_rootArmRule1aTie`, read back to the retained constitutional
   component by `constitutional_ne_of_separated`); the parent key change does not move the outcome.
4. `cuts_completeRootOutcome_transport` transports the hybrid outcome; the image cuts are the
   canonical cuts of `e·y` (`image_canonicalCut_eq`); the image's own actual outcome and uniqueness
   finish the step. The volume-sign law is derived from both calibrations and the branch sign law
   (`slotVolume_sign_of_calibrated`).

The parent cut may read outside the root arm; no transport law is needed there.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open LocalizedCumulativeDecoratedTree Rule4aTableBridge OfficialSparseCanonicalVectorComparison
open LocalizedRetainedMirrorDescriptorCorrectness LocalizedRecursiveAuxiliaryPhysicalDomain
open LocalizedCyclicGeneralRigidLabelCovariance LocalizedCyclicGeneralRigidPriority
open LocalizedCyclicMatchedReadingPhysicalTransport LocalizedCyclicRootArmReachability
open LocalizedCyclicPhysicalStageTransport
open RootedTetrahedralBranchSymmetry
open scoped Classical

noncomputable section

/-! ## The invariant -/

/-- The physical transport law at one occurrence. -/
def Law {input : Input} (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool) (z : Occurrence input) : Prop :=
  referenceState input (input.certified.transportOccurrence singleBonded e z) =
    (referenceState input z).map (retainedPhysicalLetter mirror)

/-- Reachability from one root slot by actual executable reroot steps. -/
def Reach {input : Input} {rootTarget : Occurrence input}
    {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
    {rootTargetUnit : input.certified.molecularFrameUnit rootTarget.1 = rootUnit.1}
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit) (i : Fin 4)
    (z : Occurrence input) : Prop :=
  ∃ cursor : input.certified.LocalizedRerootCursor (carrierFuel input),
    cursor.occurrence = z ∧
      Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
        (rootFrames.frame.cursorAt i) cursor

/-- Reachability from an arbitrary start cursor by actual executable reroot steps. -/
def ReachFrom {input : Input} (start : input.certified.LocalizedRerootCursor (carrierFuel input))
    (z : Occurrence input) : Prop :=
  ∃ cursor : input.certified.LocalizedRerootCursor (carrierFuel input),
    cursor.occurrence = z ∧
      Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified) start cursor

/-- The physical sign law of `e`, with mirror flag `mirror`, at every real center reached from
`start`. This is a statement about the physical configuration only. -/
def SignLawFrom {input : Input} (e : input.certified.moleculeGraph.Aut)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (start : input.certified.LocalizedRerootCursor (carrierFuel input)) : Prop :=
  ∀ cursor : input.certified.LocalizedRerootCursor (carrierFuel input),
    Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified) start cursor →
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
    ∀ d : input.certified.detectedMultiCenterMolecule.Center,
      cursor.occurrence.1.node.current? = some d.1 →
      input.certified.detectedMultiCenterMolecule.configurationSign cfg d *
          permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
            (input.certified.physicalDetectedAut e) d) =
        physicalMirrorFactor mirror *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg
            (input.certified.detectedMultiCenterMolecule.centerPerm
              (input.certified.physicalDetectedAut e) d)

/-! ## Generic helpers -/

private theorem occurrenceUnit_ext {Atom : Type*} {a b : OccurrenceUnit Atom}
    (rootEq : a.root = b.root) (pathEq : a.path = b.path) : a = b := by
  cases a
  cases b
  simp_all

theorem descriptorMap_eq_of_actualState (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (unit : DetectedOccurrence input.certified.moleculeGraph) (occurrence : Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1) :
    descriptorMap input unit =
      (referenceState input occurrence).map localizedAuxiliaryDescriptor := by
  have chosen := (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded
    unit.1 occurrence).2 unitEq
  simp [descriptorMap, chosen]

/-- The law at an occurrence makes its detected unit covariant. -/
theorem covariant_of_law {input : Input}
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool) (z : Occurrence input)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (unitEq : input.certified.molecularFrameUnit z.1 = unit.1)
    (law : Law singleBonded e mirror z) :
    LocalizedRecursiveAuxiliaryPhysicalDomain.Covariant input.certified.moleculeGraph e mirror
      (descriptorMap input) unit := by
  have source := descriptorMap_eq_of_actualState input singleBonded unit z unitEq
  have imageUnitEq : input.certified.molecularFrameUnit
      (input.certified.transportOccurrence singleBonded e z).1 =
        (mapDetected input.certified.moleculeGraph e unit).1 := by
    rw [input.certified.molecularFrameUnit_transport singleBonded e z, unitEq]
    rfl
  have image := descriptorMap_eq_of_actualState input singleBonded
    (mapDetected input.certified.moleculeGraph e unit)
    (input.certified.transportOccurrence singleBonded e z) imageUnitEq
  unfold Law at law
  unfold LocalizedRecursiveAuxiliaryPhysicalDomain.Covariant
  cases mirror with
  | false =>
      show descriptorMap input (mapDetected input.certified.moleculeGraph e unit) =
        descriptorMap input unit
      rw [image, source, law]
      cases referenceState input z <;> simp [retainedPhysicalLetter]
  | true =>
      show descriptorMap input (mapDetected input.certified.moleculeGraph e unit) =
        (descriptorMap input unit).map Descriptor.reflect
      rw [image, source, law]
      cases referenceState input z with
      | none => rfl
      | some label =>
          simp [localizedAuxiliaryDescriptor_retainedPhysicalLetter]

/-- Judgments with available coordinates are complete-root judgments on the supplied points. -/
theorem retainedContextualOutcomeAt_iff_completeRootOutcome {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom] (molecule : MoleculeGraph Atom)
    (map : DescriptorMap (DetectedOccurrence molecule)) (unit : DetectedOccurrence molecule)
    (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ)
    {coordinates : Fin 4 → Option CartesianPoint3} {points : Fin 4 → CartesianPoint3}
    (available : ∀ slot, coordinates slot = some (points slot))
    (outcome : Option LocalizedAuxiliaryLabel) :
    RetainedContextualOutcomeAt molecule map unit graphs W D coordinates outcome ↔
      CompleteRootOutcome (retainedContextualFrameKeysAt molecule map unit graphs W D) points
        outcome := by
  have judgment : ∀ descriptor,
      RetainedContextualDescriptorJudgmentAt molecule map unit graphs W D coordinates descriptor ↔
        CompleteRootDescriptorJudgment (retainedContextualFrameKeysAt molecule map unit graphs W D)
          points descriptor := by
    intro descriptor
    constructor
    · rintro ⟨other, otherAvailable, complete⟩
      have same : other = points := funext fun slot =>
        Option.some.inj ((otherAvailable slot).symm.trans (available slot))
      subst same
      exact complete
    · intro complete
      exact ⟨points, available, complete⟩
  cases outcome with
  | none =>
      simp only [RetainedContextualOutcomeAt, CompleteRootOutcome]
      exact not_congr (exists_congr judgment)
  | some descriptor =>
      simp only [RetainedContextualOutcomeAt, CompleteRootOutcome]
      exact judgment descriptor

/-! ## Image cuts are the canonical cuts of the transported occurrence -/

private theorem cut_eq_of_carriers {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) {root root' : Atom} (rootEq : root = root')
    (focus : Nodes molecule root) (incoming : Nodes molecule root)
    (anchor : CutAnchor focus (some incoming))
    (focus' : Nodes molecule root') (incoming' : Nodes molecule root')
    (anchor' : CutAnchor focus' (some incoming'))
    (focusEq : focus.1 = focus'.1) (incomingEq : incoming.1 = incoming'.1) :
    cutRetainedArm molecule root focus (some incoming) anchor =
      cutRetainedArm molecule root' focus' (some incoming') anchor' := by
  subst root'
  have hf : focus = focus' := Subtype.ext focusEq
  have hi : incoming = incoming' := Subtype.ext incomingEq
  subst focus'
  subst incoming'
  rfl

section ImageCut

variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  {imageUnit : DetectedOccurrence input.certified.moleculeGraph}

/-- The automorphic image of a source canonical cut is the image frame's canonical cut at the
transported slot. Complete carrier histories, not only atoms, are matched. -/
theorem image_canonicalCut_eq
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (frames : ContextFrameCompilation input target unit targetUnit)
    {imageTargetUnit : input.certified.molecularFrameUnit
      (input.certified.transportOccurrence singleBonded e target).1 = imageUnit.1}
    (imageFrames : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target) imageUnit imageTargetUnit)
    {k t : Fin 4}
    (sent : input.certified.transportCursor singleBonded e (frames.frame.cursorAt k) =
      imageFrames.frame.cursorAt t) :
    cutRetainedArm input.certified.moleculeGraph
        ((e : Equiv.Perm input.certified.Atom) (frames.frame.cursorAt k).occurrence.1.root)
        (imageNode e (frames.canonicalLigandCut singleBonded k).focus)
        ((some (frames.canonicalLigandCut singleBonded k).incoming).map (imageNode e))
        (cutAnchor_image e (frames.canonicalLigandCut singleBonded k).focus
          (some (frames.canonicalLigandCut singleBonded k).incoming)
          (frames.canonicalLigandCut singleBonded k).anchor) =
      imageFrames.canonicalCutGraphs singleBonded t := by
  have occurrenceSent := congrArg (fun c => c.occurrence) sent
  change input.certified.transportOccurrence singleBonded e
    (frames.frame.cursorAt k).occurrence = (imageFrames.frame.cursorAt t).occurrence
    at occurrenceSent
  have rootSent := congrArg (fun c => c.occurrence.1.root) sent
  change (e : Equiv.Perm input.certified.Atom)
    (frames.frame.cursorAt k).occurrence.1.root =
    (imageFrames.frame.cursorAt t).occurrence.1.root at rootSent
  apply cut_eq_of_carriers input.certified.moleculeGraph rootSent
  · rw [imageNode_carrier, (frames.canonicalLigandCut singleBonded k).focusCarrier,
      (imageFrames.canonicalLigandCut singleBonded t).focusCarrier]
    rw [mapCarrier_eq_mapCarrierNode, input.certified.occurrenceCarrierNode_transport,
      occurrenceSent]
  · rw [imageNode_carrier, (frames.canonicalLigandCut singleBonded k).incomingCarrier,
      (imageFrames.canonicalLigandCut singleBonded t).incomingCarrier]
    rw [mapCarrier_eq_mapCarrierNode, input.certified.occurrenceCarrierNode_transport]

end ImageCut

/-! ## The constitutional separation, read on the canonical cuts -/

section Separation

variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

/-- The retained constitutional component on one canonical cut is the actual stage graph's
observed rule key. -/
theorem canonicalCut_constitutional_eq
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (map : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph)) (slot : Fin 4) :
    constitutionalComponent (retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph map
        unit (frames.canonicalCutGraphs singleBonded slot) frames.W frames.D) =
      ruleKeyWithObservations (ruleMajorTreeGraph (frames.stages slot).a.tree) frames.W frames.D
        (retainedContextNodeObservation input.certified.moleculeGraph
          (ruleMajorTreeGraph (frames.stages slot).a.tree) unit)
        (ruleMajorTreeGraph (frames.stages slot).a.tree).root := by
  let iso : RootedDigraph.Iso (frames.canonicalCutGraphs singleBonded slot)
      (frames.actualArmGraphs slot) :=
    Classical.choice (frames.canonicalLigandCut singleBonded slot).faithful
  have keyEq := retainedCompleteLigandRule5KeyAt_iso input.certified.moleculeGraph map unit iso
    frames.W frames.D
  rw [← keyEq]
  rfl

/-- The actual constitutional comparison of the stage-`a` keys is the comparison of the observed
rule keys at the compiled window. -/
theorem stage_constitutional_compare
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit) (left right : Fin 4) :
    OfficialRuleMajorKey.compare (frames.stages left).a.key.constitutional
        (frames.stages right).a.key.constitutional =
      compare
        (ruleKeyWithObservations (ruleMajorTreeGraph (frames.stages left).a.tree) frames.W frames.D
          (retainedContextNodeObservation input.certified.moleculeGraph
            (ruleMajorTreeGraph (frames.stages left).a.tree) unit)
          (ruleMajorTreeGraph (frames.stages left).a.tree).root)
        (ruleKeyWithObservations (ruleMajorTreeGraph (frames.stages right).a.tree) frames.W
          frames.D
          (retainedContextNodeObservation input.certified.moleculeGraph
            (ruleMajorTreeGraph (frames.stages right).a.tree) unit)
          (ruleMajorTreeGraph (frames.stages right).a.tree).root) := by
  let targetCursor : input.certified.LocalizedRerootCursor (carrierFuel input) :=
    { occurrence := target, previous? := none }
  let armL := (frames.stages left).a
  let armR := (frames.stages right).a
  have realizesL := LocalizedRuleMajorSortTrace.realizes_of_trace armL.trace
  have realizesR := LocalizedRuleMajorSortTrace.realizes_of_trace armR.trace
  have childL : armL.tree.source ∈ input.certified.executableLocalizedRerootChildren targetCursor := by
    rw [armL.sourceEq]
    exact frames.childAt left
  have childR : armR.tree.source ∈ input.certified.executableLocalizedRerootChildren targetCursor := by
    rw [armR.sourceEq]
    exact frames.childAt right
  have widthL : (ruleMajorTreeGraph armL.tree).width ≤ frames.W :=
    (frames.stages left).a_width_le.trans (frames.widthBound left)
  have widthR : (ruleMajorTreeGraph armR.tree).width ≤ frames.W :=
    (frames.stages right).a_width_le.trans (frames.widthBound right)
  have heightL : (ruleMajorTreeGraph armL.tree).height ≤ frames.D :=
    (frames.stages left).a_depth_le.trans (frames.depthBound left)
  have heightR : (ruleMajorTreeGraph armR.tree).height ≤ frames.D :=
    (frames.stages right).a_depth_le.trans (frames.depthBound right)
  have observationsL := fun rule node actual lookup =>
    RetainedRule4aCanonicalBridge.retainedDecoratedObservation_eq_arm singleBonded targetCursor
      unit targetUnit armL.tree realizesL childL rule node actual lookup
  have observationsR := fun rule node actual lookup =>
    RetainedRule4aCanonicalBridge.retainedDecoratedObservation_eq_arm singleBonded targetCursor
      unit targetUnit armR.tree realizesR childR rule node actual lookup
  exact compare_eq_compare_vector
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace armL.trace).tableMatch realizesL)
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace armR.trace).tableMatch realizesR)
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph armL.tree)
      (retainedContextNodeObservation input.certified.moleculeGraph
        (ruleMajorTreeGraph armL.tree) unit) frames.W frames.D
      (ruleMajorTreeGraph armL.tree).root)
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph armR.tree)
      (retainedContextNodeObservation input.certified.moleculeGraph
        (ruleMajorTreeGraph armR.tree) unit) frames.W frames.D
      (ruleMajorTreeGraph armR.tree).root)
    (observedTree_node_bridge armL.tree _ observationsL widthL heightL
      (ruleMajorTreeGraph armL.tree).root armL.tree armL.key armL.trace (by
        change armL.tree.decoratedSubtreeAt? [] = some armL.tree
        rw [decoratedSubtreeAt?])).2
    (observedTree_node_bridge armR.tree _ observationsR widthR heightR
      (ruleMajorTreeGraph armR.tree).root armR.tree armR.key armR.trace (by
        change armR.tree.decoratedSubtreeAt? [] = some armR.tree
        rw [decoratedSubtreeAt?])).2

/-- Reader-free constitutional separation of two frame slots separates the retained
constitutional components of their canonical cuts, for every descriptor map. -/
theorem constitutional_ne_of_separated
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (map : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph)) {left right : Fin 4}
    (separated : ConstitutionallySeparated (frames.frame.cursorAt left)
      (frames.frame.cursorAt right)) :
    constitutionalComponent (retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph map
        unit (frames.canonicalCutGraphs singleBonded left) frames.W frames.D) ≠
      constitutionalComponent (retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph map
        unit (frames.canonicalCutGraphs singleBonded right) frames.W frames.D) := by
  have notTied := separated .rule4a .rule4a (contextOccurrenceRead input target)
    (contextOccurrenceRead input target) _ _ _ _ (frames.stages left).a.built
    (frames.stages right).a.built
  rw [stage_constitutional_compare singleBonded frames left right] at notTied
  rw [canonicalCut_constitutional_eq singleBonded frames map left,
    canonicalCut_constitutional_eq singleBonded frames map right]
  intro same
  rw [same] at notTied
  exact notTied ((listKey_compare_eq_iff _ _).2 rfl)

end Separation

/-! ## Reads of an actual arm are actual reached occurrences -/

section ArmReads

variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

private theorem actualSubtree_at_stageNode
    {fuel : Nat} (tree : LocalizedCumulativeDecoratedTree input.certified fuel)
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

private theorem subtreeAt?_eq_decoratedSubtreeAt?'
    {fuel : Nat} (tree : LocalizedCumulativeDecoratedTree input.certified fuel)
    (address : List Nat) :
    subtreeAt? tree address = tree.decoratedSubtreeAt? address := by
  induction address generalizing tree with
  | nil => rfl
  | cons slot rest ih =>
      rw [subtreeAt?_cons, decoratedSubtreeAt?]
      cases tree.children[slot]? with
      | none => rfl
      | some child => exact ih child

/-- **Arm-read reconstruction.** Every real read of the actual stage-`a` graph of a frame slot is
the detected unit of an actual real occurrence reached from that slot cursor. -/
theorem actualArm_read_source
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit) (slot : Fin 4)
    (node : (frames.actualArmGraphs slot).Node) (steps : List input.certified.Atom)
    (occ : DetectedOccurrence input.certified.moleculeGraph)
    (ancestorEq : ancestorAtoms (frames.actualArmGraphs slot) node = some steps)
    (contextEq : contextOccurrence input.certified.moleculeGraph unit steps = some occ) :
    ∃ cursor : input.certified.LocalizedRerootCursor (carrierFuel input),
      Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
          (frames.frame.cursorAt slot) cursor ∧
        input.certified.molecularFrameUnit cursor.occurrence.1 = occ.1 := by
  let arm := (frames.stages slot).a
  let rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input) :=
    { occurrence := target, previous? := none }
  obtain ⟨actual, lookup⟩ := actualSubtree_at_stageNode arm.tree node
  have rootChild : arm.tree.source ∈ input.certified.executableLocalizedRerootChildren rootCursor := by
    rw [arm.sourceEq]
    simpa [rootCursor] using frames.childAt slot
  obtain ⟨walkSteps, walkEq, walkRoot, walkPath⟩ :=
    input.certified.retainedCursorFrame_eq_ancestorWalk singleBonded rootCursor arm.tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) rootChild node actual
      (by simpa [subtreeAt?_eq_decoratedSubtreeAt?'] using lookup)
  have stepsWalk : walkSteps = steps := by
    have walkAncestors : ancestorAtoms (frames.actualArmGraphs slot) node = some walkSteps := by
      change ancestorAtoms (ruleMajorTreeGraph arm.tree) node = some walkSteps
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
              (input.certified.molecularFrameUnit rootCursor.occurrence.1).path walkSteps :=
          walkPath
        _ = rerootWalk unit.1.root unit.1.path walkSteps := by
          simp only [rootCursor]
          rw [targetUnit]
        _ = rerootWalk unit.1.root unit.1.path steps := by rw [stepsWalk]
        _ = occ.1.path := (congrArg OccurrenceUnit.path contextUnit).symm
  exact ⟨actual.source, arm_subtree_source_reachable frames slot arm lookup, actualUnitEq⟩

end ArmReads

/-! ## One executable step from an outward reached cursor into a frame slot -/

/-- An outward frame slot of an occurrence is an executable child of every outward cursor at that
occurrence. -/
theorem frame_outward_mem_children {input : Input} {target : Occurrence input}
    {unit : DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (cursorEq : cursor.occurrence = target) (previous : Occurrence input)
    (previousEq : cursor.previous? = some previous)
    (shorter : previous.1.address.length < target.1.address.length) {slot : Fin 4}
    (outward : IsLocalizedActualFrameOutwardCursor input.certified target
      (frames.frame.cursorAt slot)) :
    frames.frame.cursorAt slot ∈ input.certified.executableLocalizedRerootChildren cursor := by
  have start := (input.certified.executableLocalizedRerootChildren_mem_iff _ _).1
    (frames.childAt slot)
  rw [input.certified.executableLocalizedRerootChildren_mem_iff]
  obtain ⟨k, addressEq⟩ := outward
  have addressNe : (frames.frame.cursorAt slot).occurrence.1.address ≠ previous.1.address := by
    intro same
    have lengths := congrArg List.length same
    rw [addressEq] at lengths
    simp at lengths
    omega
  obtain ⟨occurrence, previous?⟩ := cursor
  simp only at cursorEq previousEq
  subst cursorEq
  subst previousEq
  refine ⟨frames.ligandCursor_previous singleBonded slot, ?_⟩
  have intended := start.2
  unfold intendedLocalizedRerootChildFrames at intended ⊢
  by_cases duplicate : occurrence.1.node.isDuplicateLeaf = true
  · simp [duplicate] at intended
  · simp only [duplicate, Bool.false_eq_true, ↓reduceIte] at intended ⊢
    exact List.mem_filter.2 ⟨intended, by simpa using addressNe⟩

/-! ## Facts about reached occurrences -/

section Reached

variable {input : Input} {rootTarget : Occurrence input}
  {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
  {rootTargetUnit : input.certified.molecularFrameUnit rootTarget.1 = rootUnit.1}

/-- A cursor reached from root slot `i` is outward, its occurrence is a proper descendant in the
root branch of slot `i`, and its outer root is the frame's root. -/
theorem cursor_facts (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom) (i : Fin 4)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor) :
    (∃ previous : Occurrence input, cursor.previous? = some previous ∧
        previous.1.address.length < cursor.occurrence.1.address.length) ∧
      input.certified.RootBranchContains (rootFrames.frame.cursorAt i).occurrence
        cursor.occurrence ∧
      cursor.occurrence.1.address ≠ [] ∧ rootFrames.center.1 = cursor.occurrence.1.root := by
  have addressEq := (rootFramePair rootFrames rootAddress i i).leftAddress
  change (rootFrames.frame.cursorAt i).occurrence.1.address =
    rootTarget.1.address ++ [(rootFramePair rootFrames rootAddress i i).leftSlot] at addressEq
  have deeper : rootTarget.1.address.length <
      (rootFrames.frame.cursorAt i).occurrence.1.address.length := by
    simp only [addressEq, List.length_append, List.length_singleton]
    omega
  have firstOut := input.certified.outward_first_cursor rootTarget
    (rootFrames.frame.cursorAt i) (rootFrames.childAt i) deeper
  have allOut := input.certified.outward_reachable_cursor rootTarget
    (rootFrames.frame.cursorAt i) cursor firstOut reachable
  have addrPrefix := input.certified.address_isPrefix_of_outward_reachable rootTarget
    (rootFrames.frame.cursorAt i) cursor firstOut reachable
  have rootEq := (rootFrame_target_facts rootFrames rootAddress rootReal).2.2
  obtain ⟨_valid, dependency, previous, previousEq, shorter⟩ := allOut
  refine ⟨⟨previous, previousEq, shorter⟩,
    ⟨firstOut.2.1.1.trans dependency.1.symm, addrPrefix⟩, ?_,
    rootEq.symm.trans dependency.1.symm⟩
  intro empty
  have positive := dependency.2
  simp [empty, rootAddress] at positive

/-- A reached occurrence is a proper descendant in the root branch of slot `i`, with the root of
the frame as outer root, and is reached by an outward cursor. -/
theorem reach_facts (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom) (i : Fin 4) {z : Occurrence input}
    (reach : Reach rootFrames i z) :
    ∃ cursor : input.certified.LocalizedRerootCursor (carrierFuel input),
      cursor.occurrence = z ∧
      Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
        (rootFrames.frame.cursorAt i) cursor ∧
      (∃ previous : Occurrence input, cursor.previous? = some previous ∧
        previous.1.address.length < z.1.address.length) ∧
      input.certified.RootBranchContains (rootFrames.frame.cursorAt i).occurrence z ∧
      z.1.address ≠ [] ∧ rootFrames.center.1 = z.1.root := by
  obtain ⟨cursor, cursorEq, reachable⟩ := reach
  subst cursorEq
  obtain ⟨previousData, inside, nonroot, rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  exact ⟨cursor, rfl, reachable, previousData, inside, nonroot, rooted⟩

/-- The current atom of a real reached occurrence lies in the physical ligand branch of slot `i`. -/
theorem reach_ligandBranchReaches
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom) (i : Fin 4)
    (cursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (reachable : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) cursor)
    (cursorReal : cursor.occurrence.1.node.provenance = .realAtom)
    (atom : input.certified.Atom) (current : cursor.occurrence.1.node.current? = some atom) :
    LigandBranchReaches input.certified.detectedMultiCenterMolecule rootFrames.center
      (rootFrames.detectedLigandPermutation i) atom := by
  rw [rootSlot_eq_canonicalLigandCursor singleBonded rootFrames rootAddress rootReal i]
    at reachable
  obtain ⟨seen, seenCurrent, reached⟩ :=
    input.certified.ligandArm_realAtom_mem_ligandBranchReaches rootFrames.center
      (input.certified.canonicalLigandReindex rootFrames.center
        (rootFrames.detectedLigandPermutation i)) cursor reachable cursorReal
  have seenEq : seen = atom := Option.some.inj (seenCurrent.symm.trans current)
  subst seen
  unfold LigandBranchReaches
  rw [input.certified.canonicalLigandReindex_spec]
  exact reached

end Reached

/-! ## Terminal twins refuse, from the graph alone -/

/-- A detected terminal-twin center refuses. Only the graph of the detected molecule is used. -/
theorem twinState_none (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (unitEq : input.certified.molecularFrameUnit target.1 = unit.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (cyclicContextFrameCompilation input singleBonded target real unit unitEq).center) :
    referenceState input target = none := by
  let frames := cyclicContextFrameCompilation input singleBonded target real unit unitEq
  have meaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have targetCurrent : target.1.node.current? = some frames.center.1 := meaning.2
  obtain ⟨centerAtom, leftLeaf, rightLeaf, current, _tetra, leftNeighbors, rightNeighbors,
      leavesDistinct, zEq, massEq, _chargeEq⟩ :=
    CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinLeaves_of_globalTwinCenter
      input input.certified.detectedMultiCenterMolecule rfl frames.center
      target targetCurrent twin
  have centerEq : centerAtom = frames.center.1 :=
    Option.some.inj (current.symm.trans targetCurrent)
  have leftNeighbors' : input.certified.moleculeGraph.neighborFinset leftLeaf =
      {frames.center.1} := by rw [← centerEq]; exact leftNeighbors
  have rightNeighbors' : input.certified.moleculeGraph.neighborFinset rightLeaf =
      {frames.center.1} := by rw [← centerEq]; exact rightNeighbors
  exact LocalizedRuleMajorReference.referenceState_eq_none_of_actualPhysicalTerminalTwinLeaves
    input singleBonded target frames.center meaning leftLeaf rightLeaf leftNeighbors' rightNeighbors'
    leavesDistinct rootTetrahedral zEq massEq

/-! ## The volume-sign law from two calibrations -/

private theorem volumeSign_reindex (points : Fin 4 → CartesianPoint3) (σ : Equiv.Perm (Fin 4)) :
    rationalVolumeSign (slotVolume fun slot => points (σ slot)) =
      rationalVolumeSign (slotVolume points) * permHandedness σ := by
  have hcal := orientedVolume_calibrated_eq (fun index => points (σ index)) points σ fun _ => rfl
  unfold slotVolume
  rw [hcal, rationalVolumeSign_permutedOrientedVolume]

section Sign

variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

/-- **Volume-sign law.** Calibrated coordinates at the source and image centers, in the detected
ligand enumeration, and the branch sign law at the source center give the four-slot sign relation
between the actual frame orders. -/
theorem slotVolume_sign_of_calibrated
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (frames : ContextFrameCompilation input target unit targetUnit)
    {imageUnit : DetectedOccurrence input.certified.moleculeGraph}
    {imageTargetUnit : input.certified.molecularFrameUnit
      (input.certified.transportOccurrence singleBonded e target).1 = imageUnit.1}
    (imageFrames : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target) imageUnit imageTargetUnit)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) (mirror : Bool)
    (signLaw : input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.physicalSourceCenter frames.center) *
        permHandedness (input.certified.detectedMultiCenterMolecule.ligandPermAt
          (input.certified.physicalDetectedAut e)
          (input.certified.physicalSourceCenter frames.center)) =
      physicalMirrorFactor mirror *
        input.certified.detectedMultiCenterMolecule.configurationSign cfg
          (input.certified.detectedMultiCenterMolecule.centerPerm
            (input.certified.physicalDetectedAut e)
            (input.certified.physicalSourceCenter frames.center)))
    (sourcePointAt imagePointAt : Fin 4 → CartesianPoint3)
    (sourceSign : rationalVolumeSign (slotVolume sourcePointAt) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center)
    (imageSign : rationalVolumeSign (slotVolume imagePointAt) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFrames.center) :
    rationalVolumeSign
        (slotVolume fun slot => imagePointAt (imageFrames.detectedLigandPermutation slot)) =
      physicalMirrorFactor mirror * permHandedness (slotTransport singleBonded e frames).slotPerm *
        rationalVolumeSign
          (slotVolume fun slot => sourcePointAt (frames.detectedLigandPermutation slot)) := by
  rw [volumeSign_reindex imagePointAt imageFrames.detectedLigandPermutation,
    volumeSign_reindex sourcePointAt frames.detectedLigandPermutation, sourceSign, imageSign]
  have imageConfig : input.certified.detectedMultiCenterMolecule.configurationSign cfg
        imageFrames.center =
      physicalMirrorFactor mirror *
        input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
        permHandedness (input.certified.framePerm e frames.center.1
          (input.certified.sourceTetra frames.center)) := by
    have turned := configurationSign_image_of_branchSign
      input.certified.detectedMultiCenterMolecule (input.certified.physicalDetectedAut e) cfg mirror
      (input.certified.physicalSourceCenter frames.center) signLaw
    rw [← input.certified.framePerm_eq_ligandPermAt e frames.center] at turned
    rw [image_center singleBonded e frames imageFrames]
    exact turned
  have ligands := image_detectedLigandPermutation_handedness singleBonded e frames imageFrames
  have squareFrame := permHandedness_mul_self (input.certified.framePerm e frames.center.1
    (input.certified.sourceTetra frames.center))
  have squareSlot := permHandedness_mul_self (slotTransport singleBonded e frames).slotPerm
  rw [imageConfig]
  calc
    physicalMirrorFactor mirror *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
          permHandedness (input.certified.framePerm e frames.center.1
            (input.certified.sourceTetra frames.center)) *
          permHandedness imageFrames.detectedLigandPermutation =
        physicalMirrorFactor mirror *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
          permHandedness (input.certified.framePerm e frames.center.1
            (input.certified.sourceTetra frames.center)) *
          ((permHandedness imageFrames.detectedLigandPermutation *
              permHandedness (slotTransport singleBonded e frames).slotPerm) *
            permHandedness (slotTransport singleBonded e frames).slotPerm) := by
      rw [mul_assoc (permHandedness imageFrames.detectedLigandPermutation), squareSlot, mul_one]
    _ = physicalMirrorFactor mirror *
          input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
          permHandedness (input.certified.framePerm e frames.center.1
            (input.certified.sourceTetra frames.center)) *
          ((permHandedness (input.certified.framePerm e frames.center.1
              (input.certified.sourceTetra frames.center)) *
              permHandedness frames.detectedLigandPermutation) *
            permHandedness (slotTransport singleBonded e frames).slotPerm) := by
      rw [ligands]
    _ = physicalMirrorFactor mirror * permHandedness (slotTransport singleBonded e frames).slotPerm *
          (input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
            permHandedness frames.detectedLigandPermutation) *
          (permHandedness (input.certified.framePerm e frames.center.1
              (input.certified.sourceTetra frames.center)) *
            permHandedness (input.certified.framePerm e frames.center.1
              (input.certified.sourceTetra frames.center))) := by ring
    _ = physicalMirrorFactor mirror * permHandedness (slotTransport singleBonded e frames).slotPerm *
          (input.certified.detectedMultiCenterMolecule.configurationSign cfg frames.center *
            permHandedness frames.detectedLigandPermutation) := by
      rw [squareFrame, mul_one]

end Sign

/-! ## One physical step at a calibrated occurrence -/

section Step

variable {input : Input}

/-- **The physical transport step.** At a real detected occurrence with actual compilations of it
and of its automorphic image at a common window, assume:

* the parent slot is reader-free constitutionally separated from the other three slots;
* every real read of the three outward canonical cuts is covariant (the induction hypothesis);
* actual coordinates at both frames, related by the four-slot volume-sign law.

Then the image state is the source state read through `retainedPhysicalLetter`. No label, order,
strictness, reference or reader correspondence is assumed. -/
theorem law_of_calibrated
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    {target : Occurrence input} {unit : DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation input target unit targetUnit)
    (imageFrames : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target)
      (input.certified.transportDetectedOccurrence e unit)
      (transportOccurrence_unit input singleBonded e target unit targetUnit))
    (sameW : imageFrames.W = frames.W) (sameD : imageFrames.D = frames.D)
    (parent : Fin 4)
    (separated : ∀ slot, slot ≠ parent →
      ConstitutionallySeparated (frames.frame.cursorAt parent) (frames.frame.cursorAt slot))
    (outward : ∀ slot, slot ≠ parent →
      ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
        (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
        (frames.canonicalCutGraphs singleBonded slot))
    (sourcePoints imagePoints : Fin 4 → CartesianPoint3)
    (sourceAvailable : ∀ slot, frames.actualCoordinates slot = some (sourcePoints slot))
    (imageAvailable : ∀ slot, imageFrames.actualCoordinates slot = some (imagePoints slot))
    (sign : rationalVolumeSign (slotVolume imagePoints) =
      physicalMirrorFactor mirror * permHandedness (slotTransport singleBonded e frames).slotPerm *
        rationalVolumeSign (slotVolume sourcePoints)) :
    Law singleBonded e mirror target := by
  set σ := (slotTransport singleBonded e frames).slotPerm with hσ
  have sourceActual : CompleteRootOutcome
      (fun slot => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded slot) frames.W frames.D)
      sourcePoints (referenceState input target) := by
    have outcome := frames.referenceState_canonicalCutOutcome singleBonded
    unfold retainedCutArmOutcome at outcome
    exact (retainedContextualOutcomeAt_iff_completeRootOutcome input.certified.moleculeGraph
      (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D
      sourceAvailable _).1 outcome
  have hybridSource : CompleteRootOutcome
      (fun slot => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (hybridMap input.certified.moleculeGraph e mirror (descriptorMap input)) unit
        (frames.canonicalCutGraphs singleBonded slot) frames.W frames.D)
      sourcePoints (referenceState input target) := by
    refine (completeRootOutcome_parent_congr
      (fun slot => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded slot) frames.W frames.D)
      (fun slot => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (hybridMap input.certified.moleculeGraph e mirror (descriptorMap input)) unit
        (frames.canonicalCutGraphs singleBonded slot) frames.W frames.D)
      parent ?_
      (constitutionalComponent_map_independent input.certified.moleculeGraph
        (frames.canonicalCutGraphs singleBonded parent)
        (hybridMap input.certified.moleculeGraph e mirror (descriptorMap input))
        (descriptorMap input) unit frames.W frames.D)
      ?_ sourcePoints _).2 sourceActual
    · intro slot ne
      exact cut_retainedCompleteLigandRule5KeyAt_congr input.certified.moleculeGraph
        (frames.canonicalLigandCut singleBonded slot).focus
        (some (frames.canonicalLigandCut singleBonded slot).incoming)
        (frames.canonicalLigandCut singleBonded slot).anchor
        (hybridMap input.certified.moleculeGraph e mirror (descriptorMap input))
        (descriptorMap input) unit
        (fun node steps occ real ancestors context =>
          hybridMap_of_covariant input.certified.moleculeGraph e mirror (descriptorMap input)
            (outward slot ne node steps occ real ancestors context))
        frames.W frames.D
    · intro slot ne
      exact constitutional_ne_of_separated singleBonded frames (descriptorMap input)
        (separated slot ne)
  have transported := (cuts_completeRootOutcome_transport input.certified.moleculeGraph e mirror σ
    (hybridMap input.certified.moleculeGraph e mirror (descriptorMap input)) (descriptorMap input)
    unit (fun slot => (frames.frame.cursorAt slot).occurrence.1.root)
    (fun slot => (frames.canonicalLigandCut singleBonded slot).focus)
    (fun slot => some (frames.canonicalLigandCut singleBonded slot).incoming)
    (fun slot => (frames.canonicalLigandCut singleBonded slot).anchor)
    (fun slot => readsAgree_hybridMap input.certified.moleculeGraph e mirror (descriptorMap input)
      unit _)
    sourcePoints imagePoints frames.W frames.D (referenceState input target) sign).2 hybridSource
  have imageKeys : (fun slot => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (descriptorMap input) (mapDetected input.certified.moleculeGraph e unit)
        (cutRetainedArm input.certified.moleculeGraph
          ((e : Equiv.Perm input.certified.Atom)
            (frames.frame.cursorAt (σ⁻¹ slot)).occurrence.1.root)
          (imageNode e (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).focus)
          ((some (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).incoming).map (imageNode e))
          (cutAnchor_image e (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).focus
            (some (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).incoming)
            (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).anchor)) frames.W frames.D) =
      retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
        (input.certified.transportDetectedOccurrence e unit)
        (imageFrames.canonicalCutGraphs singleBonded) imageFrames.W imageFrames.D := by
    funext slot
    have sent : input.certified.transportCursor singleBonded e (frames.frame.cursorAt (σ⁻¹ slot)) =
        imageFrames.frame.cursorAt slot := by
      rw [← image_cursorAt singleBonded e frames imageFrames (σ⁻¹ slot)]
      exact congrArg imageFrames.frame.cursorAt (Equiv.apply_symm_apply σ slot)
    rw [mapDetected_eq_transportDetectedOccurrence input.certified e unit, sameW, sameD]
    exact congrArg (fun graph => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
      (descriptorMap input) (input.certified.transportDetectedOccurrence e unit) graph
      frames.W frames.D) (image_canonicalCut_eq singleBonded e frames imageFrames sent)
  have transported' : CompleteRootOutcome
      (retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
        (input.certified.transportDetectedOccurrence e unit)
        (imageFrames.canonicalCutGraphs singleBonded) imageFrames.W imageFrames.D)
      imagePoints ((referenceState input target).map (retainedPhysicalLetter mirror)) := by
    rw [← imageKeys]
    exact transported
  have imageActual : CompleteRootOutcome
      (retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
        (input.certified.transportDetectedOccurrence e unit)
        (imageFrames.canonicalCutGraphs singleBonded) imageFrames.W imageFrames.D)
      imagePoints (referenceState input (input.certified.transportOccurrence singleBonded e target)) := by
    have outcome := imageFrames.referenceState_canonicalCutOutcome singleBonded
    unfold retainedCutArmOutcome at outcome
    exact (retainedContextualOutcomeAt_iff_completeRootOutcome input.certified.moleculeGraph
      (descriptorMap input) _ (imageFrames.canonicalCutGraphs singleBonded) imageFrames.W
      imageFrames.D imageAvailable _).1 outcome
  exact completeRootOutcome_unique imageActual transported'

end Step

/-! ## The induction over the actual dependency relation -/

section Induction

variable {input : Input} {rootTarget : Occurrence input}
  {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
  {rootTargetUnit : input.certified.molecularFrameUnit rootTarget.1 = rootUnit.1}

/-- **Induction step, from an arbitrary start cursor inside a tied root arm.** At an occurrence
reached from `start`, the law follows from the law at every reached strict dependency. The start
is reached from root slot `i`; the root arms `i` and `j` tie at Rule 1a; `e` fixes the root; the
physical sign law holds at every real center reached from `start`. -/
theorem law_step_general
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut e) rootFrames.center = rootFrames.center)
    (start : input.certified.LocalizedRerootCursor (carrierFuel input))
    (startReach : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) start)
    (signLaw : SignLawFrom e cfg mirror start)
    (target : Occurrence input) (reach : ReachFrom start target)
    (ih : ∀ z, input.certified.LocalizedDepthDependency z target → ReachFrom start z →
      Law singleBonded e mirror z) :
    Law singleBonded e mirror target := by
  obtain ⟨cursor, cursorEq, fromStart⟩ := reach
  have reachable := startReach.trans fromStart
  obtain ⟨⟨previous, previousEq, shorter⟩, inside, nonroot, rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  rw [cursorEq] at shorter inside nonroot rooted
  by_cases real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  swap
  · have source := referenceState_none_of_not_real input target real
    have image := referenceState_none_of_not_real input
      (input.certified.transportOccurrence singleBonded e target) (by
        rw [input.certified.transportOccurrence_provenance singleBonded e target]
        exact real)
    unfold Law
    rw [source, image]
    rfl
  by_cases detected : IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom
  swap
  · obtain ⟨source, image⟩ :=
      LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none input
        singleBonded e target real detected
    unfold Law
    rw [source, image]
    rfl
  let unit : DetectedOccurrence input.certified.moleculeGraph :=
    ⟨input.certified.molecularFrameUnit target.1, detected⟩
  let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have cursorReal : cursor.occurrence.1.node.provenance = .realAtom := by
    rw [cursorEq]
    exact real
  have signAtCenter := signLaw cursor fromStart cursorReal
    (input.certified.physicalSourceCenter frames.center) (by rw [cursorEq]; exact centerMeaning.2)
  have dNe : input.certified.physicalSourceCenter frames.center ≠ rootFrames.center := by
    intro same
    have atomNe := current_ne_root_of_nonroot input.certified target real nonroot centerMeaning.2
    apply atomNe
    rw [← rooted]
    exact congrArg Subtype.val same
  have rootFixedAtom : (e : Equiv.Perm input.certified.Atom) rootFrames.center.1 =
      rootFrames.center.1 :=
    (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff
      input.certified.detectedMultiCenterMolecule (input.certified.physicalDetectedAut e)
      rootFrames.center).mp rootFixed
  have imageNe : input.certified.physicalImageCenter e frames.center ≠ rootFrames.center := by
    intro same
    apply dNe
    apply (input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut e)).injective
    calc input.certified.detectedMultiCenterMolecule.centerPerm
          (input.certified.physicalDetectedAut e) (input.certified.physicalSourceCenter frames.center)
        = input.certified.physicalImageCenter e frames.center := rfl
      _ = rootFrames.center := same
      _ = input.certified.detectedMultiCenterMolecule.centerPerm
          (input.certified.physicalDetectedAut e) rootFrames.center := rootFixed.symm
  have imageUnitEq := transportOccurrence_unit input singleBonded e target unit rfl
  have imageReal := transportOccurrence_real input singleBonded e target real
  let imageFrames := cyclicContextFrameCompilation input singleBonded
    (input.certified.transportOccurrence singleBonded e target) imageReal
    (input.certified.transportDetectedOccurrence e unit) imageUnitEq
  by_cases twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule frames.center
  · have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root := by
      rw [← rooted]
      exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet rootFrames.center.1).mp
        rootFrames.center.2
    have sourceNone := twinState_none input singleBonded target real unit rfl rootTetrahedral twin
    have imageTwin : ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule imageFrames.center := by
      rw [image_center singleBonded e frames imageFrames]
      exact LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport
        (input.certified.physicalDetectedAut e) twin
    have imageRootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter
        (input.certified.transportOccurrence singleBonded e target).1.root := by
      rw [input.certified.transportOccurrence_root, ← rooted, rootFixedAtom, rooted]
      exact rootTetrahedral
    have imageNone := twinState_none input singleBonded
      (input.certified.transportOccurrence singleBonded e target) imageReal
      (input.certified.transportDetectedOccurrence e unit) imageUnitEq imageRootTetrahedral imageTwin
    unfold Law
    rw [sourceNone, imageNone]
    rfl
  have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule
      (input.certified.physicalImageCenter e frames.center) := fun imageTwin =>
    twin ((LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport_iff
      (input.certified.physicalDetectedAut e) (input.certified.physicalSourceCenter frames.center)).mp
      imageTwin)
  obtain ⟨sourcePointAt, sourceObserved, _sourceNonzero, sourceSign⟩ :=
    (domain.centerCase _ dNe).resolve_left twin
  obtain ⟨imagePointAt, imageObserved, _imageNonzero, imageSign⟩ :=
    (domain.centerCase _ imageNe).resolve_left imageNotTwin
  -- Common window.
  let framesW : ContextFrameCompilation input target unit rfl :=
    { frames with
      W := max frames.W imageFrames.W
      D := max frames.D imageFrames.D
      widthBound := fun k => (frames.widthBound k).trans (le_max_left _ _)
      depthBound := fun k => (frames.depthBound k).trans (le_max_left _ _) }
  let imageFramesW : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target)
      (input.certified.transportDetectedOccurrence e unit) imageUnitEq :=
    { imageFrames with
      W := max frames.W imageFrames.W
      D := max frames.D imageFrames.D
      widthBound := fun k => (imageFrames.widthBound k).trans (le_max_right _ _)
      depthBound := fun k => (imageFrames.depthBound k).trans (le_max_right _ _) }
  -- Parent separation inside the tied root arm.
  have realI := (rootFrame_cursor_facts singleBonded rootFrames rootAddress rootReal i).1
  have realJ := (rootFrame_cursor_facts singleBonded rootFrames rootAddress rootReal j).1
  have armDistinct : (rootFrames.frame.cursorAt i).occurrence ≠
      (rootFrames.frame.cursorAt j).occurrence := by
    intro same
    have currents := congrArg
      (fun occurrence : Occurrence input => occurrence.1.node.current?) same
    simp only at currents
    rw [rootFrames.ligandAt i, rootFrames.ligandAt j] at currents
    exact distinct (rootFrames.detectedLigandPermutation.injective
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective rootFrames.center
        (Option.some.inj currents)))
  have oldI := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input rootTarget) _ _).symm.trans (rootFrames.stages i).a.built
  have oldJ := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input rootTarget) _ _).symm.trans (rootFrames.stages j).a.built
  obtain ⟨parent, _parentClass, others⟩ :=
    parentSlot_separated_of_rootArmRule1aTie input.certified singleBonded
      { occurrence := rootTarget, previous? := none } rootAddress
      (rootFrames.frame.cursorAt i) (rootFrames.frame.cursorAt j) (rootFrames.childAt i)
      (rootFrames.childAt j) armDistinct realI realJ (contextOccurrenceRead input rootTarget)
      (contextOccurrenceRead input rootTarget) (rootFrames.stages i).a.key
      (rootFrames.stages j).a.key oldI oldJ tie target real inside framesW.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed framesW) nonroot
  -- Outward reads are covariant, by the induction hypothesis.
  have outwardReads : ∀ slot, slot ≠ parent →
      ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
        (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
        (framesW.canonicalCutGraphs singleBonded slot) := by
    intro slot ne
    have outSlot := (others slot ne).1
    have deeperSlot : target.1.address.length <
        (framesW.frame.cursorAt slot).occurrence.1.address.length := by
      obtain ⟨k, addressEq⟩ := outSlot
      rw [addressEq]
      simp
    have step : CertifiedLocalizedCIPInput.E input.certified cursor
        (framesW.frame.cursorAt slot) :=
      frame_outward_mem_children singleBonded framesW cursor cursorEq previous previousEq
        shorter outSlot
    have armReads : ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
        (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
        (framesW.actualArmGraphs slot) := by
      intro node steps occ _nodeReal ancestors context
      obtain ⟨source, sourceReach, sourceUnit⟩ :=
        actualArm_read_source singleBonded framesW slot node steps occ ancestors context
      have dependency := (input.certified.outward_reachable_dependency target
        (framesW.frame.cursorAt slot) source (framesW.childAt slot) deeperSlot sourceReach).1
      have sourceRoot : ReachFrom start source.occurrence :=
        ⟨source, rfl, (fromStart.tail step).trans sourceReach⟩
      exact covariant_of_law singleBonded e mirror source.occurrence occ sourceUnit
        (ih source.occurrence dependency sourceRoot)
    let iso : RootedDigraph.Iso (framesW.canonicalCutGraphs singleBonded slot)
        (framesW.actualArmGraphs slot) :=
      Classical.choice (framesW.canonicalLigandCut singleBonded slot).faithful
    exact readsAgree_of_iso e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit iso.symm armReads
  -- Coordinates and the sign law.
  have sourceAvailable : ∀ slot, framesW.actualCoordinates slot =
      some (sourcePointAt (framesW.detectedLigandPermutation slot)) := fun slot =>
    sourceObserved _
  have imageCenterEq := image_center singleBonded e framesW imageFramesW
  have imageAvailable : ∀ slot, imageFramesW.actualCoordinates slot =
      some (imagePointAt (imageFramesW.detectedLigandPermutation slot)) := by
    intro slot
    show input.certified.spatialPointAt?
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt imageFramesW.center
        (imageFramesW.detectedLigandPermutation slot)) = _
    rw [imageCenterEq]
    exact imageObserved _
  have imageSign' : rationalVolumeSign (slotVolume imagePointAt) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFramesW.center := by
    rw [imageCenterEq]
    exact imageSign
  have sign := slotVolume_sign_of_calibrated singleBonded e framesW imageFramesW cfg mirror
    signAtCenter sourcePointAt imagePointAt sourceSign imageSign'
  exact law_of_calibrated singleBonded e mirror framesW imageFramesW rfl rfl parent
    (fun slot ne => (others slot ne).2) outwardReads _ _ sourceAvailable imageAvailable sign

/-- **Recursive physical transport from an arbitrary start inside a tied root arm.** Every
occurrence reached from `start` satisfies the law. -/
theorem law_of_reachFrom
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (rootFixed : input.certified.detectedMultiCenterMolecule.centerPerm
      (input.certified.physicalDetectedAut e) rootFrames.center = rootFrames.center)
    (start : input.certified.LocalizedRerootCursor (carrierFuel input))
    (startReach : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) start)
    (signLaw : SignLawFrom e cfg mirror start)
    (target : Occurrence input) (reach : ReachFrom start target) :
    Law singleBonded e mirror target := by
  have main : ∀ z, ReachFrom start z → Law singleBonded e mirror z := by
    intro z
    refine @WellFounded.induction _ _
      (input.certified.localizedDepthDependency_wellFounded (carrierFuel input))
      (fun z => ReachFrom start z → Law singleBonded e mirror z) z ?_
    intro z ih reachZ
    exact law_step_general singleBonded rootFrames rootAddress rootReal distinct tie cfg domain
      e mirror rootFixed start startReach signLaw z reachZ
      (fun w dependency reachW => ih w dependency reachW)
  exact main target reach

/-- The actual Rule-1a tie of two root arms related by an automorphism. -/
theorem rootArms_rule1aTie
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4}
    (sent : input.certified.transportCursor singleBonded e (rootFrames.frame.cursorAt i) =
      rootFrames.frame.cursorAt j) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq := by
  have builtAtTransport : input.certified.buildRuleMajorCumulativeWithRead? .rule4a
      (contextOccurrenceRead input rootTarget) (2 * (carrierFuel input + 1))
      (input.certified.transportCursor singleBonded e (rootFrames.frame.cursorAt i)) =
      some (rootFrames.stages j).a.key := by
    rw [sent]
    exact (rootFrames.stages j).a.built
  exact rule1aTie_of_ruleMajorBuild_observable_transport singleBonded
    (frames_cursor_aligned rootFrames i) (rootFrames.stages i).a.built builtAtTransport

/-- **Recursive physical transport of actual auxiliary states.** Every occurrence reached from the
transported root slot satisfies the law. -/
theorem law_of_reach
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg rootFrames.center)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4} (distinct : i ≠ j) (mirror : Bool)
    (transport : input.certified.DetectedBranchTransport e cfg rootFrames.center
      (rootFrames.detectedLigandPermutation i) (rootFrames.detectedLigandPermutation j) mirror)
    (target : Occurrence input) (reach : Reach rootFrames i target) :
    Law singleBonded e mirror target := by
  have tie := rootArms_rule1aTie singleBonded rootFrames e
    (rootSlot_transport singleBonded rootFrames rootAddress rootReal e transport)
  have signLaw : SignLawFrom e cfg mirror (rootFrames.frame.cursorAt i) :=
    fun cursor reachable real d current =>
      transport.signLaw d (reach_ligandBranchReaches singleBonded rootFrames rootAddress rootReal
        i cursor reachable real d.1 current)
  exact law_of_reachFrom singleBonded rootFrames rootAddress rootReal distinct tie cfg domain e
    mirror transport.rootFixed (rootFrames.frame.cursorAt i) Relation.ReflTransGen.refl signLaw
    target reach

end Induction

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.covariant_of_law
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.retainedContextualOutcomeAt_iff_completeRootOutcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.image_canonicalCut_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.stage_constitutional_compare
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.constitutional_ne_of_separated
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.actualArm_read_source
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.frame_outward_mem_children
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.reach_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.reach_ligandBranchReaches
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.twinState_none
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.slotVolume_sign_of_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.law_of_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.cursor_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.law_step_general
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.law_of_reachFrom
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.rootArms_rule1aTie
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport.law_of_reach
