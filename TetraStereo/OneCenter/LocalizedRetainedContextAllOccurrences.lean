import TetraStereo.OneCenter.DeclarativeCIPRetainedCutArm
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.OneCenter.LocalizedRetainedContextGeneratedDescriptor
import TetraStereo.OneCenter.LocalizedRetainedRealArmExpansion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! Every carrier occurrence of a finite simple-bonded molecule, and every final-report center.

A non-real occurrence, including a terminal ring duplicate, has reference state `none`. A real
occurrence whose frame atom is not a detected center has reference state `none`. A real detected
occurrence keeps its stored root and address. Its reference state is the independent retained
judgment on the predecessor cuts of its four compiled ligand arms.

Each cut is `cutRetainedArm` at the target's outer root. Its focus is
`occurrenceCarrierNode` of that ligand cursor and its incoming node is `occurrenceCarrierNode`
of the target, whether the predecessor lies inward or outward. `previous?` stays `some` of the
target. The correspondence is
`executableChild_retainedContextArmFaithful_of_carrierFuel` at stage `a` of the compiled frame.
The retained keys are the independent chemical keys of the molecule and `descriptorMap` on those
cuts. Any other rooted graphs isomorphic to the cuts, or to the actual stage graphs, have the
same outcome.

A final-report center is that statement at `localizedFinalOccurrenceExecutable`, whose root is
the center and whose address is empty. Auxiliary targets are not moved onto that root.

No acyclicity, fixed molecule size, depth bound, all-real hypothesis, unique-nearest selection,
or chosen key, reference, reader, order, strictness, isomorphism, or letter is assumed. The
window is the compiled frame's `W` and `D`. Unresolved full-key ties and missing coordinates
remain refusals. A returned lowercase letter means `completeRule5PairCount = 1` on the retained
cut keys. The raw `R` or `S` reading is the geometric class of the descending cut-key order.
That pair count is not a physical enantiomorphic-pair relation. This is the generated rule-major
profile, including its proposed real-node extension. It is not a Rule 6 or full IUPAC claim.
-/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
noncomputable section
open scoped Classical

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom]

/-- The four predecessor-cut arms named by one focus, incoming neighbor, and cut anchor per slot.
`incoming` may be an inward or outward reroot-child. This is not `retainedArm`. -/
def retainedCutArmGraphs (molecule : MoleculeGraph Atom) (root : Fin 4 → Atom)
    (focus : ∀ slot, RetainedOccurrenceCarrier.Nodes molecule (root slot))
    (incoming : ∀ slot, Option (RetainedOccurrenceCarrier.Nodes molecule (root slot)))
    (anchor : ∀ slot, CutAnchor (focus slot) (incoming slot)) :
    Fin 4 → RootedDigraph Atom :=
  fun slot => cutRetainedArm molecule (root slot) (focus slot) (incoming slot) (anchor slot)

/-- Independent retained outcome on those cut arms. Inhabitation for the actual ligand cursors
is the cut-bridge obligation; this definition does not supply it. -/
def retainedCutArmOutcome (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (root : Fin 4 → Atom)
    (focus : ∀ slot, RetainedOccurrenceCarrier.Nodes molecule (root slot))
    (incoming : ∀ slot, Option (RetainedOccurrenceCarrier.Nodes molecule (root slot)))
    (anchor : ∀ slot, CutAnchor (focus slot) (incoming slot))
    (W D : Nat) (coordinates : Fin 4 → Option CartesianPoint3)
    (state : Option LocalizedAuxiliaryLabel) : Prop :=
  RetainedContextualOutcomeAt molecule descriptorMap unit
    (retainedCutArmGraphs molecule root focus incoming anchor) W D coordinates state

/-- Each graph is isomorphic to the predecessor cut of the same slot. -/
def actualArmsCutFaithful (molecule : MoleculeGraph Atom) (root : Fin 4 → Atom)
    (focus : ∀ slot, RetainedOccurrenceCarrier.Nodes molecule (root slot))
    (incoming : ∀ slot, Option (RetainedOccurrenceCarrier.Nodes molecule (root slot)))
    (anchor : ∀ slot, CutAnchor (focus slot) (incoming slot))
    (graphs : Fin 4 → RootedDigraph Atom) : Prop :=
  ∀ slot, RetainedContextArmFaithful molecule (root slot) (focus slot) (incoming slot)
    (anchor slot) (graphs slot)

variable {input : Input}

/-- Under `SimpleBonded`, a carrier occurrence is non-real exactly when it is a terminal ring
duplicate. -/
theorem carrierOccurrence_nonreal_iff_ringDuplicate
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input) :
    target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom ↔
      ∃ distance, target.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance := by
  constructor
  · intro notReal
    rcases input.certified.carrierOccurrence_provenance_simple_or_ring singleBonded target with
      real | ring
    · exact absurd real notReal
    · exact ring
  · intro ⟨_distance, ring⟩ real
    rw [ring] at real
    cases real

/-- A real carrier occurrence that is not a detected center has no descriptor.
The current atom is the frame atom of its simple path. -/
theorem referenceState_none_of_real_not_detected
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (notDetected : ¬ IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom) :
    referenceState input target = none := by
  have path := input.certified.simpleOccurrencePath_of_carrier_real singleBonded target real
  obtain ⟨current, _walk, currentObserved, head, _provenance, _isPath, _support, _parent⟩ :=
    input.certified.simpleOccurrencePath_realPathNode path
  have last := input.certified.realPathNode_history_getLast
    (input.certified.simpleOccurrencePath_realPathNode path)
  have frameAtom : (input.certified.molecularFrameUnit target.1).atom = current :=
    input.certified.molecularFrameUnit_atom_eq_current target.1 head last
  have notCenter : current ∉ input.certified.tetrahedralCenterSet := by
    intro present
    apply notDetected
    rw [frameAtom]
    exact (input.certified.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card current).mp
      ((input.certified.moleculeGraph.mem_tetrahedralCenterSet current).mp present)
  rw [← reference_fixed input target]
  exact input.certified.ruleMajorDescriptor?_eq_none_of_no_center target
    (input.certified.localizedDependencyView (referenceState input) target)
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
      target current currentObserved notCenter)

/-- A terminal ring duplicate is refused, whether or not its current atom is a detected center.
Recognition never demands a frame for it. -/
theorem referenceState_none_of_ringDuplicate
    (target : Occurrence input) {distance : Nat}
    (ring : target.1.node.provenance = OfficialCIPNodeProvenance.ringDuplicate distance) :
    referenceState input target = none := by
  apply referenceState_none_of_not_real input target
  rw [ring]
  intro bad
  cases bad

namespace ContextFrameCompilation

variable {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (frames : ContextFrameCompilation input target unit targetUnit)

/-- The compiled ligand cursors still name the stored target as their predecessor.
The actual bridge must preserve this; this module does not rewrite `previous?` to `none`. -/
def ligandCursorKeepsPredecessor : Prop :=
  ∀ slot, (frames.frame.cursorAt slot).previous? = some target

/-- Any rooted graphs isomorphic to the actual stage graphs have the same retained outcome.
The isomorphism is a parameter. It is not a cut-faithfulness proof. -/
theorem referenceState_retainedOutcome_of_armIso
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (isos : ∀ slot, RootedDigraph.Iso (frames.actualArmGraphs slot) (other slot)) :
    RetainedContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      other frames.W frames.D frames.actualCoordinates (referenceState input target) :=
  (retainedContextualOutcomeAt_iso input.certified.moleculeGraph (descriptorMap input) unit
    frames.actualArmGraphs other isos frames.W frames.D frames.actualCoordinates
    (referenceState input target)).2 (frames.referenceState_retainedOutcome singleBonded)

theorem referenceState_some_iff_retainedJudgment_of_armIso
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (isos : ∀ slot, RootedDigraph.Iso (frames.actualArmGraphs slot) (other slot))
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input target = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        unit other frames.W frames.D frames.actualCoordinates descriptor := by
  rw [frames.referenceState_some_iff_retainedJudgment singleBonded descriptor]
  exact (retainedContextualDescriptorJudgmentAt_iso input.certified.moleculeGraph
    (descriptorMap input) unit frames.actualArmGraphs other isos frames.W frames.D
    frames.actualCoordinates descriptor).symm

theorem referenceState_none_iff_no_retainedJudgment_of_armIso
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (isos : ∀ slot, RootedDigraph.Iso (frames.actualArmGraphs slot) (other slot)) :
    referenceState input target = none ↔
      ¬ ∃ descriptor,
        RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
          unit other frames.W frames.D frames.actualCoordinates descriptor := by
  rw [frames.referenceState_none_iff_no_retainedJudgment singleBonded]
  constructor
  · intro noActual ⟨descriptor, judgmentOther⟩
    exact noActual ⟨descriptor, (retainedContextualDescriptorJudgmentAt_iso
      input.certified.moleculeGraph (descriptorMap input) unit frames.actualArmGraphs other isos
      frames.W frames.D frames.actualCoordinates descriptor).1 judgmentOther⟩
  · intro noOther ⟨descriptor, judgmentActual⟩
    exact noOther ⟨descriptor, (retainedContextualDescriptorJudgmentAt_iso
      input.certified.moleculeGraph (descriptorMap input) unit frames.actualArmGraphs other isos
      frames.W frames.D frames.actualCoordinates descriptor).2 judgmentActual⟩

/-- Transport along a supplied predecessor-cut correspondence.
The canonical family below discharges this hypothesis for the compiled frame. The same
statement still transports any other family, including an alternative that is faithful to the
same cuts. -/
theorem referenceState_retainedCutOutcome_of_bridge
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (root : Fin 4 → input.certified.Atom)
    (focus : ∀ slot, RetainedOccurrenceCarrier.Nodes input.certified.moleculeGraph (root slot))
    (incoming : ∀ slot, Option (RetainedOccurrenceCarrier.Nodes input.certified.moleculeGraph (root slot)))
    (anchor : ∀ slot, CutAnchor (focus slot) (incoming slot))
    (faithful : actualArmsCutFaithful input.certified.moleculeGraph root focus incoming anchor
      frames.actualArmGraphs) :
    retainedCutArmOutcome input.certified.moleculeGraph (descriptorMap input) unit root focus
      incoming anchor frames.W frames.D frames.actualCoordinates (referenceState input target) := by
  unfold retainedCutArmOutcome
  exact frames.referenceState_retainedOutcome_of_armIso singleBonded
    (retainedCutArmGraphs input.certified.moleculeGraph root focus incoming anchor)
    (fun slot => (Classical.choice (faithful slot)).symm)

/-- The frame's parent cursor. Its occurrence is the stored target, so a child whose
`previous?` is this occurrence still carries the auxiliary outer context. -/
def actualTargetCursor :
    input.certified.LocalizedRerootCursor (carrierFuel input) :=
  { occurrence := target, previous? := none }

theorem ligandCursor_outerRoot (slot : Fin 4) :
    (frames.frame.cursorAt slot).occurrence.1.root = target.1.root :=
  input.certified.localizedRerootChildren_root_eq actualTargetCursor
    (frames.frame.cursorAt slot)
    (input.certified.executableLocalizedRerootChildren actualTargetCursor)
    (input.certified.executableLocalizedRerootChildren_declarative actualTargetCursor)
    (frames.childAt slot)

/-- The actual stage-`a` arm of one compiled ligand slot, with the carrier identities
returned by the real-arm bridge. -/
theorem ligandCutBridge
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (slot : Fin 4) :
    (frames.frame.cursorAt slot).previous? = some target ∧
    ∃ (focus : RetainedOccurrenceCarrier.Nodes input.certified.moleculeGraph
        (frames.frame.cursorAt slot).occurrence.1.root)
      (incoming : RetainedOccurrenceCarrier.Nodes input.certified.moleculeGraph
        (frames.frame.cursorAt slot).occurrence.1.root)
      (anchor : CutAnchor focus (some incoming)),
      focus.1 = input.certified.occurrenceCarrierNode singleBonded
          (frames.frame.cursorAt slot).occurrence ∧
        incoming.1 = input.certified.occurrenceCarrierNode singleBonded target ∧
        RetainedContextArmFaithful input.certified.moleculeGraph
          (frames.frame.cursorAt slot).occurrence.1.root focus (some incoming) anchor
          (frames.actualArmGraphs slot) := by
  obtain ⟨previousEq, focus, incoming, anchor, focusEq, incomingEq, faithful⟩ :=
    input.certified.executableChild_retainedContextArmFaithful_of_carrierFuel singleBonded
      actualTargetCursor (frames.frame.cursorAt slot) (frames.childAt slot)
      (frames.stages slot).a
  refine ⟨previousEq, focus, incoming, anchor, focusEq, incomingEq, ?_⟩
  simpa [actualArmGraphs] using faithful

/-- One ligand's predecessor cut: focus and incoming are the carrier nodes of the actual
child and the actual target, and the stage graph is faithful to that cut. -/
structure CanonicalLigandCut
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (slot : Fin 4) where
  focus : RetainedOccurrenceCarrier.Nodes input.certified.moleculeGraph
    (frames.frame.cursorAt slot).occurrence.1.root
  incoming : RetainedOccurrenceCarrier.Nodes input.certified.moleculeGraph
    (frames.frame.cursorAt slot).occurrence.1.root
  anchor : CutAnchor focus (some incoming)
  focusCarrier : focus.1 = input.certified.occurrenceCarrierNode singleBonded
    (frames.frame.cursorAt slot).occurrence
  incomingCarrier : incoming.1 = input.certified.occurrenceCarrierNode singleBonded target
  faithful : RetainedContextArmFaithful input.certified.moleculeGraph
    (frames.frame.cursorAt slot).occurrence.1.root focus (some incoming) anchor
    (frames.actualArmGraphs slot)

theorem canonicalLigandCut_nonempty
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (slot : Fin 4) :
    Nonempty (frames.CanonicalLigandCut singleBonded slot) := by
  obtain ⟨_previousEq, focus, incoming, anchor, focusEq, incomingEq, faithful⟩ :=
    frames.ligandCutBridge singleBonded slot
  exact ⟨⟨focus, incoming, anchor, focusEq, incomingEq, faithful⟩⟩

def canonicalLigandCut
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (slot : Fin 4) :
    frames.CanonicalLigandCut singleBonded slot :=
  Classical.choice (frames.canonicalLigandCut_nonempty singleBonded slot)

theorem ligandCursor_previous
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (slot : Fin 4) :
    (frames.frame.cursorAt slot).previous? = some target :=
  (frames.ligandCutBridge singleBonded slot).1

theorem ligandCursorKeepsPredecessor_holds
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    frames.ligandCursorKeepsPredecessor :=
  frames.ligandCursor_previous singleBonded

/-- The four `cutRetainedArm` graphs named by the compiled cursors. -/
def canonicalCutGraphs
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    Fin 4 → RootedDigraph input.certified.Atom :=
  fun slot =>
    let cut := frames.canonicalLigandCut singleBonded slot
    cutRetainedArm input.certified.moleculeGraph
      (frames.frame.cursorAt slot).occurrence.1.root cut.focus (some cut.incoming) cut.anchor

theorem canonicalArmsCutFaithful
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    actualArmsCutFaithful input.certified.moleculeGraph
      (fun slot => (frames.frame.cursorAt slot).occurrence.1.root)
      (fun slot => (frames.canonicalLigandCut singleBonded slot).focus)
      (fun slot => some (frames.canonicalLigandCut singleBonded slot).incoming)
      (fun slot => (frames.canonicalLigandCut singleBonded slot).anchor)
      frames.actualArmGraphs :=
  fun slot => (frames.canonicalLigandCut singleBonded slot).faithful

theorem referenceState_canonicalCutOutcome
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    retainedCutArmOutcome input.certified.moleculeGraph (descriptorMap input) unit
      (fun slot => (frames.frame.cursorAt slot).occurrence.1.root)
      (fun slot => (frames.canonicalLigandCut singleBonded slot).focus)
      (fun slot => some (frames.canonicalLigandCut singleBonded slot).incoming)
      (fun slot => (frames.canonicalLigandCut singleBonded slot).anchor)
      frames.W frames.D frames.actualCoordinates (referenceState input target) :=
  frames.referenceState_retainedCutOutcome_of_bridge singleBonded
    (fun slot => (frames.frame.cursorAt slot).occurrence.1.root)
    (fun slot => (frames.canonicalLigandCut singleBonded slot).focus)
    (fun slot => some (frames.canonicalLigandCut singleBonded slot).incoming)
    (fun slot => (frames.canonicalLigandCut singleBonded slot).anchor)
    (frames.canonicalArmsCutFaithful singleBonded)

theorem referenceState_some_iff_canonicalCutJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input target = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D frames.actualCoordinates
        descriptor :=
  frames.referenceState_some_iff_retainedJudgment_of_armIso singleBonded
    (frames.canonicalCutGraphs singleBonded)
    (fun slot => (Classical.choice
      (frames.canonicalLigandCut singleBonded slot).faithful).symm) descriptor

theorem referenceState_none_iff_no_canonicalCutJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    referenceState input target = none ↔
      ¬ ∃ descriptor,
        RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
          unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D
          frames.actualCoordinates descriptor :=
  frames.referenceState_none_iff_no_retainedJudgment_of_armIso singleBonded
    (frames.canonicalCutGraphs singleBonded)
    (fun slot => (Classical.choice
      (frames.canonicalLigandCut singleBonded slot).faithful).symm)

/-- A graph family isomorphic to the derived cuts has the same retained outcome. The canonical
family itself is derived; this isomorphism is only the step to another representation. -/
theorem referenceState_retainedOutcome_of_canonicalCutIso
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (isos : ∀ slot, RootedDigraph.Iso (frames.canonicalCutGraphs singleBonded slot) (other slot)) :
    RetainedContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      other frames.W frames.D frames.actualCoordinates (referenceState input target) :=
  frames.referenceState_retainedOutcome_of_armIso singleBonded other fun slot =>
    ((Classical.choice (frames.canonicalLigandCut singleBonded slot).faithful).symm).trans
      (isos slot)

theorem referenceState_lowercase_iff_canonicalCut
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    descriptor.IsLowercase ↔
      completeRule5PairCount (retainedContextualFrameKeysAt input.certified.moleculeGraph
        (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D) =
        1 :=
  retainedContextualDescriptorJudgmentAt_lowercase_iff
    ((frames.referenceState_some_iff_canonicalCutJudgment singleBonded descriptor).1 returned)

/-- An assigned letter is the geometric reading of the descending retained-cut key order.
`R` and `S` are that raw orientation. `r` and `s` are the same reading after the retained
prior-pair count. -/
theorem referenceState_eq_canonicalCut_geometric_reading
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    ∃ (points : Fin 4 → CartesianPoint3) (order : List (Fin 4)) (raw : RS),
      (∀ slot, frames.actualCoordinates slot = some (points slot)) ∧
      order.Perm (List.finRange 4) ∧
      order.Pairwise (fun left right =>
        retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
          (frames.canonicalCutGraphs singleBonded) frames.W frames.D right <
        retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
          (frames.canonicalCutGraphs singleBonded) frames.W frames.D left) ∧
      RationalTetrahedralDescriptor (order.map points) raw ∧
      descriptor = classifyTetrahedralRSPseudo raw (completeRule5PairCount
        (retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
          (frames.canonicalCutGraphs singleBonded) frames.W frames.D)) := by
  have judgment :=
    (frames.referenceState_some_iff_canonicalCutJudgment singleBonded descriptor).1 returned
  obtain ⟨points, available, complete⟩ := judgment
  obtain ⟨order, raw, permutation, sorted, rational, descriptorEq⟩ := complete
  exact ⟨points, order, raw, available, permutation, sorted, rational, descriptorEq⟩

end ContextFrameCompilation

/-- Actual-graph form of the occurrence classification. The cut-arm endpoint is
`all_carrier_occurrences_retained_on_cut_arms`. -/
theorem all_carrier_occurrences_retained_on_actual_graphs
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    ∀ target : Occurrence input,
      (target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom →
        referenceState input target = none) ∧
      (∀ _real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom,
        ¬ IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit target.1).atom →
          referenceState input target = none) ∧
      (∀ (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
        (detected : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit target.1).atom),
        let unit : DetectedOccurrence input.certified.moleculeGraph :=
          ⟨input.certified.molecularFrameUnit target.1, detected⟩
        let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
        RetainedContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
          frames.actualArmGraphs frames.W frames.D frames.actualCoordinates
          (referenceState input target)) := by
  intro target
  refine ⟨referenceState_none_of_not_real input target, ?_, ?_⟩
  · intro real notDetected
    exact referenceState_none_of_real_not_detected singleBonded target real notDetected
  · intro real detected
    exact referenceState_retainedOutcome_of_real input singleBonded target real
      ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl

/-- Every carrier occurrence on the derived predecessor cuts. Non-real occurrences, including
terminal rings, and real non-centers are `none`. A real detected occurrence keeps its stored
root and address. Its reference state agrees with the independent retained judgment on the
cuts named by the actual ligand and target carrier nodes. -/
theorem all_carrier_occurrences_retained_on_cut_arms
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    ∀ target : Occurrence input,
      (target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom →
        referenceState input target = none) ∧
      (∀ _real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom,
        ¬ IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit target.1).atom →
          referenceState input target = none) ∧
      (∀ (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
        (detected : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit target.1).atom),
        let unit : DetectedOccurrence input.certified.moleculeGraph :=
          ⟨input.certified.molecularFrameUnit target.1, detected⟩
        let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
        (∀ slot, (frames.frame.cursorAt slot).occurrence.1.root = target.1.root) ∧
        (∀ slot, (frames.frame.cursorAt slot).previous? = some target) ∧
        (∀ slot,
          (frames.canonicalLigandCut singleBonded slot).focus.1 =
            input.certified.occurrenceCarrierNode singleBonded
              (frames.frame.cursorAt slot).occurrence ∧
          (frames.canonicalLigandCut singleBonded slot).incoming.1 =
            input.certified.occurrenceCarrierNode singleBonded target) ∧
        (∀ descriptor, referenceState input target = some descriptor ↔
          RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph
            (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D
            frames.actualCoordinates descriptor) ∧
        (referenceState input target = none ↔
          ¬ ∃ descriptor, RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph
            (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D
            frames.actualCoordinates descriptor)) := by
  intro target
  refine ⟨referenceState_none_of_not_real input target, ?_, ?_⟩
  · intro real notDetected
    exact referenceState_none_of_real_not_detected singleBonded target real notDetected
  · intro real detected
    let frames := cyclicContextFrameCompilation input singleBonded target real
      ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl
    exact ⟨frames.ligandCursor_outerRoot, frames.ligandCursor_previous singleBonded,
      fun slot => ⟨(frames.canonicalLigandCut singleBonded slot).focusCarrier,
        (frames.canonicalLigandCut singleBonded slot).incomingCarrier⟩,
      fun descriptor => frames.referenceState_some_iff_canonicalCutJudgment singleBonded descriptor,
      frames.referenceState_none_iff_no_canonicalCutJudgment singleBonded⟩

/-- A returned lowercase letter on a real detected occurrence is one retained prior pair of
the derived cut keys. -/
theorem detected_referenceState_lowercase_iff_canonicalCut
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    descriptor.IsLowercase ↔ completeRule5PairCount (retainedContextualFrameKeysAt
      input.certified.moleculeGraph (descriptorMap input) unit
      (frames.canonicalCutGraphs singleBonded) frames.W frames.D) = 1 :=
  (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).referenceState_lowercase_iff_canonicalCut singleBonded returned

theorem detected_referenceState_eq_canonicalCut_geometric_reading
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    ∃ (points : Fin 4 → CartesianPoint3) (order : List (Fin 4)) (raw : RS),
      (∀ slot, frames.actualCoordinates slot = some (points slot)) ∧
      order.Perm (List.finRange 4) ∧
      order.Pairwise (fun left right =>
        retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
          (frames.canonicalCutGraphs singleBonded) frames.W frames.D right <
        retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
          (frames.canonicalCutGraphs singleBonded) frames.W frames.D left) ∧
      RationalTetrahedralDescriptor (order.map points) raw ∧
      descriptor = classifyTetrahedralRSPseudo raw (completeRule5PairCount
        (retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
          (frames.canonicalCutGraphs singleBonded) frames.W frames.D)) :=
  (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).referenceState_eq_canonicalCut_geometric_reading singleBonded returned

/-- A returned lowercase letter is one retained prior pair. It is not a graph-enantiomorphism
claim, and an unresolved full-key tie is a refusal rather than a letter. -/
theorem detected_referenceState_lowercase_iff
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    descriptor.IsLowercase ↔ completeRule5PairCount frames.retainedKeys = 1 :=
  referenceState_lowercase_iff_of_real input singleBonded target real unit targetUnit returned

/-- The report entry of one center is the retained outcome at that center's own final root.
The address is empty. This is not an auxiliary occurrence of some outer digraph. -/
theorem analyze_center_retainedOutcome
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter) :
    let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
    let unit := finalCenterUnit input center
    let frames := cyclicContextFrameCompilation input singleBonded target
      (finalOccurrence_provenance_real input center) unit
      (finalOccurrence_molecularFrameUnit input center)
    target.1.root = center.val ∧
    target.1.address = [] ∧
    RetainedContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      frames.actualArmGraphs frames.W frames.D frames.actualCoordinates
      (referenceState input target) := by
  refine ⟨?_, ?_, ?_⟩
  · exact input.certified.localizedFinalOccurrenceExecutable_root (carrierFuel input) center
  · exact input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center
  · exact referenceState_retainedOutcome_of_real input singleBonded
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (finalOccurrence_provenance_real input center)
      (finalCenterUnit input center)
      (finalOccurrence_molecularFrameUnit input center)

/-- The report state of one center is the retained cut judgment at that center's own final
root. The address is empty. -/
theorem analyze_center_retainedCutOutcome
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter) :
    let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
    let unit := finalCenterUnit input center
    let frames := cyclicContextFrameCompilation input singleBonded target
      (finalOccurrence_provenance_real input center) unit
      (finalOccurrence_molecularFrameUnit input center)
    target.1.root = center.val ∧
    target.1.address = [] ∧
    (∀ descriptor, referenceState input target = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D frames.actualCoordinates
        descriptor) ∧
    (referenceState input target = none ↔
      ¬ ∃ descriptor, RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph
        (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D
        frames.actualCoordinates descriptor) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact input.certified.localizedFinalOccurrenceExecutable_root (carrierFuel input) center
  · exact input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center
  · intro descriptor
    exact (cyclicContextFrameCompilation input singleBonded
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (finalOccurrence_provenance_real input center) (finalCenterUnit input center)
      (finalOccurrence_molecularFrameUnit input center)).referenceState_some_iff_canonicalCutJudgment
        singleBonded descriptor
  · exact (cyclicContextFrameCompilation input singleBonded
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (finalOccurrence_provenance_real input center) (finalCenterUnit input center)
      (finalOccurrence_molecularFrameUnit input center)).referenceState_none_iff_no_canonicalCutJudgment
        singleBonded

/-- `analyze` reads each center at that same own-root occurrence. -/
theorem analyze_reads_own_final_root (input : Input) :
    (analyze input = input.certified.canonicalTetrahedralCenters.map fun center =>
      (center.val.val, referenceState input
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))) ∧
    ∀ center, (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center).1.root =
      center.val :=
  analyze_uses_own_final_root input

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.retainedCutArmGraphs
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.retainedCutArmOutcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.actualArmsCutFaithful
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.carrierOccurrence_nonreal_iff_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_none_of_real_not_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_none_of_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.ligandCursorKeepsPredecessor
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_retainedOutcome_of_armIso
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_some_iff_retainedJudgment_of_armIso
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_none_iff_no_retainedJudgment_of_armIso
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_retainedCutOutcome_of_bridge
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualTargetCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.ligandCursor_outerRoot
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.ligandCutBridge
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.CanonicalLigandCut
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalLigandCut_nonempty
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalLigandCut
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.ligandCursor_previous
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.ligandCursorKeepsPredecessor_holds
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalCutGraphs
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.canonicalArmsCutFaithful
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_canonicalCutOutcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_some_iff_canonicalCutJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_none_iff_no_canonicalCutJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_retainedOutcome_of_canonicalCutIso
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_lowercase_iff_canonicalCut
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_eq_canonicalCut_geometric_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.all_carrier_occurrences_retained_on_actual_graphs
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.all_carrier_occurrences_retained_on_cut_arms
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.detected_referenceState_lowercase_iff_canonicalCut
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.detected_referenceState_eq_canonicalCut_geometric_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.detected_referenceState_lowercase_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_center_retainedOutcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_center_retainedCutOutcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_reads_own_final_root
