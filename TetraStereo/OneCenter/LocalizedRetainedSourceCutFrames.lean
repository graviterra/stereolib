import TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySourceWindows
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Source four-cut families of a retained occurrence

The accepted canonical cuts (`ContextFrameCompilation.canonicalCutGraphs`) are `cutRetainedArm`
graphs. Their focus and incoming carrier nodes are fixed by source equalities
(`occurrenceCarrierNode`), but the `CanonicalLigandCut` record holding them is chosen through a
faithfulness witness against the actual stage-`a` graph. This module states the same cuts from
source data alone:

* `sourceCutArm molecule root focus incoming`: `cutRetainedArm` at the carrier nodes `focus`,
  `incoming` when they are valid carrier nodes and form a `CutAnchor` (real child, inward or
  outward, or ring duplicate with its carrier parent). `SourceCutAdmissible` is a proposition;
  only its proofs are chosen, and `cutRetainedArm` does not depend on which proof.
* `sourceCutGraphs singleBonded target frame`: the four cuts whose focus is each frame cursor's
  carrier node and whose incoming node is the target's carrier node.
* `sourceCoordinates frame`: the certified spatial table at each frame cursor's current atom.
* The frame is the source reroot-child enumeration `localizedNoDoubleFourLigandFrameExec?` of
  the target cursor, a function of the target. No frame choice is made.

Connection to the accepted compilation (proofs only):

* `canonicalCutGraphs_eq_source`: the compiled canonical cuts **equal** the source cuts at the
  compiled frame.
* `actualCoordinates_eq_sourceCoordinates`: equal coordinates.
* `frame_eq_of_sourceFrame`: any source frame of the target is the compiled frame.

`assert_closure_excludes` checks that the source definitions mention no generated state, actual
descriptor map, frame compilation/skeleton or stage build. It walks every constant they transitively
use, including proofs.
-/

open Lean Elab Command in
/-- Fails if the transitive constant closure (types, values, proofs, constructors) of the first
declaration contains any listed declaration. -/
elab "assert_closure_excludes " n:ident " [" bad:ident,* "]" : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let mut badNames : Array Name := #[]
  for b in bad.getElems do
    badNames := badNames.push (← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo b)
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[name]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if badNames.contains c then
      throwError "{n} depends on {c}"
    match env.find? c with
    | some info =>
        let mut used := info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          used := used ++ value.getUsedConstants
        if let .inductInfo v := info then
          used := used ++ v.ctors.toArray
        for d in used do
          unless visited.contains d do
            stack := stack.push d
    | none => pure ()

namespace TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open scoped Classical

noncomputable section

universe u

/-! ## Source cut arms -/

section Generic

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (root : Atom)

/-- The carrier nodes are valid and `incoming` is an admitted cut predecessor of `focus`. -/
def SourceCutAdmissible (focus incoming : CarrierNode Atom) : Prop :=
  ∃ (hf : CarrierNode.Valid molecule root focus) (hi : CarrierNode.Valid molecule root incoming),
    CutAnchor (⟨focus, hf⟩ : Nodes molecule root) (some ⟨incoming, hi⟩)

/-- The predecessor cut at two carrier nodes. Outside admissibility it is the uncut root arm; that
branch is never used on a real detected occurrence (`sourceCutAdmissible_of_compilation`). -/
def sourceCutArm (focus incoming : CarrierNode Atom) : RootedDigraph Atom :=
  if h : SourceCutAdmissible molecule root focus incoming then
    cutRetainedArm molecule root ⟨focus, h.choose⟩ (some ⟨incoming, h.choose_spec.choose⟩)
      h.choose_spec.choose_spec
  else
    cutRetainedArm molecule root ⟨.real [root], carrier_root_valid molecule root⟩ none
      CutAnchor.noCut

/-- On admitted nodes the source cut is `cutRetainedArm`, for any proofs. -/
theorem sourceCutArm_eq {focus incoming : Nodes molecule root}
    (anchor : CutAnchor focus (some incoming)) :
    sourceCutArm molecule root focus.1 incoming.1 =
      cutRetainedArm molecule root focus (some incoming) anchor := by
  have h : SourceCutAdmissible molecule root focus.1 incoming.1 := ⟨focus.2, incoming.2, anchor⟩
  unfold sourceCutArm
  rw [dif_pos h]

end Generic

/-! ## Source admissibility of every executable reroot child

Real child: the target is an inward or outward reroot-child of the focus
(`realExecutableChild_incomingArmChild`). Ring-duplicate child: the target is its carrier parent.
The ring argument is the stage-free part of the accepted
`ringExecutableChild_retainedContextArmFaithful`, which also needs a stage arm for its
graph-faithfulness conclusion; that conclusion is not needed here. -/

theorem sourceCutAdmissible_of_executableChild (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (target cursor : input.LocalizedRerootCursor fuel)
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target) :
    SourceCutAdmissible input.moleculeGraph cursor.occurrence.1.root
      (input.occurrenceCarrierNode singleBonded cursor.occurrence)
      (input.occurrenceCarrierNode singleBonded target.occurrence) := by
  rcases input.carrierOccurrence_provenance_simple_or_ring singleBonded cursor.occurrence with
    real | ⟨distance, ring⟩
  · obtain ⟨path, hpath, inc, cursorCarrier, incomingEq, child⟩ :=
      input.realExecutableChild_incomingArmChild singleBonded target cursor childMem real
    rw [cursorCarrier, incomingEq]
    exact ⟨hpath, inc.2, CutAnchor.realChild child⟩
  · have targetReal :=
      input.retainedExecutableParent_realAtom singleBonded target cursor childMem
    have duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true :=
      input.isDuplicateLeaf_eq_true_of_ring_provenance cursor.occurrence.1.node ring
    have intended : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames target := by
      rw [← input.executableLocalizedRerootChildren_map target]
      exact List.mem_map.mpr ⟨cursor, childMem, rfl⟩
    have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended target
      cursor.occurrence.1 intended
    have split := (input.mem_localizedRerootNeighborFrames_iff (fuel := fuel)
      target.occurrence.1 cursor.occurrence.1).mp neighbor
    rcases split.2 with ⟨rootEq, shorter | longer⟩
    · -- A ring duplicate has no children, so it is not the target's parent.
      exfalso
      have targetNonempty : target.occurrence.1.address ≠ [] := by
        intro empty
        simp [empty] at shorter
      let slot := target.occurrence.1.address.getLast targetNonempty
      have addressEq : target.occurrence.1.address =
          cursor.occurrence.1.address ++ [slot] := by
        simpa [slot, shorter.2] using
          (List.dropLast_append_getLast targetNonempty).symm
      have cursorDerived :=
        (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
      have targetDerived :=
        (input.mem_localizedOccurrences_iff fuel target.occurrence.1).mp target.occurrence.2
      obtain ⟨_childNode, childAt, _frameEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child cursorDerived targetDerived
          rootEq.symm slot addressEq
      have presentNode := List.fst_mem_of_mem_zipIdx childAt
      unfold executableOfficialCIPChildren at presentNode
      rw [if_pos duplicate] at presentNode
      simp at presentNode
    · have cursorNonempty : cursor.occurrence.1.address ≠ [] := by
        intro empty
        simp [empty] at longer
      obtain ⟨certificate⟩ :=
        input.exists_localizedParentFrameHistory cursor.occurrence cursorNonempty
      have targetDerived :=
        (input.mem_localizedOccurrences_iff fuel target.occurrence.1).mp target.occurrence.2
      have parentDerived :=
        (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
      have frameEq : target.occurrence.1 = certificate.parent.1 :=
        input.declarativeLocalizedOccurrence_functional_at_root_address targetDerived
          parentDerived (rootEq.symm.trans certificate.parent_root.symm)
          (longer.2.trans certificate.parent_address.symm)
      have historyEq : cursor.occurrence.1.node.history =
          certificate.current :: certificate.parent.1.node.history := certificate.history_eq
      have frameNode : target.occurrence.1.node = certificate.parent.1.node := by
        rw [frameEq]
      have targetNodeEq : input.occurrenceCarrierNode singleBonded target.occurrence =
          .real certificate.parent.1.node.history.reverse := by
        rw [occurrenceCarrierNode, if_pos targetReal]
        simp [frameNode]
      have cursorNodeEq : input.occurrenceCarrierNode singleBonded cursor.occurrence =
          .ring certificate.parent.1.node.history.reverse certificate.current := by
        rw [occurrenceCarrierNode]
        have notReal : cursor.occurrence.1.node.provenance ≠
            OfficialCIPNodeProvenance.realAtom := by
          rw [ring]
          intro bad
          cases bad
        rw [if_neg notReal]
        simp [historyEq]
      have ringValid : CarrierNode.Valid input.moleculeGraph cursor.occurrence.1.root
          (.ring certificate.parent.1.node.history.reverse certificate.current) :=
        cursorNodeEq ▸ input.occurrenceCarrierNode_valid singleBonded cursor.occurrence
      rw [cursorNodeEq, targetNodeEq]
      exact ⟨ringValid, ringValid.1, CutAnchor.ringParent⟩

/-! ## The source four-cut family and coordinates -/

variable {input : Input}

/-- Source four-ligand frame: the reroot-child enumeration of the target cursor. -/
abbrev sourceFrame? (target : Occurrence input) :
    Option (input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :=
  input.certified.localizedNoDoubleFourLigandFrameExec? target

/-- Four predecessor cuts: each frame cursor's carrier node, entered from the target's. -/
def sourceCutGraphs (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    Fin 4 → RootedDigraph input.certified.Atom :=
  fun slot => sourceCutArm input.certified.moleculeGraph (frame.cursorAt slot).occurrence.1.root
    (input.certified.occurrenceCarrierNode singleBonded (frame.cursorAt slot).occurrence)
    (input.certified.occurrenceCarrierNode singleBonded target)

/-- Certified spatial positions of the four frame cursors' current atoms. -/
def sourceCoordinates
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)) :
    Fin 4 → Option CartesianPoint3 :=
  fun slot => input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt slot)

/-- Every source frame cursor is an executable reroot child of the target cursor. -/
theorem sourceFrame_childAt {target : Occurrence input}
    {frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)}
    (computed : sourceFrame? target = some frame) (slot : Fin 4) :
    frame.cursorAt slot ∈ input.certified.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.certified.LocalizedRerootCursor (carrierFuel input)) := by
  have original : input.certified.localizedOccurrenceFourLigandFrame? target = some frame := by
    rw [← input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact computed
  rw [← input.certified.localizedOccurrenceFourLigandFrame_cursors_eq_executable target frame
    original]
  exact List.get_mem frame.cursors (Fin.cast frame.length_eq.symm slot)

/-- **Source admissibility at a source frame**: every slot of every source frame uses the admitted
cut branch. The proof reads only the source carrier, never a stage. -/
theorem sourceCutAdmissible_at_sourceFrame
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) {target : Occurrence input}
    {frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)}
    (computed : sourceFrame? target = some frame) (slot : Fin 4) :
    SourceCutAdmissible input.certified.moleculeGraph (frame.cursorAt slot).occurrence.1.root
      (input.certified.occurrenceCarrierNode singleBonded (frame.cursorAt slot).occurrence)
      (input.certified.occurrenceCarrierNode singleBonded target) :=
  sourceCutAdmissible_of_executableChild input.certified singleBonded _ (frame.cursorAt slot)
    (sourceFrame_childAt computed slot)

/-- At a real detected occurrence a source frame exists (source skeleton; no stage build). -/
theorem sourceFrame_exists (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (detected : IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom) :
    ∃ frame, sourceFrame? target = some frame := by
  obtain ⟨skeleton⟩ := exists_cyclicContextFrameSkeleton input singleBonded target real
    ⟨input.certified.molecularFrameUnit target.1, detected⟩ rfl
  exact ⟨skeleton.frame, skeleton.frameComputed⟩

/-! ## Connection to the accepted compilation (proofs only) -/

section Compilation

variable {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (frames : ContextFrameCompilation input target unit targetUnit)

theorem frame_eq_of_sourceFrame
    {frame : input.certified.LocalizedOccurrenceFourLigandFrame (carrierFuel input)}
    (computed : sourceFrame? target = some frame) : frame = frames.frame :=
  Option.some.inj (computed.symm.trans frames.frameComputed)

/-- **The compiled canonical cuts are the source cuts.** -/
theorem canonicalCutGraphs_eq_source
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    frames.canonicalCutGraphs singleBonded = sourceCutGraphs singleBonded target frames.frame := by
  funext slot
  have focusEq := (frames.canonicalLigandCut singleBonded slot).focusCarrier
  have incomingEq := (frames.canonicalLigandCut singleBonded slot).incomingCarrier
  unfold sourceCutGraphs
  rw [← focusEq, ← incomingEq,
    sourceCutArm_eq _ _ (frames.canonicalLigandCut singleBonded slot).anchor]
  rfl

theorem actualCoordinates_eq_sourceCoordinates :
    frames.actualCoordinates = sourceCoordinates frames.frame :=
  funext fun slot => (frames.actualCursor_coordinates slot).symm

end Compilation

end

end TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames

assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceCutArm_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.frame_eq_of_sourceFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.canonicalCutGraphs_eq_source
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.actualCoordinates_eq_sourceCoordinates
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceCutAdmissible_of_executableChild
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceFrame_childAt
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceCutAdmissible_at_sourceFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceFrame_exists

/-! Proof closures of the well-definedness facts avoid generated state and stage builds too. -/
assert_closure_excludes
  TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceCutAdmissible_at_sourceFrame
  [TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm]
assert_closure_excludes TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceFrame_exists
  [TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm]

assert_closure_excludes TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceCutGraphs
  [TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.descriptorMap,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameSkeleton,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.cyclicContextFrameCompilation,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.contextOccurrenceView,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages]
assert_closure_excludes TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames.sourceCoordinates
  [TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.descriptorMap,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameSkeleton,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.cyclicContextFrameCompilation,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.contextOccurrenceView,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages]
