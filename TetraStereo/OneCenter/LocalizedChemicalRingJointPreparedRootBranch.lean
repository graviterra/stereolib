import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Actual original-root joint ties supply the constitutional tied-branch certificate for
every residual query. Root/arm histories, real children, successful Rule-4a builds, the
Rule-1a tie, and query membership are derived; none is a caller-supplied branch premise. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranch

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointSelectedTieWitness (joint_refined_tie_constitutional)
open LocalizedChemicalRingJointPreparedRootWitness (root_slot_data)
open LocalizedChemicalRingProperRotationConsensus (slot_current referenceAt_injective)
open LocalizedChemicalRingReferenceConsensusCorrectionInduction (actual_boundary)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedActualBoundaryObservationReadback
open LocalizedActualOutwardRule1bEquivalence
open LocalizedActualBoundaryPathRealization

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (rootAddress : data.target.1.address = [])
  (state : OccurrenceAuxState) (references : List input.Atom)
  (left right : Fin 4) (distinct : left ≠ right)
  (tie : slotKeys input mol single c node data state references left =
    slotKeys input mol single c node data state references right)

include rootAddress distinct tie in
theorem query_branch (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse
      (referenceAt input mol c node data left) p)
    (d : input.detectedMultiCenterMolecule.Center) (query : RawMolecule.CanonicalBranchNode)
    (payload : rawPathNode data.target.1.root (boundaryPath data.target p) = query)
    (actual : OccurrenceData input mol d query) : Nonempty (TiedRootBranch input actual.target) := by
  let frame := frames input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
  have rootNode : data.target.1.node = OfficialCIPNode.root data.target.1.root := by
    have h := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((input.mem_localizedOccurrences_iff _ _).mp data.target.2) rootAddress
    exact congrArg (fun occurrence => occurrence.node) h
  have history : data.target.1.node.history = [data.target.1.root] := by rw [rootNode]; rfl
  have rootCurrent : data.target.1.node.current? = some data.target.1.root := by rw [rootNode]; rfl
  have currentL := slot_current input mol single c node data state left
  have currentR := slot_current input mol single c node data state right
  obtain ⟨realL, rootL, slotL, addressL⟩ := root_slot_data input single _ data.target frame
    rootAddress left _ currentL
  obtain ⟨realR, rootR, slotR, addressR⟩ := root_slot_data input single _ data.target frame
    rootAddress right _ currentR
  have child := outwardChild_node_mem input
    (⟨data.target, none⟩ : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (frame.frame.cursorAt left) rootL slotL addressL
  obtain ⟨next, nodeEq, _, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input single _ rootCurrent data.real _).mp child
  have nextEq : next = referenceAt input mol c node data left := by
    rw [nodeEq] at currentL
    exact Option.some.inj currentL
  subst next
  have armHistory : (frame.frame.cursorAt left).occurrence.1.node.history =
      [referenceAt input mol c node data left, data.target.1.root] := by
    rw [nodeEq]
    change referenceAt input mol c node data left :: data.target.1.node.history = _
    rw [history]
  have boundary := actual_boundary input mol single data actual p payload.symm
  have queryHistory : actual.target.1.node.history = (data.target.1.root :: p).reverse := by
    have h := congrArg List.reverse boundary
    simpa only [List.reverse_reverse, history, List.reverse_singleton, List.singleton_append] using h
  have packed := input.legitimateOccurrence_transport single 1
    (input.carrierOccurrence_legitimate single actual.target)
  have queryRoot : actual.target.1.root = data.target.1.root := by
    have h := packed.sourceHead
    simpa only [queryHistory, List.reverse_reverse, List.head?_cons, Option.some.injEq] using h.symm
  have nonroot : actual.target.1.address ≠ [] := by
    intro empty
    have length := congrArg List.length packed.sourceAddress
    rw [empty] at length
    simp only [CertifiedLocalizedCIPInput.canonicalAddress, queryHistory, List.reverse_reverse, List.tail_cons,
      foldSlots_length, List.length_nil] at length
    exact valid.nonempty (List.length_eq_zero_iff.mp length.symm)
  have constitutional := joint_refined_tie_constitutional input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left right tie
  change OfficialRuleMajorKey.compare (frame.stages left).a.key.constitutional
    (frame.stages right).a.key.constitutional = .eq at constitutional
  have rule1a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (frame.stages left).a.key.constitutional.rule1a
      (frame.stages right).a.key.constitutional.rule1a = .eq := by
    unfold OfficialRuleMajorKey.compare at constitutional
    cases first : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (frame.stages left).a.key.constitutional.rule1a
        (frame.stages right).a.key.constitutional.rule1a <;>
      simp_all only [compareLex, Ordering.byKey, Ordering.then]
  refine ⟨{
    rootCursor := ⟨data.target, none⟩
    rootAddress := rootAddress
    arm := frame.frame.cursorAt left
    arm' := frame.frame.cursorAt right
    member := frame.childAt left
    member' := frame.childAt right
    different := ?_
    real := realL
    real' := realR
    read := _
    read' := _
    fuel := 2 * (retainedCarrierFuel input + 1)
    fuel' := 2 * (retainedCarrierFuel input + 1)
    key := (frame.stages left).a.key
    key' := (frame.stages right).a.key
    built := (input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized _ _ _).symm.trans
      (frame.stages left).a.built
    built' := (input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized _ _ _).symm.trans
      (frame.stages right).a.built
    tie := rule1a
    inside := ?_
    nonroot := nonroot }⟩
  · intro same
    have h := congrArg (fun occurrence => occurrence.1.node.current?) same
    exact distinct (referenceAt_injective input mol c node data (Option.some.inj
      ((slot_current input mol single c node data state left).symm.trans (h.trans currentR))))
  · obtain ⟨first, rest, split⟩ := List.exists_cons_of_ne_nil valid.nonempty
    have firstEq : first = referenceAt input mol c node data left := by
      have head := valid.head
      rw [split] at head
      exact Option.some.inj head
    subst first
    have armAddress := (input.legitimateOccurrence_transport single 1
      (input.carrierOccurrence_legitimate single (frame.frame.cursorAt left).occurrence)).sourceAddress
    refine ⟨rootL.trans queryRoot.symm, ?_⟩
    rw [armAddress, packed.sourceAddress, rootL, queryRoot]
    simp [CertifiedLocalizedCIPInput.canonicalAddress, armHistory, queryHistory, split]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranch.query_branch
