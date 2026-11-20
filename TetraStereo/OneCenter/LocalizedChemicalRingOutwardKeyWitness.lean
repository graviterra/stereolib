import TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedWitnessLabels
import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout
import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
The unchanged runtime marker dimensions suffice at every real outward occurrence,
including inside rings. An actual tie at those dimensions therefore constructs one
history- and reference-fixing automorphism with support, deletion ranks, and exact
optional generated-fact matches. Layout bounds and a separately chosen matching
automorphism are not premises. Physical orientation at other centers is not asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingOutwardKeyWitness

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingActualReferenceFixing LocalizedActualBoundaryPathRealization
open LocalizedActualBoundaryObservationReadback LocalizedChemicalRingTwoFixedNeighbors
open LocalizedChemicalRingPrefixRankedWitnessLabels LocalizedChemicalRingWitnessLabelMatch
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingDefaultMarkerLayout RetainedCoherentSymmetry

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

/-- The default width/depth cover an actual outward slot, without a root-address premise. -/
theorem outward_slot_default_bounds (slot : Fin 4) (atom : input.Atom)
    (current : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.current? = some atom)
    (childReal : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.provenance = .realAtom)
    (sameRoot : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.root = target.1.root)
    (childSlot : Nat)
    (address : ((frames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.address = target.1.address ++ [childSlot]) :
    (∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit slot)).childList node).length ≤
      retainedCarrierFuel input) ∧
    (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit slot)).height ≤
      2 * (retainedCarrierFuel input + 1) := by
  let frame := frames input single state target real unit targetUnit
  obtain ⟨rooted, _, _⟩ := outward_slot_boundary input single
    (rawStateDescriptorMap input state) target frame real slot atom current childReal sameRoot childSlot address
  exact ⟨source_branching_le single _ rooted.generated, trace_height_le (frame.stages slot).a.trace⟩

/-- One reconstruction carries both structural and label evidence at the actual runtime
layout. Optional fact matches include absent labels; they do not assert that absence is
physically meaningful. The reference may be arbitrarily distant. -/
theorem actual_outward_default_tie_witness
    (reference : input.Atom) (left right : Fin 4) (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (realL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.provenance = .realAtom)
    (realR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.provenance = .realAtom)
    (rootL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.root = target.1.root)
    (rootR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.root = target.1.root)
    (slotL slotR : Nat)
    (addressL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.address = target.1.address ++ [slotL])
    (addressR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.address = target.1.address ++ [slotR])
    (tie : refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left =
      refinedKey input single state target real unit targetUnit reference
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ (e : input.detectedMultiCenterMolecule.Aut) (rank : input.Atom → Nat),
      (∀ atom ∈ target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom) ∧
      (e : Equiv.Perm input.Atom) a = b ∧
      (e : Equiv.Perm input.Atom) reference = reference ∧
      (∀ z, ¬ InComponent input.moleculeGraph target.1.node.history.reverse a z →
        ¬ InComponent input.moleculeGraph target.1.node.history.reverse b z →
        (e : Equiv.Perm input.Atom) z = z) ∧
      ∀ c : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph target.1.node.history.reverse a c.1 →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph target.1.node.history.reverse a p},
          pathTerminal p.1 p.2.nonempty = c.1 ∧
          PathLabelsAgree
            (slotTree input single state target real unit targetUnit left)
            (slotTree input single state target real unit targetUnit right)
            (rawStateReader input state target) (rawStateReader input state target)
            target.1.node.history.reverse p.1 (p.1.map (e : Equiv.Perm input.Atom)) ∧
          (state.factAt? (rawPathNode target.1.root (boundaryPath target p.1))).map factLabel =
            (state.factAt? (rawPathNode target.1.root
              (boundaryPath target (p.1.map (e : Equiv.Perm input.Atom))))).map factLabel ∧
          (∀ y ∈ p.1.dropLast, rank y < rank c.1) ∧
          ∀ y, InComponent input.moleculeGraph (target.1.node.history.reverse ++ p.1.dropLast) c.1 y →
            y ≠ c.1 → rank c.1 < rank y := by
  let frame := frames input single state target real unit targetUnit
  obtain ⟨rootedL, _, adjacentL⟩ := outward_slot_boundary input single
    (rawStateDescriptorMap input state) target frame real left a currentL realL rootL slotL addressL
  obtain ⟨rootedR, _, adjacentR⟩ := outward_slot_boundary input single
    (rawStateDescriptorMap input state) target frame real right b currentR realR rootR slotR addressR
  obtain ⟨widthL, heightL⟩ := outward_slot_default_bounds input single state target real unit
    targetUnit left a currentL realL rootL slotL addressL
  obtain ⟨widthR, heightR⟩ := outward_slot_default_bounds input single state target real unit
    targetUnit right b currentR realR rootR slotR addressR
  have history := occurrence_history_facts input target real
  have parentOf : ∀ x : input.Atom,
      (∀ c, target.1.node.current? = some c → input.moleculeGraph.Adj c x) →
      ∀ z, target.1.node.history.reverse.getLast? = some z → input.moleculeGraph.Adj x z := by
    intro x adjacent z last
    rw [List.getLast?_reverse, ← history.2] at last
    exact input.moleculeGraph.adj_symm.mp (adjacent z last)
  obtain ⟨π, rank, aut, boundary, image, ref, support, witnesses⟩ :=
    actual_tie_prefix_ranked_reference_fixed_aut_with_labels input single state target real unit targetUnit
      reference (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
      (frame.retainedKeys unit left) left right widthL heightL widthR heightR tie
      target.1.node.history.reverse a b rootedL rootedR charge (parentOf a adjacentL) (parentOf b adjacentR)
  let e : input.detectedMultiCenterMolecule.Aut :=
    input.moleculeGraph.detectedMultiCenterAutOfGraphAut ⟨π, aut⟩
  refine ⟨e, rank, ?_, image, ref, support, ?_⟩
  · intro atom member
    exact boundary atom (List.mem_reverse.mpr member)
  · intro c member
    obtain ⟨p, terminal, labels, lower, higher⟩ := witnesses c.1 member
    have detected (d : input.detectedMultiCenterMolecule.Center) :
        IsDetectedCenter input.moleculeGraph d.1 :=
      (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card d.1).mp
        ((input.moleculeGraph.mem_tetrahedralCenterSet d.1).mp d.2)
    have mappedNonempty : p.1.map π ≠ [] := by simpa using p.2.nonempty
    have mappedTerminal : pathTerminal (p.1.map π) mappedNonempty = π c.1 := by
      simp only [pathTerminal, List.getLast_map]
      exact congrArg π terminal
    have sameFacts := fact_labels_eq_of_boundary_pathLabelsAgree single state target
      (slotTree input single state target real unit targetUnit left)
      (slotTree input single state target real unit targetUnit right)
      p.1 (p.1.map π) p.2.nonempty mappedNonempty
      (by rw [terminal]; exact detected c)
      (by rw [mappedTerminal]; exact detected (input.detectedMultiCenterMolecule.centerPerm e c)) labels
    exact ⟨p, terminal, labels, sameFacts, lower, higher⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingOutwardKeyWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOutwardKeyWitness.outward_slot_default_bounds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOutwardKeyWitness.actual_outward_default_tie_witness
