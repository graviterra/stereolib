import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.OneCenter.LocalizedChemicalRingRankedWitnessLabels
import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! One actual outward-key tie supplies the SAME history-fixing automorphism for local
oddness, a finite residual rank, and exact optional stored-fact matches at detected witness
centers. The actual target's existing history is retained. This uses the
ranked reconstruction's witnesses instead of choosing a second automorphism for parity.
Real outward slots, distinct neighboring parent/reference atoms, and marker layout bounds
remain explicit. Properness at other centers, including boundary centers, is not asserted. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingOddRankedWitness

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingActualReferenceFixing LocalizedActualBoundaryPathRealization
open LocalizedActualBoundaryObservationReadback LocalizedChemicalRingTwoFixedNeighbors
open LocalizedChemicalRingRankedWitnessLabels LocalizedChemicalRingWitnessLabelMatch
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open RetainedCoherentSymmetry

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

include fallback in
theorem actual_outward_tie_odd_ranked_aut_with_labels
    (center : input.detectedMultiCenterMolecule.Center)
    (centerCurrent : target.1.node.current? = some center.1)
    (parent : input.Atom) (parentHistory : parent ∈ target.1.node.history)
    (parentAdjacent : input.moleculeGraph.Adj center.1 parent)
    (referenceAdjacent : input.moleculeGraph.Adj center.1 reference) (different : parent ≠ reference)
    (left right : Fin 4) (a b : input.Atom) (distinct : a ≠ b)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (realL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.provenance = .realAtom)
    (realR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.provenance = .realAtom)
    (rootL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.root = target.1.root)
    (rootR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.root = target.1.root)
    (slotL slotR : Nat)
    (addressL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.address = target.1.address ++ [slotL])
    (addressR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.address = target.1.address ++ [slotR])
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ (e : input.detectedMultiCenterMolecule.Aut) (rank : input.Atom → Nat),
      (∀ atom ∈ target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom) ∧
      (e : Equiv.Perm input.Atom) a = b ∧ (e : Equiv.Perm input.Atom) reference = reference ∧
      input.detectedMultiCenterMolecule.centerPerm e center = center ∧
      permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e center) = -1 ∧
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
          ∀ y, InComponent input.moleculeGraph (target.1.node.history.reverse ++ p.1.dropLast) c.1 y →
            y ≠ c.1 → rank c.1 < rank y := by
  let frame := frames input single state target real unit targetUnit
  obtain ⟨rootedL, _, adjacentL⟩ := outward_slot_boundary input single
    (rawStateDescriptorMap input state) target frame real left a currentL realL rootL slotL addressL
  obtain ⟨rootedR, _, adjacentR⟩ := outward_slot_boundary input single
    (rawStateDescriptorMap input state) target frame real right b currentR realR rootR slotR addressR
  have history := occurrence_history_facts input target real
  have parentOf : ∀ x : input.Atom,
      (∀ c, target.1.node.current? = some c → input.moleculeGraph.Adj c x) →
      ∀ z, target.1.node.history.reverse.getLast? = some z → input.moleculeGraph.Adj x z := by
    intro x adjacent z last
    rw [List.getLast?_reverse, ← history.2] at last
    exact input.moleculeGraph.adj_symm.mp (adjacent z last)
  obtain ⟨π, rank, aut, boundary, image, ref, witnesses⟩ :=
    actual_tie_ranked_reference_fixed_aut_with_labels input single state target real unit targetUnit
      reference W D fallback left right widthL heightL widthR heightR tie
      target.1.node.history.reverse a b rootedL rootedR charge (parentOf a adjacentL) (parentOf b adjacentR)
  let e : input.detectedMultiCenterMolecule.Aut :=
    input.moleculeGraph.detectedMultiCenterAutOfGraphAut ⟨π, aut⟩
  have fixed : ∀ atom ∈ target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom := by
    intro atom member
    exact boundary atom (List.mem_reverse.mpr member)
  have centerHistory : center.1 ∈ target.1.node.history := by
    have head : target.1.node.history.head? = some center.1 := history.2.symm.trans centerCurrent
    exact List.mem_of_head? head
  have odd := local_odd_of_two_fixed_neighbors input.detectedMultiCenterMolecule e center
    (fixed center.1 centerHistory) parent reference different parentAdjacent referenceAdjacent
    (fixed parent parentHistory) ref ⟨a, adjacentL center.1 centerCurrent, by
      change π a ≠ a
      rw [image]
      exact Ne.symm distinct⟩
  refine ⟨e, rank, fixed, image, ref, odd.1, odd.2, ?_⟩
  intro c member
  obtain ⟨p, terminal, labels, ordered⟩ := witnesses c.1 member
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
  exact ⟨p, terminal, labels, sameFacts, ordered⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingOddRankedWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOddRankedWitness.actual_outward_tie_odd_ranked_aut_with_labels
