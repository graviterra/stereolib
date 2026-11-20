import TetraStereo.OneCenter.LocalizedChemicalRingOutwardKeyWitness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
Actual refined-key equality preserves labels along EVERY prescribed residual path,
under one residual path-tree equivalence. The corresponding path need not be the
pointwise image under a previously reconstructed molecular automorphism. Reference
terminal colors are preserved by this same equivalence. At actual outward slots,
default layout bounds are derived and detected terminals give exact optional raw
fact-label equality at the original-root histories.

No successful label, global atomwise path map, or physical sign is assumed or asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathLabels

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedChemicalRingPromotedFullLabelMatch
open LocalizedChemicalRingActualReferenceFixing LocalizedChemicalRingReaddressedSource
open LocalizedChemicalRingReferencePathReconstruction LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingColoredReconstruction RetainedCoherentSymmetry
open LocalizedChemicalRingWitnessLabelMatch LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingOutwardKeyWitness
open LocalizedChemicalRingTwoFixedNeighbors LocalizedActualBoundaryObservationReadback

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

/-- A single path equivalence supplies actual label equality for all prescribed paths.
Its reference-color property comes from the same promoted marker correspondence. -/
theorem actual_tie_path_equivalence
    (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)
    (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph
      (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph
      (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph
      (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph
      (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right)
    (B : List input.Atom) (a b : input.Atom)
    (rootedL : BoundaryRootedTree input B a
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit left)))
    (rootedR : BoundaryRootedTree input B b
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit right)))
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (parentL : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj a z)
    (parentR : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj b z) :
    ∃ e : ResidualPathTreeEquiv input.moleculeGraph B B a b,
      TerminalColorPreserved e (referenceColor reference) ∧
      ∀ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
        PathLabelsAgree
          (slotTree input single state target real unit targetUnit left)
          (slotTree input single state target real unit targetUnit right)
          (rawStateReader input state target) (rawStateReader input state target)
          B p.1 (e.toEquiv p).1 := by
  obtain ⟨matched, same, occupied, labels⟩ := actual_tie_joint_full_label_readback input single state
    target real unit targetUnit reference W D fallback left right widthL heightL widthR heightR tie
  let treeL := slotTree input single state target real unit targetUnit left
  let treeR := slotTree input single state target real unit targetUnit right
  have constitution := readdressed_constitution_eq treeL treeR
    (LocalizedRuleMajorSortTrace.realizes_of_trace
      ((frames input single state target real unit targetUnit).stages left).a.trace)
    (LocalizedRuleMajorSortTrace.realizes_of_trace
      ((frames input single state target real unit targetUnit).stages right).a.trace)
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1
    matched.rightCanonical.1 same occupied
  let pair := observedTreePair_of_constitutional single
    (readdressed_boundaryRooted _ matched.leftAddressing matched.leftCanonical.1 rootedL)
    (readdressed_boundaryRooted _ matched.rightAddressing matched.rightCanonical.1 rootedR)
    rfl constitution
  let e := residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR
  have referenceSame (position : List Nat) :
      referenceAt (readdressed (toOfficialSourceTree treeL)
        matched.leftAddressing matched.leftCanonical.1) reference position =
      referenceAt (readdressed (toOfficialSourceTree treeR)
        matched.rightAddressing matched.rightCanonical.1) reference position := by
    rw [readdressed_referenceAt_eq, readdressed_referenceAt_eq]
    exact matched.same position
  refine ⟨e, residual_reference_preserved pair charge parentL parentR reference referenceSame, ?_⟩
  intro p
  exact path_labels_of_correspondence treeL treeR
    (rawStateReader input state target) (rawStateReader input state target)
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1 matched.rightCanonical.1
    (fun x y address => (labels x y address).1) B p.1 (e.toEquiv p).1
    (residualPathTreeEquivOfSameObservations_correspond pair charge rfl parentL parentR p)

/-- At actual real outward slots the runtime marker layout covers both trees. Every
prescribed path then has a matching full-history optional fact label whenever both
terminals are detected centers. Detection of the image terminal remains explicit. -/
theorem actual_outward_default_tie_path_equivalence
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
    ∃ e : ResidualPathTreeEquiv input.moleculeGraph
        target.1.node.history.reverse target.1.node.history.reverse a b,
      TerminalColorPreserved e (referenceColor reference) ∧
      ∀ p : {p : List input.Atom //
          ResidualObsPath input.moleculeGraph target.1.node.history.reverse a p},
        PathLabelsAgree
          (slotTree input single state target real unit targetUnit left)
          (slotTree input single state target real unit targetUnit right)
          (rawStateReader input state target) (rawStateReader input state target)
          target.1.node.history.reverse p.1 (e.toEquiv p).1 ∧
        (IsDetectedCenter input.moleculeGraph (pathTerminal p.1 p.2.nonempty) →
          IsDetectedCenter input.moleculeGraph
            (pathTerminal (e.toEquiv p).1 (e.toEquiv p).2.nonempty) →
          (state.factAt? (rawPathNode target.1.root (boundaryPath target p.1))).map factLabel =
            (state.factAt? (rawPathNode target.1.root
              (boundaryPath target (e.toEquiv p).1))).map factLabel) := by
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
  obtain ⟨e, referencePreserved, labels⟩ := actual_tie_path_equivalence input single state target
    real unit targetUnit reference (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))
    (frame.retainedKeys unit left) left right widthL heightL widthR heightR tie
    target.1.node.history.reverse a b rootedL rootedR charge (parentOf a adjacentL) (parentOf b adjacentR)
  refine ⟨e, referencePreserved, ?_⟩
  intro p
  refine ⟨labels p, ?_⟩
  intro detectedP detectedQ
  exact fact_labels_eq_of_boundary_pathLabelsAgree single state target
    (slotTree input single state target real unit targetUnit left)
    (slotTree input single state target real unit targetUnit right)
    p.1 (e.toEquiv p).1 p.2.nonempty (e.toEquiv p).2.nonempty detectedP detectedQ (labels p)

end
end TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathLabels

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathLabels.actual_tie_path_equivalence
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathLabels.actual_outward_default_tie_path_equivalence
