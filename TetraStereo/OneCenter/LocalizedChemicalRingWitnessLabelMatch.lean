import TetraStereo.OneCenter.LocalizedChemicalRingPromotedFullLabelMatch
import TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! The automorphism reconstructed from actual tied keys retains label-matched realizing paths.
This strengthens the molecular graph conclusion without asserting that every path is mapped by
the same permutation, or that equal recorded labels already imply proper physical orientation. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedChemicalRingPromotedFullLabelMatch
open LocalizedChemicalRingActualReferenceFixing LocalizedChemicalRingReaddressedSource
open LocalizedChemicalRingReferencePathReconstruction LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingColoredReconstruction RetainedCoherentSymmetry
open BoundaryComponentReconstruction

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- Equal actual labels at occurrences carrying the two complete boundary/path payloads.
Histories are retained; this is not a color assigned just to the terminal atom. -/
def PathLabelsAgree
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (B p q : List input.Atom) : Prop :=
  ∃ x : (ruleMajorTreeGraph treeL).Node, ∃ y : (ruleMajorTreeGraph treeR).Node,
    (nodeSource input treeL x).occurrence.1.node = boundaryNode B p ∧
    (nodeSource input treeR y).occurrence.1.node = boundaryNode B q ∧
    readL (nodeSource input treeL x) = readR (nodeSource input treeR y)

theorem path_labels_of_correspondence
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (addressL : (ruleMajorTreeGraph treeL).Addressing) (addressR : (ruleMajorTreeGraph treeR).Addressing)
    (denseL : Dense addressL) (denseR : Dense addressR)
    (labels : ∀ x y, addressL.address x = addressR.address y →
      readL (nodeSource input treeL x) = readR (nodeSource input treeR y))
    (B p q : List input.Atom)
    (correspond : PathsCorrespond
      (readdressed (toOfficialSourceTree treeL) addressL denseL)
      (readdressed (toOfficialSourceTree treeR) addressR denseR) B B p q) :
    PathLabelsAgree treeL treeR readL readR B p q := by
  obtain ⟨position, lookupL, lookupR⟩ := correspond
  obtain ⟨x, addressX, payloadX⟩ :=
    (readdressed_lookup_iff _ addressL denseL position _).mp lookupL
  obtain ⟨y, addressY, payloadY⟩ :=
    (readdressed_lookup_iff _ addressR denseR position _).mp lookupR
  exact ⟨x, y, (payload_eq_source treeL x).symm.trans payloadX,
    (payload_eq_source treeR y).symm.trans payloadY, labels x y (addressX.trans addressY.symm)⟩

section Actual

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

include fallback in
/-- Actual tied keys construct one reference-fixing molecular automorphism and, for every
source-component atom, a realizing path whose actual label matches its image under that same
permutation. No automorphism, selected path correspondence or label match is supplied. -/
theorem actual_tie_reference_fixed_aut_with_labels (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
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
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      (∀ z ∈ B, π z = z) ∧ π a = b ∧ π reference = reference ∧
      ∀ atom, InComponent input.moleculeGraph B a atom →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
          pathTerminal p.1 p.2.nonempty = atom ∧
          PathLabelsAgree
            (slotTree input single state target real unit targetUnit left)
            (slotTree input single state target real unit targetUnit right)
            (rawStateReader input state target) (rawStateReader input state target) B p.1 (p.1.map π) := by
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
      referenceAt (readdressed (toOfficialSourceTree treeL) matched.leftAddressing matched.leftCanonical.1)
        reference position =
      referenceAt (readdressed (toOfficialSourceTree treeR) matched.rightAddressing matched.rightCanonical.1)
        reference position := by
    rw [readdressed_referenceAt_eq, readdressed_referenceAt_eq]
    exact matched.same position
  have referencePreserved := residual_reference_preserved pair charge parentL parentR reference referenceSame
  have outside : a ∉ B := not_mem_of_nodup_append_singleton rootedL.nodup
  obtain ⟨π, aut, fixed, entry, ref, _, witnesses⟩ :=
    exists_reference_fixed_automorphism e outside reference referencePreserved
  refine ⟨π, aut, fixed, entry, ref, ?_⟩
  intro atom member
  obtain ⟨p, terminal, image⟩ := witnesses atom member
  refine ⟨p, terminal, ?_⟩
  have correspond := residualPathTreeEquivOfSameObservations_correspond pair charge rfl parentL parentR p
  have pathLabels := path_labels_of_correspondence treeL treeR
    (rawStateReader input state target) (rawStateReader input state target)
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1 matched.rightCanonical.1
    (fun x y address => (labels x y address).1) B p.1 (e.toEquiv p).1 correspond
  simpa only [image] using pathLabels

include fallback in
/-- At an actual root, boundary-rootedness and incoming adjacency are derived from the
computed frame. The resulting single automorphism retains the label-matched witness paths. -/
theorem actual_root_tie_reference_fixed_aut_with_labels (rootAddress : target.1.address = [])
    (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right)
    (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧ π reference = reference ∧
      ∀ atom, InComponent input.moleculeGraph [target.1.root] a atom →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph [target.1.root] a p},
          pathTerminal p.1 p.2.nonempty = atom ∧
          PathLabelsAgree
            (slotTree input single state target real unit targetUnit left)
            (slotTree input single state target real unit targetUnit right)
            (rawStateReader input state target) (rawStateReader input state target)
            [target.1.root] p.1 (p.1.map π) := by
  obtain ⟨rootedL, adjacentL⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress left a currentL
  obtain ⟨rootedR, adjacentR⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress right b currentR
  obtain ⟨π, aut, fixed, entry, ref, witnesses⟩ := actual_tie_reference_fixed_aut_with_labels
    input single state target real unit targetUnit reference W D fallback left right
    widthL heightL widthR heightR tie [target.1.root] a b rootedL rootedR charge
    (by
      intro z hz
      have eq : target.1.root = z := by simpa using hz
      simpa only [← eq] using adjacentL)
    (by
      intro z hz
      have eq : target.1.root = z := by simpa using hz
      simpa only [← eq] using adjacentR)
  exact ⟨π, aut, fixed _ (by simp), entry, ref, witnesses⟩

end Actual
end
end TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch.path_labels_of_correspondence
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch.actual_tie_reference_fixed_aut_with_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch.actual_root_tie_reference_fixed_aut_with_labels
