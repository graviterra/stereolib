import TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Actual tied keys supply one reference-fixing molecular automorphism with ranked,
label-matched realizing paths. The component exchange uses the chosen ranked isomorphism;
it does not independently choose a second reconstruction. The rank controls the residual
component at each witness, not arbitrary paths or physical orientations. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRankedWitnessLabels

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedChemicalRingPromotedFullLabelMatch
open LocalizedChemicalRingActualReferenceFixing LocalizedChemicalRingReaddressedSource
open LocalizedChemicalRingReferencePathReconstruction LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingColoredReconstruction RetainedCoherentSymmetry
open BoundaryComponentReconstruction LocalizedChemicalRingRankedReconstruction
open LocalizedChemicalRingWitnessLabelMatch

noncomputable section
open scoped Classical

/-- Extend this particular ranked isomorphism, retaining its rank and realizing paths.
Reference-color preservation fixes the reference under the same component exchange. -/
theorem ranked_reference_fixed_aut {V : Type*} [Fintype V] [DecidableEq V]
    {m : MoleculeGraph V} {B : List V} {a b : V}
    (e : ResidualPathTreeEquiv m B B a b) (outside : a ∉ B) (reference : V)
    (preserved : TerminalColorPreserved e (referenceColor reference))
    (ranked : RankedWitnessIso e) :
    ∃ π : Equiv.Perm V, m.IsAutomorphism π ∧ (∀ z ∈ B, π z = z) ∧
      π a = b ∧ π reference = reference ∧
      ∀ x, InComponent m B a x →
        ∃ p : {p : List V // ResidualObsPath m B a p},
          pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map π ∧
          ∀ y, InComponent m (B ++ p.1.dropLast) x y → y ≠ x → ranked.rank x < ranked.rank y := by
  have targetOutside := target_root_outside e outside
  refine ⟨componentExchangePerm ranked.iso outside targetOutside,
    componentExchangePerm_isAutomorphism ranked.iso outside targetOutside, ?_, ?_, ?_, ?_⟩
  · intro z member
    rw [componentExchangePerm_apply]
    exact exchange_of_none ranked.iso (fun h => inComponent_not_mem m h member)
      (fun h => inComponent_not_mem m h member)
  · rw [componentExchangePerm_apply, exchange_of_a ranked.iso (inComponent_self m outside)]
    exact ranked.iso.entry
  · rw [componentExchangePerm_apply]
    have same := componentExchange_color_eq e ranked.toWitnessed (referenceColor reference)
      preserved reference
    change referenceColor reference (componentExchange ranked.iso reference) =
      referenceColor reference reference at same
    by_contra different
    simp [referenceColor, different] at same
  · intro x member
    obtain ⟨p, terminal, image, ordered⟩ := ranked.witnessPath x member
    refine ⟨p, terminal, ?_, ordered⟩
    rw [image]
    apply List.map_congr_left
    intro u present
    rw [componentExchangePerm_apply,
      exchange_of_a ranked.iso (obsPath_mem_inComponent p.2 present)]

section Actual

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

include fallback in
/-- Actual refined-key equality constructs one molecular automorphism, one finite rank,
and label-matched witnesses obeying that rank. The source observations, reference
preservation, and witness label matches are derived from the actual keys. -/
theorem actual_tie_ranked_reference_fixed_aut_with_labels (left right : Fin 4)
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
    ∃ (π : Equiv.Perm input.Atom) (rank : input.Atom → Nat),
      input.moleculeGraph.IsAutomorphism π ∧ (∀ z ∈ B, π z = z) ∧
      π a = b ∧ π reference = reference ∧
      ∀ atom, InComponent input.moleculeGraph B a atom →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
          pathTerminal p.1 p.2.nonempty = atom ∧
          PathLabelsAgree
            (slotTree input single state target real unit targetUnit left)
            (slotTree input single state target real unit targetUnit right)
            (rawStateReader input state target) (rawStateReader input state target) B p.1 (p.1.map π) ∧
          ∀ y, InComponent input.moleculeGraph (B ++ p.1.dropLast) atom y →
            y ≠ atom → rank atom < rank y := by
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
  let ranked : RankedWitnessIso e := Classical.choice (exists_rankedWitnessIso e outside)
  obtain ⟨π, aut, fixed, entry, ref, witnesses⟩ :=
    ranked_reference_fixed_aut e outside reference referencePreserved ranked
  refine ⟨π, ranked.rank, aut, fixed, entry, ref, ?_⟩
  intro atom member
  obtain ⟨p, terminal, image, ordered⟩ := witnesses atom member
  refine ⟨p, terminal, ?_, ordered⟩
  have correspond := residualPathTreeEquivOfSameObservations_correspond pair charge rfl parentL parentR p
  have pathLabels := path_labels_of_correspondence treeL treeR
    (rawStateReader input state target) (rawStateReader input state target)
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1 matched.rightCanonical.1
    (fun x y address => (labels x y address).1) B p.1 (e.toEquiv p).1 correspond
  simpa only [image] using pathLabels

include fallback in
/-- At the original root, the actual frame supplies boundary-rootedness and incoming
adjacency. The same permutation, rank, and occurrence-label witnesses are retained. -/
theorem actual_root_tie_ranked_reference_fixed_aut_with_labels (rootAddress : target.1.address = [])
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
    ∃ (π : Equiv.Perm input.Atom) (rank : input.Atom → Nat), input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧ π reference = reference ∧
      ∀ atom, InComponent input.moleculeGraph [target.1.root] a atom →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph [target.1.root] a p},
          pathTerminal p.1 p.2.nonempty = atom ∧
          PathLabelsAgree
            (slotTree input single state target real unit targetUnit left)
            (slotTree input single state target real unit targetUnit right)
            (rawStateReader input state target) (rawStateReader input state target)
            [target.1.root] p.1 (p.1.map π) ∧
          ∀ y, InComponent input.moleculeGraph ([target.1.root] ++ p.1.dropLast) atom y →
            y ≠ atom → rank atom < rank y := by
  obtain ⟨rootedL, adjacentL⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress left a currentL
  obtain ⟨rootedR, adjacentR⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress right b currentR
  obtain ⟨π, rank, aut, fixed, entry, ref, witnesses⟩ := actual_tie_ranked_reference_fixed_aut_with_labels
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
  exact ⟨π, rank, aut, fixed _ (by simp), entry, ref, witnesses⟩

end Actual
end
end TetraStereo.OneCenter.LocalizedChemicalRingRankedWitnessLabels

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedWitnessLabels.ranked_reference_fixed_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedWitnessLabels.actual_tie_ranked_reference_fixed_aut_with_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedWitnessLabels.actual_root_tie_ranked_reference_fixed_aut_with_labels
