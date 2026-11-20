import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstructionSource
import TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessLabelMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! One all-reference-fixing molecular reconstruction with label-matched witness paths and
finite deletion ranks, derived from actual joint-key equality. Both reference fixation and
label correspondence concern the same ranked reconstruction. Layout coverage and boundary
geometry are explicit here; physical properness of generated labels is not asserted. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRankedWitness

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedChemicalRingJointMarkerRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedChemicalRingPromotedFullLabelMatch
open LocalizedChemicalRingActualReferenceFixing LocalizedChemicalRingReaddressedSource
open LocalizedChemicalRingReferencePathReconstruction LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingColoredReconstruction RetainedCoherentSymmetry
open BoundaryComponentReconstruction LocalizedChemicalRingRankedReconstruction
open LocalizedChemicalRingWitnessLabelMatch
open LocalizedChemicalRingPrefixRankedReconstruction
open LocalizedChemicalRingJointMarkerReconstructionSource

noncomputable section
open scoped Classical

/-- Extend one ranked reconstruction while preserving the whole vector of reference colors. -/
theorem prefix_ranked_references_fixed_aut (input : CertifiedLocalizedCIPInput)
    {B : List input.Atom} {a b : input.Atom}
    (e : ResidualPathTreeEquiv input.moleculeGraph B B a b) (outside : a ∉ B)
    (references : List input.Atom)
    (preserved : TerminalColorPreserved e (referenceVectorColor input references))
    (ranked : PrefixRankedWitnessIso e) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      (∀ z ∈ B, π z = z) ∧ π a = b ∧
      (∀ reference ∈ references, π reference = reference) ∧
      (∀ z, ¬ InComponent input.moleculeGraph B a z →
        ¬ InComponent input.moleculeGraph B b z → π z = z) ∧
      ∀ x, InComponent input.moleculeGraph B a x →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
          pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map π ∧
          (∀ y ∈ p.1.dropLast, ranked.rank y < ranked.rank x) ∧
          ∀ y, InComponent input.moleculeGraph (B ++ p.1.dropLast) x y →
            y ≠ x → ranked.rank x < ranked.rank y := by
  have targetOutside := target_root_outside e outside
  let π := componentExchangePerm ranked.iso outside targetOutside
  refine ⟨π, componentExchangePerm_isAutomorphism ranked.iso outside targetOutside,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro z member
    rw [componentExchangePerm_apply]
    exact exchange_of_none ranked.iso
      (fun h => inComponent_not_mem input.moleculeGraph h member)
      (fun h => inComponent_not_mem input.moleculeGraph h member)
  · rw [componentExchangePerm_apply, exchange_of_a ranked.iso
      (inComponent_self input.moleculeGraph outside)]
    exact ranked.iso.entry
  · apply reference_fixed_of_vectorColor input references π
    intro z
    exact componentExchange_color_eq e ranked.toRanked.toWitnessed
      (referenceVectorColor input references) preserved z
  · intro z left right
    exact exchange_of_none ranked.iso left right
  · intro x member
    obtain ⟨p, terminal, image, prefixLower, ordered⟩ := ranked.witnessPath x member
    refine ⟨p, terminal, ?_, prefixLower, ordered⟩
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
  (references : List input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

include fallback in
/-- Actual refined-key equality constructs one molecular automorphism, one finite rank,
and label-matched witnesses obeying that rank. The source observations, reference
preservation, and witness label matches are derived from the actual keys. -/
theorem actual_joint_tie_prefix_ranked_references_fixed_aut_with_labels (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit references W D left =
      refinedKey input single state target real unit targetUnit references W D right)
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
      π a = b ∧ (∀ reference ∈ references, π reference = reference) ∧
      (∀ z, ¬ InComponent input.moleculeGraph B a z →
        ¬ InComponent input.moleculeGraph B b z → π z = z) ∧
      ∀ atom, InComponent input.moleculeGraph B a atom →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph B a p},
          pathTerminal p.1 p.2.nonempty = atom ∧
          PathLabelsAgree
            (slotTree input single state target real unit targetUnit left)
            (slotTree input single state target real unit targetUnit right)
            (rawStateReader input state target) (rawStateReader input state target) B p.1 (p.1.map π) ∧
          (∀ y ∈ p.1.dropLast, rank y < rank atom) ∧
          ∀ y, InComponent input.moleculeGraph (B ++ p.1.dropLast) atom y →
            y ≠ atom → rank atom < rank y := by
  obtain ⟨matched, equiv, pair, _constitution, _occupied, reader, _marks, vectorSame⟩ :=
    actual_joint_tie_source_pair input single state target real unit targetUnit references W D
      fallback left right widthL heightL widthR heightR tie B a b rootedL rootedR
  let treeL := slotTree input single state target real unit targetUnit left
  let treeR := slotTree input single state target real unit targetUnit right
  let e := residualPathTreeEquivOfSameObservations pair charge rfl parentL parentR
  have preserved := residual_reference_vector_preserved input pair charge parentL parentR
    references vectorSame
  have outside : a ∉ B := not_mem_of_nodup_append_singleton rootedL.nodup
  let ranked : PrefixRankedWitnessIso e := Classical.choice (exists_prefixRankedWitnessIso e outside)
  obtain ⟨π, aut, fixed, entry, refs, support, witnesses⟩ :=
    prefix_ranked_references_fixed_aut input e outside references preserved ranked
  refine ⟨π, ranked.rank, aut, fixed, entry, refs, support, ?_⟩
  intro atom member
  obtain ⟨p, terminal, image, prefixLower, ordered⟩ := witnesses atom member
  refine ⟨p, terminal, ?_, prefixLower, ordered⟩
  have correspond := residualPathTreeEquivOfSameObservations_correspond pair charge rfl parentL parentR p
  have pathLabels := path_labels_of_correspondence treeL treeR
    (rawStateReader input state target) (rawStateReader input state target)
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1 matched.rightCanonical.1
    (fun x y address => by
      have equal : equiv.toEquiv x = y :=
        matched.rightAddressing.address_injective ((equiv.aligns x).trans address)
      exact (reader x).trans (congrArg
        (fun z => rawStateReader input state target (nodeSource input treeR z)) equal))
    B p.1 (e.toEquiv p).1 correspond
  simpa only [image] using pathLabels

end Actual
end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRankedWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRankedWitness.prefix_ranked_references_fixed_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRankedWitness.actual_joint_tie_prefix_ranked_references_fixed_aut_with_labels
