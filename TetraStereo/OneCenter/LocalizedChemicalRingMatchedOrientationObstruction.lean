import TetraStereo.OneCenter.LocalizedChemicalRingSelectedRefusalWitness
import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation
import TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Close the successful-label part of the ranked physical argument without assuming
properness at deeper centers. For the SAME actual-key-derived matched symmetry, either
every source-component sign is proper, or a maximal-rank negative center has an absent
generated witness label and all its other residual centers are already proper.

An absent fact is not called an evaluator refusal: the witnessed path may not be among
the paths selected by `underWith`. That execution-selection bridge remains separate.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingMatchedOrientationObstruction

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingSelectedRefusalWitness LocalizedChemicalRingRankedReconstruction
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessOrientation
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut actual_covariant)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

theorem proper_or_missing_witness
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (reference : input.Atom) (left right : Fin 4) (a b : input.Atom)
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (w : MatchedSymmetry input single
      (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol depth
        (inputGeometry input) source reference.val)
      target real unit targetUnit reference left right a b) :
    (∀ c : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph target.1.node.history.reverse a c.1 →
      relativeSign input.detectedMultiCenterMolecule cfg w.symmetry c = 1) ∨
    ∃ (c : input.detectedMultiCenterMolecule.Center)
      (p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph target.1.node.history.reverse a p}),
      InComponent input.moleculeGraph target.1.node.history.reverse a c.1 ∧
      pathTerminal p.1 p.2.nonempty = c.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg w.symmetry c = -1 ∧
      ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol depth
        (inputGeometry input) source reference.val).factAt?
          (rawPathNode target.1.root (boundaryPath target p.1))).map factLabel = none ∧
      (∀ d : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph (target.1.node.history.reverse ++ p.1.dropLast) c.1 d.1 →
        d.1 ≠ c.1 → relativeSign input.detectedMultiCenterMolecule cfg w.symmetry d = 1) := by
  by_cases allProper : ∀ c : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph target.1.node.history.reverse a c.1 →
      relativeSign input.detectedMultiCenterMolecule cfg w.symmetry c = 1
  · exact Or.inl allProper
  · right
    let bad := Finset.univ.filter fun c : input.detectedMultiCenterMolecule.Center =>
      InComponent input.moleculeGraph target.1.node.history.reverse a c.1 ∧
        relativeSign input.detectedMultiCenterMolecule cfg w.symmetry c ≠ 1
    have nonempty : bad.Nonempty := by
      push_neg at allProper
      obtain ⟨c, member, negative⟩ := allProper
      exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, member, negative⟩⟩
    obtain ⟨c, badC, maximal⟩ := bad.exists_max_image (fun c => w.rank c.1) nonempty
    obtain ⟨member, notProper⟩ := (Finset.mem_filter.mp badC).2
    obtain ⟨p, terminal, _, matched, _, higher⟩ := w.matched c member
    have proper : ∀ d : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph (target.1.node.history.reverse ++ p.1.dropLast) c.1 d.1 →
        d.1 ≠ c.1 → relativeSign input.detectedMultiCenterMolecule cfg w.symmetry d = 1 := by
      intro d residual different
      by_contra negative
      have weakened := component_weaken
        (show target.1.node.history.reverse ⊆ target.1.node.history.reverse ++ p.1.dropLast from
          fun _ h => List.mem_append_left _ h) residual
      have inSource : InComponent input.moleculeGraph target.1.node.history.reverse a d.1 :=
        ⟨member.1, member.2.trans weakened.2⟩
      have bound := maximal d (Finset.mem_filter.mpr ⟨Finset.mem_univ d, inSource, negative⟩)
      have later := higher d.1 residual different
      omega
    have negative : relativeSign input.detectedMultiCenterMolecule cfg w.symmetry c = -1 :=
      (relativeSign_eq_one_or_neg_one _ cfg w.symmetry c).resolve_left notProper
    refine ⟨c, p, member, terminal, negative, ?_, proper⟩
    cases observed : ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep?
        input mol depth (inputGeometry input) source reference.val).factAt?
          (rawPathNode target.1.root (boundaryPath target p.1))).map factLabel with
    | none => rfl
    | some label =>
      have sym := structuralSymmetry_of_aut input mol agreement admissible supported w.symmetry
      have cov := actual_covariant input mol agreement admissible supported single w.symmetry
      have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
      have stepMap := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1
        admissible.1.2 rawSingle cov
      have sign := relativeSign_of_snapshot_match input mol agreement admissible supported single
        cfg w.symmetry calibrated LocalizedChemicalRingInheritedFallback.rawStep? stepMap
        (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations input mol))
        (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations input mol))
        target reference a (fun atom h => w.fixedHistory atom (List.mem_reverse.mp h))
        w.fixedReference p.1 p.2 c terminal depth source sourceReached matched label observed proper
      exact False.elim (notProper sign)

end
end TetraStereo.OneCenter.LocalizedChemicalRingMatchedOrientationObstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMatchedOrientationObstruction.proper_or_missing_witness
