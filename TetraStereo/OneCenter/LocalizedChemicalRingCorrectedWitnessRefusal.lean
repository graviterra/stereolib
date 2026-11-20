import TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal
import TetraStereo.OneCenter.LocalizedChemicalRingShiftedReferenceWitness
import TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter.LocalizedChemicalRingCorrectedWitnessRefusal

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingMatchedWitnessRefusal LocalizedChemicalRingShiftedReferenceWitness
open LocalizedChemicalRingRankedCorrectionTransport LocalizedChemicalRingRankedReconstruction
open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback (flipDescriptorBy)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut actual_covariant)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (reference : input.Atom) (left right : Fin 4) (a b : input.Atom) (distinct : a ≠ b)
  (w : MatchedSymmetry input single
    (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
      (structuralDepth mol node) (inputGeometry input) node reference.val)
    data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
    reference left right a b)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (correction : input.detectedMultiCenterMolecule.Aut) (bound : Nat)
  (boundaryFixed : ∀ atom ∈ data.target.1.node.history,
    (correction : Equiv.Perm input.Atom) atom = atom)
  (lowFixed : ∀ atom, w.rank atom ≤ bound → (correction : Equiv.Perm input.Atom) atom = atom)
  (higherProper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
    bound < w.rank d.1 →
    relativeSign input.detectedMultiCenterMolecule cfg (w.symmetry * correction) d = 1)

include agreement admissible supported reached distinct calibrated boundaryFixed lowFixed
  higherProper in
/-- The exact remaining failure after correction is derived from actual keys and actual
execution. In the successful-label branch, reference sensitivity is a conclusion. -/
theorem proper_or_refusal_or_reference_change :
    (∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg (w.symmetry * correction) d = 1) ∨
    ∃ (d : input.detectedMultiCenterMolecule.Center)
      (p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p}),
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 ∧
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg (w.symmetry * correction) d = -1 ∧
      w.rank d.1 ≤ bound ∧
      (∀ other : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
          d.1 other.1 → other.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg (w.symmetry * correction) other = 1) ∧
      (let query := rawPathNode data.target.1.root (boundaryPath data.target p.1)
       let remaining := structuralDepth mol node + node.history.length - query.history.length
       LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
           remaining (inputGeometry input) [] (some reference.val) query = none ∨
       ∃ label : LocalizedTetrahedralRSPseudoDescriptor,
         LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
             remaining (inputGeometry input) [] (some reference.val) query = some label ∧
         LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
             remaining (inputGeometry input) []
             (some (((w.symmetry * correction : input.detectedMultiCenterMolecule.Aut) :
               Equiv.Perm input.Atom).symm reference).val) query =
             flipDescriptorBy (-1) (some label)) := by
  let action := w.symmetry * correction
  by_cases allProper : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg action d = 1
  · exact Or.inl allProper
  right
  let bad := Finset.univ.filter fun d : input.detectedMultiCenterMolecule.Center =>
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg action d ≠ 1
  have nonempty : bad.Nonempty := by
    push_neg at allProper
    obtain ⟨d, member, negative⟩ := allProper
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, member, negative⟩⟩
  obtain ⟨d, badD, maximal⟩ := bad.exists_max_image (fun d => w.rank d.1) nonempty
  obtain ⟨member, notProper⟩ := (Finset.mem_filter.mp badD).2
  obtain ⟨p, terminal, _, matched, prefixLower, higher⟩ := w.matched d member
  have pending : w.rank d.1 ≤ bound := by
    by_contra later
    exact notProper (higherProper d member (Nat.lt_of_not_ge later))
  have samePath : p.1.map (action : Equiv.Perm input.Atom) =
      p.1.map (w.symmetry : Equiv.Perm input.Atom) :=
    pending_witness_image w.rank bound w.symmetry correction lowFixed p.1 p.2.nonempty
      d.1 terminal prefixLower pending
  have proper : ∀ other : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
        d.1 other.1 → other.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg action other = 1 := by
    intro other residual different
    by_contra negative
    have weakened := component_weaken
      (show data.target.1.node.history.reverse ⊆
        data.target.1.node.history.reverse ++ p.1.dropLast from
        fun _ h => List.mem_append_left _ h) residual
    have inSource : InComponent input.moleculeGraph data.target.1.node.history.reverse a other.1 :=
      ⟨member.1, member.2.trans weakened.2⟩
    have upper := maximal other
      (Finset.mem_filter.mpr ⟨Finset.mem_univ other, inSource, negative⟩)
    have lower := higher other.1 residual different
    omega
  have negative : relativeSign input.detectedMultiCenterMolecule cfg action d = -1 :=
    (relativeSign_eq_one_or_neg_one _ cfg action d).resolve_left notProper
  refine ⟨d, p, member, terminal, negative, pending, proper, ?_⟩
  dsimp only
  cases observed : ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
      (structuralDepth mol node) (inputGeometry input) node reference.val).factAt?
        (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel with
  | none =>
      exact Or.inl (missing_refuses input mol agreement admissible supported single c node data
        reached reference left right a b distinct w p.1 p.2 observed)
  | some label =>
      have fixed : ∀ atom ∈ data.target.1.node.history.reverse,
          (action : Equiv.Perm input.Atom) atom = atom := by
        intro atom present
        change (w.symmetry : Equiv.Perm input.Atom)
          ((correction : Equiv.Perm input.Atom) atom) = atom
        rw [boundaryFixed atom (List.mem_reverse.mp present),
          w.fixedHistory atom (List.mem_reverse.mp present)]
      have matchedAfter : ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
          (structuralDepth mol node) (inputGeometry input) node reference.val).factAt?
            (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel =
        ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
          (structuralDepth mol node) (inputGeometry input) node reference.val).factAt?
            (rawPathNode data.target.1.root
              (boundaryPath data.target (p.1.map (action : Equiv.Perm input.Atom))))).map factLabel := by
        rw [samePath]
        exact matched
      have sym := structuralSymmetry_of_aut input mol agreement admissible supported action
      have cov := actual_covariant input mol agreement admissible supported single action
      have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
      have mapped := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1
        admissible.1.2 rawSingle cov
      have result := shifted_descriptor_of_snapshot_match input mol agreement admissible supported
        single action cfg calibrated LocalizedChemicalRingInheritedFallback.rawStep? mapped
        (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations input mol))
        (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations input mol))
        data.target reference a fixed p.1 p.2 d terminal (structuralDepth mol node) node reached
        matchedAfter label observed proper
      rw [negative] at result
      right
      refine ⟨label, ?_⟩
      simpa only [LocalizedChemicalRingInheritedFallback.descriptor?, rawPathNode,
        List.length_map, List.length_reverse, List.length_cons, action] using result

include agreement admissible supported reached distinct calibrated boundaryFixed lowFixed
  higherProper in
/-- The ordinary correction case closes without supplying fresh label matches. The
original-reference fixation eliminates the derived two-context obstruction. -/
theorem proper_or_actual_refusal_of_reference_fixed
    (referenceFixed : (correction : Equiv.Perm input.Atom) reference = reference) :
    (∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg (w.symmetry * correction) d = 1) ∨
    ∃ (d : input.detectedMultiCenterMolecule.Center)
      (p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p}),
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 ∧
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg (w.symmetry * correction) d = -1 ∧
      w.rank d.1 ≤ bound ∧
      (∀ other : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
          d.1 other.1 → other.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg (w.symmetry * correction) other = 1) ∧
      (let query := rawPathNode data.target.1.root (boundaryPath data.target p.1)
       LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
         (structuralDepth mol node + node.history.length - query.history.length)
         (inputGeometry input) [] (some reference.val) query = none) := by
  rcases proper_or_refusal_or_reference_change input mol agreement admissible supported single
    c node data reached reference left right a b distinct w cfg calibrated correction bound
    boundaryFixed lowFixed higherProper with allProper | bad
  · exact Or.inl allProper
  obtain ⟨d, p, member, terminal, negative, pending, proper, failure⟩ := bad
  refine Or.inr ⟨d, p, member, terminal, negative, pending, proper, ?_⟩
  rcases failure with refused | ⟨label, original, shifted⟩
  · exact refused
  · have inverse : (((w.symmetry * correction : input.detectedMultiCenterMolecule.Aut) :
        Equiv.Perm input.Atom).symm reference) = reference :=
      inverse_reference_two_port w.symmetry correction reference reference
        w.fixedReference referenceFixed
    rw [inverse, original] at shifted
    have impossible := LocalizedChemicalRingOrientationReadback.flipDescriptorBy_some_eq
      (-1) (Or.inr rfl) label shifted.symm
    norm_num at impossible

end
end TetraStereo.OneCenter.LocalizedChemicalRingCorrectedWitnessRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCorrectedWitnessRefusal.proper_or_refusal_or_reference_change
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCorrectedWitnessRefusal.proper_or_actual_refusal_of_reference_fixed
