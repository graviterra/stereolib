import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionWitness
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMatchedExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedResidualDecoder
import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! The highest negative centre of an actual joint-key witness must refuse in its actual
smaller prepared evaluation. Successful labels would force the physical sign to be proper.
All accumulated references are fixed by the same map; the exact query, context and recursive
budget are preserved. This supplies the refusal step of the correction induction. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionStep

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedCorrectionWitness
open LocalizedChemicalRingJointPreparedMatchedExecution
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedChemicalRingBoundaryWitnessExecution (boundary_node_map)
open LocalizedChemicalRingBoundaryWitnessOrientation (witness_boundary)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedChemicalRingRankedCorrectionTransport (pending_witness_image)
open LocalizedChemicalRingRankedReconstruction (component_weaken)
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf)
open LocalizedChemicalRingRelabel (mapNode)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (descendant_reached)
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
  (references : List input.Atom)

variable {references} {a b : input.Atom}
  (W : CorrectionWitness input mol c node data (inputGeometry input) references a b)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (correction : input.detectedMultiCenterMolecule.Aut) (bound : Nat)
  (boundaryFixed : ∀ atom ∈ data.target.1.node.history,
    (correction : Equiv.Perm input.Atom) atom = atom)
  (lowFixed : ∀ atom, W.rank atom ≤ bound → (correction : Equiv.Perm input.Atom) atom = atom)
  (higherProper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
    bound < W.rank d.1 →
    relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d = 1)
  (referencesFixed : ∀ reference ∈ references, (correction : Equiv.Perm input.Atom) reference = reference)

include agreement admissible supported single reached calibrated boundaryFixed lowFixed higherProper
  referencesFixed in
/-- **One correction step.** All source signs are proper, or the highest negative center has an
actual descriptor refusal under the same reference, on its witness path. -/
theorem step :
    (∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d = 1) ∨
    ∃ (d : input.detectedMultiCenterMolecule.Center)
      (p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p}),
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 ∧
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d = -1 ∧
      W.rank d.1 ≤ bound ∧
      (∀ y ∈ p.1.dropLast, W.rank y < W.rank d.1) ∧
      (∀ y, InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
        d.1 y → y ≠ d.1 → W.rank d.1 < W.rank y) ∧
      (∀ other : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph data.target.1.node.history.reverse a other.1 →
        W.rank d.1 < W.rank other.1 →
        relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) other = 1) ∧
      preparedDescriptor? mol (jointOperations input mol)
        (structuralDepth mol node + node.history.length -
          (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length)
        (inputGeometry input) [] (references.map Fin.val)
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) = none := by
  let action := W.symmetry * correction
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
  obtain ⟨d, badD, maximal⟩ := bad.exists_max_image (fun d => W.rank d.1) nonempty
  obtain ⟨member, notProper⟩ := (Finset.mem_filter.mp badD).2
  obtain ⟨p, terminal, matched, prefixLower, higher⟩ := W.matched d member
  have pending : W.rank d.1 ≤ bound := by
    by_contra later
    exact notProper (higherProper d member (Nat.lt_of_not_ge later))
  have samePath : p.1.map (action : Equiv.Perm input.Atom) =
      p.1.map (W.symmetry : Equiv.Perm input.Atom) :=
    pending_witness_image W.rank bound W.symmetry correction lowFixed p.1 p.2.nonempty
      d.1 terminal prefixLower pending
  have maximalProper : ∀ other : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a other.1 →
      W.rank d.1 < W.rank other.1 →
      relativeSign input.detectedMultiCenterMolecule cfg action other = 1 := by
    intro other inSource later
    by_contra negative
    have upper := maximal other (Finset.mem_filter.mpr ⟨Finset.mem_univ other, inSource, negative⟩)
    omega
  have proper : ∀ other : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
        d.1 other.1 → other.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg action other = 1 := by
    intro other residual different
    have weakened := component_weaken
      (show data.target.1.node.history.reverse ⊆
        data.target.1.node.history.reverse ++ p.1.dropLast from
        fun _ h => List.mem_append_left _ h) residual
    exact maximalProper other ⟨member.1, member.2.trans weakened.2⟩ (higher other.1 residual different)
  have negative : relativeSign input.detectedMultiCenterMolecule cfg action d = -1 :=
    (relativeSign_eq_one_or_neg_one _ cfg action d).resolve_left notProper
  refine ⟨d, p, member, terminal, negative, pending, prefixLower, higher, maximalProper, ?_⟩
  cases observed : ((originalState input mol node (inputGeometry input) references).factAt?
      (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel with
  | none =>
      have executed := witness_label_execution input mol c node data (inputGeometry input)
        references reached W p.1 p.2
      exact executed.2.symm.trans observed
  | some label =>
      exfalso
      have fixed : ∀ atom ∈ data.target.1.node.history.reverse,
          (action : Equiv.Perm input.Atom) atom = atom := by
        intro atom present
        change (W.symmetry : Equiv.Perm input.Atom)
          ((correction : Equiv.Perm input.Atom) atom) = atom
        rw [boundaryFixed atom (List.mem_reverse.mp present),
          W.fixedHistory atom (List.mem_reverse.mp present)]
      have allFixed : ∀ reference ∈ references,
          (action : Equiv.Perm input.Atom) reference = reference := by
        intro reference member
        change (W.symmetry : Equiv.Perm input.Atom)
          ((correction : Equiv.Perm input.Atom) reference) = reference
        rw [referencesFixed reference member, W.fixedReferences reference member]
      have matchedAfter : ((originalState input mol node (inputGeometry input) references).factAt?
            (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel =
        ((originalState input mol node (inputGeometry input) references).factAt?
            (mapNode (relabelOf input (action : Equiv.Perm input.Atom))
              (rawPathNode data.target.1.root (boundaryPath data.target p.1)))).map factLabel := by
        rw [boundary_node_map single data.target action fixed p.1, samePath]
        exact matched
      obtain ⟨descent, _⟩ := W.execution p.1 p.2
      obtain ⟨child, edge, rest⟩ := descent
      have queryReached := descendant_reached (reached_child mol node child reached edge) rest
      obtain ⟨original, pulled⟩ := snapshot_matched_pullback input mol agreement admissible
        supported single action (structuralDepth mol node) (inputGeometry input) node
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) reached queryReached
        references allFixed matchedAfter label observed
      obtain ⟨atomEq, outside, carried⟩ := witness_boundary input single data.target a p.1 p.2
      rw [terminal] at atomEq outside
      have frame := LocalizedMarkedDetectedFrames.detected_frame mol input agreement admissible
        supported single d (rawPathNode data.target.1.root (boundaryPath data.target p.1))
        queryReached rfl atomEq.symm
      have sign := LocalizedChemicalRingJointPreparedResidualDecoder.relativeSign_eq_one_of_residual_signs
        input mol agreement admissible supported single cfg action calibrated
        (data.target.1.node.history.reverse ++ p.1.dropLast)
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) d.1 atomEq outside
        carried queryReached proper (jointOperations input mol) d atomEq.symm _ frame
        (structuralDepth mol node + node.history.length -
          (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length)
        [] (references.map Fin.val) label original pulled
      exact notProper sign

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionStep

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionStep.step
