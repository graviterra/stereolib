import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCrossGeometryExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The exact cross-geometry witness required by mirror correction. Its matched fields must
come from actual comparison-key reconstruction. At a highest center of wrong physical sense,
the matching actual observations force refusal; otherwise the signed decoder contradicts
that sense. The current theorem does not assume or establish the key-to-witness producer. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorCorrectionWitness

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedCorrectionWitness (originalState)
open LocalizedChemicalRingJointPreparedLabelExecution (generated_label_eq_descriptor)
open LocalizedChemicalRingJointPreparedCrossGeometryExecution (snapshot_cross_matched_pullback)
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
open LocalizedMarkedTerminalReferenceScope (StrictDescendant descendant_reached)
open LocalizedGenericMarkedRecalculation (structuralDepth mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (references : List input.Atom)

/-- One reconstructed map, with observations on the original source and mirrored image. -/
structure MirrorWitness (a b : input.Atom) where
  symmetry : input.detectedMultiCenterMolecule.Aut
  rank : input.Atom → Nat
  rankInjective : Function.Injective rank
  fixedHistory : ∀ atom ∈ data.target.1.node.history,
    (symmetry : Equiv.Perm input.Atom) atom = atom
  entry : (symmetry : Equiv.Perm input.Atom) a = b
  fixedReferences : ∀ atom ∈ references, (symmetry : Equiv.Perm input.Atom) atom = atom
  execution : ∀ p : List input.Atom,
    ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p →
    StrictDescendant mol node (rawPathNode data.target.1.root (boundaryPath data.target p)) ∧
      (rawPathNode data.target.1.root (boundaryPath data.target p)).history.length ≤
        structuralDepth mol node + node.history.length
  matched : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
    ∃ p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p},
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      ((originalState input mol node (inputGeometry input) references).factAt?
        (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel =
      ((originalState input mol node (mirror (inputGeometry input)) references).factAt?
        (rawPathNode data.target.1.root
          (boundaryPath data.target (p.1.map (symmetry : Equiv.Perm input.Atom))))).map factLabel ∧
      (∀ y ∈ p.1.dropLast, rank y < rank d.1) ∧
      ∀ y, InComponent input.moleculeGraph
        (data.target.1.node.history.reverse ++ p.1.dropLast) d.1 y →
        y ≠ d.1 → rank d.1 < rank y

variable (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded) (reached : Reached mol node)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported single reached calibrated in
/-- A highest wrong-sense matched center has an actual smaller-call refusal. In particular,
successful pseudo labels cannot be incorrectly interpreted as a proper spatial sign. -/
theorem refusal_at_wrong_sign {a b : input.Atom}
    (W : MirrorWitness input mol c node data references a b)
    (correction : input.detectedMultiCenterMolecule.Aut)
    (d : input.detectedMultiCenterMolecule.Center)
    (member : InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1)
    (boundaryFixed : ∀ atom ∈ data.target.1.node.history,
      (correction : Equiv.Perm input.Atom) atom = atom)
    (lowFixed : ∀ atom, W.rank atom ≤ W.rank d.1 →
      (correction : Equiv.Perm input.Atom) atom = atom)
    (referencesFixed : ∀ atom ∈ references, (correction : Equiv.Perm input.Atom) atom = atom)
    (wrong : relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d ≠ -1)
    (higherNegative : ∀ other : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a other.1 →
      W.rank d.1 < W.rank other.1 →
      relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) other = -1) :
    ∃ p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p},
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      (∀ y ∈ p.1.dropLast, W.rank y < W.rank d.1) ∧
      (∀ y, InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
        d.1 y → y ≠ d.1 → W.rank d.1 < W.rank y) ∧
      preparedDescriptor? mol (jointOperations input mol)
        (structuralDepth mol node + node.history.length -
          (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length)
        (inputGeometry input) [] (references.map Fin.val)
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) = none := by
  let action := W.symmetry * correction
  obtain ⟨p, terminal, matched, prefixLower, higher⟩ := W.matched d member
  refine ⟨p, terminal, prefixLower, higher, ?_⟩
  obtain ⟨descent, adequate⟩ := W.execution p.1 p.2
  cases observed : ((originalState input mol node (inputGeometry input) references).factAt?
      (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel with
  | none =>
      exact (generated_label_eq_descriptor input mol (structuralDepth mol node)
        (inputGeometry input) node _ references reached descent adequate).symm.trans observed
  | some label =>
      exfalso
      have samePath : p.1.map (action : Equiv.Perm input.Atom) =
          p.1.map (W.symmetry : Equiv.Perm input.Atom) :=
        pending_witness_image W.rank (W.rank d.1) W.symmetry correction lowFixed p.1 p.2.nonempty
          d.1 terminal prefixLower le_rfl
      have fixed : ∀ atom ∈ data.target.1.node.history.reverse,
          (action : Equiv.Perm input.Atom) atom = atom := by
        intro atom present
        change (W.symmetry : Equiv.Perm input.Atom)
          ((correction : Equiv.Perm input.Atom) atom) = atom
        rw [boundaryFixed atom (List.mem_reverse.mp present),
          W.fixedHistory atom (List.mem_reverse.mp present)]
      have allFixed : ∀ atom ∈ references, (action : Equiv.Perm input.Atom) atom = atom := by
        intro atom present
        change (W.symmetry : Equiv.Perm input.Atom)
          ((correction : Equiv.Perm input.Atom) atom) = atom
        rw [referencesFixed atom present, W.fixedReferences atom present]
      have matchedAfter : ((originalState input mol node (inputGeometry input) references).factAt?
            (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel =
          ((originalState input mol node (mirror (inputGeometry input)) references).factAt?
            (mapNode (relabelOf input (action : Equiv.Perm input.Atom))
              (rawPathNode data.target.1.root (boundaryPath data.target p.1)))).map factLabel := by
        rw [boundary_node_map single data.target action fixed p.1, samePath]
        exact matched
      obtain ⟨child, edge, rest⟩ := descent
      have queryReached := descendant_reached (reached_child mol node child reached edge) rest
      obtain ⟨original, pulled⟩ := snapshot_cross_matched_pullback input mol agreement admissible
        supported single action (structuralDepth mol node) (inputGeometry input)
        (mirror (inputGeometry input)) node
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) reached queryReached
        references allFixed matchedAfter label observed
      obtain ⟨atomEq, outside, carried⟩ := witness_boundary input single data.target a p.1 p.2
      rw [terminal] at atomEq outside
      have frame := LocalizedMarkedDetectedFrames.detected_frame mol input agreement admissible
        supported single d (rawPathNode data.target.1.root (boundaryPath data.target p.1))
        queryReached rfl atomEq.symm
      have residual : ∀ other : input.detectedMultiCenterMolecule.Center,
          InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
            d.1 other.1 → other.1 ≠ d.1 →
          relativeSign input.detectedMultiCenterMolecule cfg action other = -1 := by
        intro other present different
        have weakened := component_weaken
          (show data.target.1.node.history.reverse ⊆
            data.target.1.node.history.reverse ++ p.1.dropLast from
            fun _ h => List.mem_append_left _ h) present
        exact higherNegative other ⟨member.1, member.2.trans weakened.2⟩
          (higher other.1 present different)
      exact wrong
        (LocalizedChemicalRingJointPreparedSignedResidualDecoder.relativeSign_eq_neg_one_of_residual_mirror_signs
          input mol agreement admissible supported single cfg action calibrated
          (data.target.1.node.history.reverse ++ p.1.dropLast)
          (rawPathNode data.target.1.root (boundaryPath data.target p.1)) d.1 atomEq outside carried
          queryReached residual (jointOperations input mol) d atomEq.symm _ frame
          (structuralDepth mol node + node.history.length -
            (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length)
          [] (references.map Fin.val) label original pulled)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorCorrectionWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorCorrectionWitness.refusal_at_wrong_sign
