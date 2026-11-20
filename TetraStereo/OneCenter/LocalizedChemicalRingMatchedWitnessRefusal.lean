import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent
import TetraStereo.OneCenter.LocalizedChemicalRingMatchedOrientationObstruction
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
A missing matched witness is an ACTUAL refused recursive query. Selection of its first
child, the raw descent, and sufficient execution depth are all derived from the SAME
key-reconstructed symmetry and the finite molecular path. There is no assumed selected
reference or successful label, and no fabricated query or enlarged comparison window.

Consequently a physically incorrect reconstructed symmetry has a negative witness at
an actually refused query, with proper signs at all other residual centers derived by
finite maximality. This closes the missing-fact/execution join, not the construction of
the physical correcting symmetry. Input geometry and the isolated candidate are explicit.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingMovedSlotEligibility LocalizedChemicalRingWitnessRawDescent
open LocalizedChemicalRingMatchedOrientationObstruction LocalizedChemicalRingSelectedFactCompleteness
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedReachableConfigurations (reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends descendant_reached)
open LocalizedMarkedOperationEvaluator (tiedChildren mem_tiedChildren_actual)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
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

include agreement admissible supported reached distinct w in
/-- Actual selection, descent, and sufficient budget for any of this reconstruction's
residual witness paths. No observation of a successful descriptor is needed. -/
theorem matched_path_execution (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p) :
    ∃ child ∈ tiedChildren mol (sparseOperations input mol) [] node,
      Descends mol child (rawPathNode data.target.1.root (boundaryPath data.target p)) ∧
      (rawPathNode data.target.1.root (boundaryPath data.target p)).history.length ≤
        structuralDepth mol node + node.history.length := by
  have fresh : a ∉ data.target.1.node.history := by
    intro present
    exact distinct ((w.fixedHistory a present).symm.trans w.entry)
  obtain ⟨child, actualChild, atChild, _, descent⟩ :=
    actual_fresh_boundary_path_descent input mol agreement admissible supported single node reached
      _ data.target data.found data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
      left a w.leftCurrent w.leftReal fresh p valid
  have selected := matched_child_selected input mol agreement admissible supported single c node
    data reached _ reference left right a b distinct w child actualChild atChild
  have adequate := boundary_query_adequate input mol agreement single data.target data.real a p valid node
  exact ⟨child, selected, descent, adequate⟩

include agreement admissible supported reached distinct w in
/-- Derives the operational premises of absence-to-refusal from the matched molecular
symmetry. The actual structural depth suffices; no caller-supplied budget is needed. -/
theorem missing_refuses (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p)
    (absent : ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
      (structuralDepth mol node) (inputGeometry input) node reference.val).factAt?
        (rawPathNode data.target.1.root (boundaryPath data.target p))).map factLabel = none) :
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      (structuralDepth mol node + node.history.length -
        (rawPathNode data.target.1.root (boundaryPath data.target p)).history.length)
      (inputGeometry input) [] (some reference.val)
      (rawPathNode data.target.1.root (boundaryPath data.target p)) = none := by
  obtain ⟨child, selected, descent, adequate⟩ := matched_path_execution input mol agreement
    admissible supported single c node data reached reference left right a b distinct w p valid
  exact candidate_absence_refusal input mol (structuralDepth mol node) (inputGeometry input)
    node child (rawPathNode data.target.1.root (boundaryPath data.target p)) reference.val
    selected descent adequate absent

include agreement admissible supported reached distinct w in
/-- At a detected witness the refused query supplies an actual generated-state key tie
under the original inherited reference. Its frame and reachability are constructed. -/
theorem missing_witness_key_tie (cfg : input.detectedMultiCenterMolecule.Configuration)
    (d : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p)
    (terminal : pathTerminal p valid.nonempty = d.1)
    (absent : ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
      (structuralDepth mol node) (inputGeometry input) node reference.val).factAt?
        (rawPathNode data.target.1.root (boundaryPath data.target p))).map factLabel = none) :
    let query := rawPathNode data.target.1.root (boundaryPath data.target p)
    let remaining := structuralDepth mol node + node.history.length - query.history.length
    ∃ (actual : OccurrenceData input mol d query) (reflected : Bool) (i j : Fin 4),
      LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
        (observedGeometry input reflected) [] (some reference.val) query
        (generated input mol query remaining reflected) = none ∧ i ≠ j ∧
      markedKeys input mol single d query actual
        (generated input mol query remaining reflected reference.val) reference i =
      markedKeys input mol single d query actual
        (generated input mol query remaining reflected reference.val) reference j := by
  obtain ⟨child, selected, descent, _⟩ := matched_path_execution input mol agreement
    admissible supported single c node data reached reference left right a b distinct w p valid
  have queryReached := descendant_reached
    (reached_child mol node child reached (mem_tiedChildren_actual mol _ [] node child selected)) descent
  have current := (LocalizedChemicalRingBoundaryWitnessOrientation.witness_boundary
    input single data.target a p valid).1
  rw [terminal] at current
  have refused := missing_refuses input mol agreement admissible supported single c node data reached
    reference left right a b distinct w p valid absent
  exact LocalizedChemicalRingInheritedReferenceTie.reached_descriptor_original_reference_tie
    input mol agreement admissible supported single cfg d calibrated _ queryReached rfl current.symm
    _ reference refused

include agreement admissible supported reached distinct in
/-- No unproved selection, descent, or deeper-physical-sign premise remains in this
reduction. Either the matched symmetry is source-proper, or its maximal bad witness is
an actual refused descriptor query at the original inherited reference. -/
theorem proper_or_actual_refusal (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d) :
    (∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg w.symmetry d = 1) ∨
    ∃ (d : input.detectedMultiCenterMolecule.Center)
      (p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p}),
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 ∧
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg w.symmetry d = -1 ∧
      LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
        (structuralDepth mol node + node.history.length -
          (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length)
        (inputGeometry input) [] (some reference.val)
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) = none ∧
      (∀ other : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
          d.1 other.1 → other.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg w.symmetry other = 1) := by
  rcases proper_or_missing_witness input mol agreement admissible supported single cfg calibrated
      data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
      reference left right a b (structuralDepth mol node) node reached w with allProper | bad
  · exact Or.inl allProper
  · obtain ⟨d, p, member, terminal, negative, absent, residual⟩ := bad
    exact Or.inr ⟨d, p, member, terminal, negative,
      missing_refuses input mol agreement admissible supported single c node data reached
        reference left right a b distinct w p.1 p.2 absent, residual⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal.missing_refuses
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal.matched_path_execution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal.missing_witness_key_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMatchedWitnessRefusal.proper_or_actual_refusal
