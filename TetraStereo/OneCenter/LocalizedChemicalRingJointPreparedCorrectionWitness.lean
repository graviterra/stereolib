import TetraStereo.OneCenter.LocalizedChemicalRingJointSelectedTieWitness
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReflection
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Correction witnesses for the actual prepared recursion. A joint tie on either geometry
produces one all-reference-fixing molecular map and exact optional fact matches in the original
generated snapshot. Every realizing path is an actual canonical descent and uses a smaller
descriptor budget. No desired label, successful descriptor or physical sign is supplied.
This is execution data for the physical correction induction, not that induction's conclusion. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionWitness

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointSelectedTieWitness
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointPreparedReflection (generated_labels_of_mirror)
open LocalizedChemicalRingJointPreparedLabelExecution
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingReferenceConsensusCorrectionWitness
  (refineRank refineRank_lt refineRank_injective)
open LocalizedChemicalRingWitnessRawDescent
  (actual_fresh_boundary_path_descent boundary_query_adequate)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedGenericMarkedRecalculation (Geometry mirror structuralDepth)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (geom : Geometry) (references : List input.Atom)

abbrev originalState : OccurrenceAuxState :=
  generated input mol (structuralDepth mol node) geom node references

abbrev sideState (reflected : Bool) : OccurrenceAuxState :=
  generated input mol (structuralDepth mol node)
    (if reflected then mirror geom else geom) node references

/-- One reconstructed map and rank, with all facts read in the actual same-context snapshot. -/
structure CorrectionWitness (a b : input.Atom) where
  symmetry : input.detectedMultiCenterMolecule.Aut
  rank : input.Atom → Nat
  rankInjective : Function.Injective rank
  fixedHistory : ∀ atom ∈ data.target.1.node.history,
    (symmetry : Equiv.Perm input.Atom) atom = atom
  entry : (symmetry : Equiv.Perm input.Atom) a = b
  fixedReferences : ∀ reference ∈ references,
    (symmetry : Equiv.Perm input.Atom) reference = reference
  support : ∀ atom,
    ¬ InComponent input.moleculeGraph data.target.1.node.history.reverse a atom →
    ¬ InComponent input.moleculeGraph data.target.1.node.history.reverse b atom →
    (symmetry : Equiv.Perm input.Atom) atom = atom
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
      ((originalState input mol node geom references).factAt?
        (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel =
      ((originalState input mol node geom references).factAt?
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

include agreement admissible supported reached in
/-- Actual joint matches on either geometry give a correction witness on the original
geometry, with the same permutation, the same accumulated references and an injective rank. -/
theorem exists_correctionWitness (reflected : Bool) (left right : Fin 4)
    (a b : input.Atom) (distinct : a ≠ b)
    (w : JointMatchedSymmetry input single (sideState input mol node geom references reflected)
      data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
      references left right a b) :
    ∃ W : CorrectionWitness input mol c node data geom references a b,
      (W.symmetry : Equiv.Perm input.Atom) = w.symmetry := by
  refine ⟨{
    symmetry := w.symmetry
    rank := refineRank w.rank
    rankInjective := refineRank_injective w.rank
    fixedHistory := w.fixedHistory
    entry := w.entry
    fixedReferences := w.fixedReferences
    support := w.support
    execution := ?_
    matched := ?_ }, rfl⟩
  · intro p valid
    have fresh : a ∉ data.target.1.node.history := by
      intro member
      exact distinct ((w.fixedHistory a member).symm.trans w.entry)
    obtain ⟨child, edge, _, _, descent⟩ :=
      actual_fresh_boundary_path_descent input mol agreement admissible supported single
        node reached _ data.target data.found data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left a
        w.leftCurrent w.leftReal fresh p valid
    exact ⟨⟨child, edge, descent⟩,
      boundary_query_adequate input mol agreement single data.target data.real a p valid node⟩
  · intro d member
    obtain ⟨p, terminal, _, labels, lower, higher⟩ := w.matched d member
    refine ⟨p, terminal, ?_, fun y present => refineRank_lt w.rank (lower y present),
      fun y residual different => refineRank_lt w.rank (higher y residual different)⟩
    cases reflected with
    | false => exact labels
    | true =>
        exact generated_labels_of_mirror input mol (structuralDepth mol node) geom node
          _ _ references labels

include reached in
/-- A witness reads an actual smaller recursive call, including the refusal case. -/
theorem witness_label_execution {a b : input.Atom}
    (W : CorrectionWitness input mol c node data geom references a b)
    (p : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p) :
    let query := rawPathNode data.target.1.root (boundaryPath data.target p)
    let remaining := structuralDepth mol node + node.history.length - query.history.length
    remaining < structuralDepth mol node ∧
      ((originalState input mol node geom references).factAt? query).map factLabel =
        preparedDescriptor? mol (jointOperations input mol) remaining geom []
          (references.map Fin.val) query := by
  obtain ⟨descent, adequate⟩ := W.execution p valid
  exact ⟨residual_depth_lt _ descent adequate,
    generated_label_eq_descriptor input mol (structuralDepth mol node) geom node _ references
      reached descent adequate⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionWitness.exists_correctionWitness
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionWitness.witness_label_execution
