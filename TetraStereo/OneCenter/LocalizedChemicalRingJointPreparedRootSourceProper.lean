import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! The root correction loop reuses the closed non-root induction at every residual query.
The structural root-to-query branch adapter is supplied to the local assembly lemma below. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceProper

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointSelectedTieWitness (JointMatchedSymmetry)
open LocalizedChemicalRingJointPreparedCorrectionWitness
open LocalizedChemicalRingJointPreparedCorrectionLoop
open LocalizedChemicalRingJointPreparedSourceProper (claim_all)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection
open LocalizedChemicalRingReferenceConsensusCorrectionInduction (actual_boundary query_branch)
open LocalizedChemicalRingBoundaryWitnessOrientation (witness_boundary)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath boundaryPath_raw_history)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedChemicalRingWitnessRawDescent (boundary_query_length_le)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (descendant_reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported charge calibrated in
theorem sourceProper_of_queryBranches
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (data : OccurrenceData input mol c node)
    (references : List input.Atom) (reflected : Bool) (left right : Fin 4)
    (a b : input.Atom) (distinct : a ≠ b)
    (w : JointMatchedSymmetry input single
      (sideState input mol node (inputGeometry input) references reflected)
      data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
      references left right a b)
    (queryBranch : ∀ (p : List input.Atom),
      ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p →
      ∀ (d : input.detectedMultiCenterMolecule.Center) (query : RawMolecule.CanonicalBranchNode),
      rawPathNode data.target.1.root (boundaryPath data.target p) = query →
      ∀ actual : OccurrenceData input mol d query, TiedRootBranch input actual.target) :
    SourceProper input cfg data.target references a b := by
  obtain ⟨W, _⟩ := exists_correctionWitness input mol c node data (inputGeometry input) references
    agreement admissible supported single reached reflected left right a b distinct w
  unfold SourceProper
  apply sourceProper_of_oracle input mol agreement admissible supported single c node data reached W
    cfg calibrated
  intro d p _member terminal prefixLower higher refused
  have boundaryFacts := witness_boundary input single data.target a p.1 p.2
  have atomEq : (rawPathNode data.target.1.root (boundaryPath data.target p.1)).atom = d.1.val := by
    rw [← terminal]
    exact boundaryFacts.1.symm
  have outsideB : d.1 ∉ data.target.1.node.history.reverse ++ p.1.dropLast := by
    rw [← terminal]
    exact boundaryFacts.2.1
  obtain ⟨⟨child, edge, descent⟩, _⟩ := W.execution p.1 p.2
  have queryReached : Reached mol (rawPathNode data.target.1.root (boundaryPath data.target p.1)) :=
    descendant_reached (reached_child mol node child reached edge) descent
  have queryReal : (rawPathNode data.target.1.root (boundaryPath data.target p.1)).provenance =
      RawMolecule.CanonicalNodeProvenance.realAtom := rfl
  have nodeLength : node.history.length = data.target.1.node.history.length := by
    have sound := (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).history
    rw [← sound, List.length_map]
  have queryLength : (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length =
      data.target.1.node.history.length + p.1.length := by
    rw [boundaryPath_raw_history single data.target p.1, List.length_map, List.length_append,
      List.length_reverse, Nat.add_comm]
  have queryBound := boundary_query_length_le input mol agreement single data.target data.real a
    p.1 p.2
  have split : p.1.dropLast ++ [d.1] = p.1 := by
    have whole := List.dropLast_append_getLast p.2.nonempty
    have last : p.1.getLast p.2.nonempty = d.1 := terminal
    rw [last] at whole
    exact whole
  generalize queryEq : rawPathNode data.target.1.root (boundaryPath data.target p.1) = query
    at atomEq queryReached queryReal queryLength queryBound refused
  have remaining : structuralDepth mol node + node.history.length - query.history.length =
      structuralDepth mol query := by
    unfold structuralDepth
    omega
  rw [remaining] at refused
  obtain ⟨g, a', b', adjacentA, adjacentB, fixedG, supportG, referencesG, negativeG, properG⟩ :=
    occurrence_correction input mol agreement admissible supported single charge cfg calibrated
      (structuralDepth mol query + 1)
      (fun n _ => claim_all input mol agreement admissible supported single charge cfg calibrated n)
      d query queryReached queryReal atomEq (Nat.lt_succ_self _)
      (data.target.1.node.history.reverse ++ p.1.dropLast) outsideB
      (fun actual => by
        have extended := actual_boundary input mol single data actual p.1 queryEq.symm
        rw [extended, List.append_assoc, split])
      (queryBranch p.1 p.2 d query queryEq)
      references refused
  exact ⟨g, localCorrection_of_support input mol c node data W cfg d p.1 prefixLower higher
    outsideB g a' b' adjacentA adjacentB fixedG supportG referencesG negativeG properG⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceProper

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceProper.sourceProper_of_queryBranches
