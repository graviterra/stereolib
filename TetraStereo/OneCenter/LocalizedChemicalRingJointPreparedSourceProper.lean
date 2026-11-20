import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedOccurrenceCorrection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! Source-proper physical reconstruction for actual prepared joint-key ties. The induction
uses only strictly smaller residual depth; each local correction retains the entire reference
list. The statement has no moving-reference refusal escape and no correction oracle premise. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProper

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointSelectedTieWitness (JointMatchedSymmetry)
open LocalizedChemicalRingJointPreparedCorrectionWitness
open LocalizedChemicalRingJointPreparedCorrectionLoop
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
theorem claim_step (n : Nat) (IH : ∀ m < n, Claim input mol single cfg m) :
    Claim input mol single cfg n := by
  intro node nodeDepth reached c _current data branch references reflected left right a b distinct w
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
  have pathPositive : 0 < p.1.length := List.length_pos_of_ne_nil p.2.nonempty
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
  have smaller : structuralDepth mol query < n := by
    rw [← nodeDepth]
    unfold structuralDepth
    omega
  rw [remaining] at refused
  obtain ⟨g, a', b', adjacentA, adjacentB, fixedG, supportG, referencesG, negativeG, properG⟩ :=
    occurrence_correction input mol agreement admissible supported single charge cfg calibrated
      n IH d query queryReached queryReal atomEq smaller
      (data.target.1.node.history.reverse ++ p.1.dropLast) outsideB
      (fun actual => by
        have extended := actual_boundary input mol single data actual p.1 queryEq.symm
        rw [extended, List.append_assoc, split])
      (fun actual => query_branch input mol single data actual p.1 queryEq.symm branch)
      references refused
  exact ⟨g, localCorrection_of_support input mol c node data W cfg d p.1 prefixLower higher
    outsideB g a' b' adjacentA adjacentB fixedG supportG referencesG negativeG properG⟩

include agreement admissible supported charge calibrated in
theorem claim_all (n : Nat) : Claim input mol single cfg n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  exact claim_step input mol agreement admissible supported single charge cfg calibrated n ih

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProper

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProper.claim_step
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProper.claim_all
