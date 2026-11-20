import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorCorrectionWitness
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceProper
import TetraStereo.OneCenter.LocalizedChemicalRingSignedCorrectionLoop
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Mirror correction uses the already closed non-root physical induction. An actual refused
query supplies an odd local correction; the signed finite rank loop makes every source-center
sign negative while retaining all reference identities. The input cross-geometry witness and
structural query-branch adapter remain explicit here; their actual-key producer is separate. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceMirror

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointPreparedMirrorCorrectionWitness
open LocalizedChemicalRingJointPreparedSourceProper (claim_all)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection (occurrence_correction)
open LocalizedChemicalRingSignedCorrectionLoop (exists_signed_source_map)
open LocalizedChemicalRingRankedCorrectionTransport (support_fixes_low witness_member_rank_le)
open LocalizedChemicalRingReferenceConsensusCorrectionInduction (actual_boundary)
open LocalizedChemicalRingBoundaryWitnessOrientation (witness_boundary)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath boundaryPath_raw_history)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedChemicalRingWitnessRawDescent (boundary_query_length_le)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (descendant_reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported single charge calibrated in
/-- Cross-geometry witness observations produce one uniformly mirror source map, with no
correction oracle, auxiliary rigidity, or assumed signs at previously unlabelled centers. -/
theorem sourceMirror_of_queryBranches
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (data : OccurrenceData input mol c node)
    (references : List input.Atom) (a b : input.Atom)
    (W : MirrorWitness input mol c node data references a b)
    (queryBranch : ∀ p : List input.Atom,
      ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p →
      ∀ (d : input.detectedMultiCenterMolecule.Center) (query : RawMolecule.CanonicalBranchNode),
      rawPathNode data.target.1.root (boundaryPath data.target p) = query →
      ∀ actual : OccurrenceData input mol d query, TiedRootBranch input actual.target) :
    ∃ F : input.detectedMultiCenterMolecule.Aut,
      (∀ atom ∈ data.target.1.node.history, (F : Equiv.Perm input.Atom) atom = atom) ∧
      (F : Equiv.Perm input.Atom) a = b ∧
      (∀ atom ∈ references, (F : Equiv.Perm input.Atom) atom = atom) ∧
      ∀ d : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg F d = -1 := by
  have repairs : LocalizedChemicalRingSignedCorrectionLoop.Repairable
      input.detectedMultiCenterMolecule cfg data.target.1.node.history.reverse references a
      W.rank W.symmetry (-1) := by
    intro correction d boundary low fixedReferences _entryFixed member wrong higherNegative
    obtain ⟨p, terminal, prefixLower, higher, refused⟩ :=
      refusal_at_wrong_sign input mol c node data references agreement admissible supported single
        reached cfg calibrated W correction d member
        (fun atom present => boundary atom (List.mem_reverse.mpr present)) low fixedReferences
        wrong higherNegative
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
    obtain ⟨g, left, right, edgeL, edgeR, fixedG, supportG, referencesG, negativeG, properG⟩ :=
      occurrence_correction input mol agreement admissible supported single charge cfg calibrated
        (structuralDepth mol query + 1)
        (fun n _ => claim_all input mol agreement admissible supported single charge cfg calibrated n)
        d query queryReached queryReal atomEq (Nat.lt_succ_self _)
        (data.target.1.node.history.reverse ++ p.1.dropLast) outsideB
        (fun actual => by
          have extended := actual_boundary input mol single data actual p.1 queryEq.symm
          rw [extended, List.append_assoc, split])
        (queryBranch p.1 p.2 d query queryEq) references refused
    have gLow : ∀ atom, W.rank atom ≤ W.rank d.1 → (g : Equiv.Perm input.Atom) atom = atom :=
      support_fixes_low input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
        W.rank d.1 left right outsideB edgeL edgeR higher g supportG
    have entryRank : W.rank a ≤ W.rank d.1 :=
      witness_member_rank_le W.rank p.1 p.2.nonempty d.1 terminal prefixLower a
        (List.mem_of_mem_head? (Option.mem_def.mpr p.2.head))
    refine ⟨g, ?_, gLow, referencesG, gLow a entryRank, negativeG, ?_⟩
    · intro atom present
      exact fixedG atom (List.mem_append_left _ (List.mem_append_left _ present))
    · intro other inSource later
      apply properG
      intro present
      rcases List.mem_append.mp present with inBoundary | isCenter
      · rcases List.mem_append.mp inBoundary with inHistory | inPrefix
        · exact inComponent_not_mem input.moleculeGraph inSource inHistory
        · have lower := prefixLower other.1 inPrefix
          omega
      · have same : other.1 = d.1 := List.mem_singleton.mp isCenter
        rw [same] at later
        exact Nat.lt_irrefl _ later
  obtain ⟨F, fixedF, referencesF, entryF, mirrorF⟩ := exists_signed_source_map
    input.detectedMultiCenterMolecule cfg data.target.1.node.history.reverse references a
    W.rank W.rankInjective W.symmetry (-1) (Or.inr rfl) repairs
    (fun atom present => W.fixedHistory atom (List.mem_reverse.mp present)) W.fixedReferences b W.entry
  exact ⟨F, fun atom present => fixedF atom (List.mem_reverse.mpr present), entryF, referencesF, mirrorF⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceMirror

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceMirror.sourceMirror_of_queryBranches
