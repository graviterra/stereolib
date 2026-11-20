import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorCorrectionWitness
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorTransport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranch
import TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Reconstruct once on a spliced state, then transfer its exact optional observations to
the original and mirrored generated states. The same molecular map and rank carry every
observation. The remaining inputs are a purely structural branch-selection predicate and
an actual same-state key tie; the separate slot-locality bridge must derive that tie from
the original cross-state comparison. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSplicedMirrorWitness

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointPreparedRootWitness (root_matched_of_tie)
open LocalizedChemicalRingJointPreparedMirrorCorrectionWitness (MirrorWitness)
open LocalizedChemicalRingJointPreparedCorrectionWitness (originalState)
open LocalizedChemicalRingReferenceConsensusCorrectionWitness
  (refineRank refineRank_lt refineRank_injective)
open LocalizedChemicalRingWitnessRawDescent
  (actual_fresh_boundary_path_descent boundary_query_adequate)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingRawStateSplice (splice find_splice)
open LocalizedChemicalRingProperRotationConsensus (referenceAt_injective)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (mirror structuralDepth)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (rootAddress : data.target.1.address = [])
  (left right : Fin 4) (distinct : left ≠ right)

include agreement admissible supported charge reached rootAddress distinct in
theorem exists_mirrorWitness_of_spliced_tie
    (select : CanonicalOccurrenceKey → Bool)
    (onLeft : ∀ p : List input.Atom,
      p.head? = some (referenceAt input mol c node data left) →
      select (canonicalOccurrenceKey
        (rawPathNode data.target.1.root (boundaryPath data.target p))) = true)
    (onRight : ∀ p : List input.Atom,
      p.head? = some (referenceAt input mol c node data right) →
      select (canonicalOccurrenceKey
        (rawPathNode data.target.1.root (boundaryPath data.target p))) = false)
    (tie : slotKeys input mol single c node data
        (splice select (originalState input mol node (inputGeometry input) [])
          (originalState input mol node (mirror (inputGeometry input)) [])) [] left =
      slotKeys input mol single c node data
        (splice select (originalState input mol node (inputGeometry input) [])
          (originalState input mol node (mirror (inputGeometry input)) [])) [] right) :
    Nonempty (MirrorWitness input mol c node data []
      (referenceAt input mol c node data left) (referenceAt input mol c node data right)) := by
  let stateL := originalState input mol node (inputGeometry input) []
  let stateR := originalState input mol node (mirror (inputGeometry input)) []
  let state := splice select stateL stateR
  obtain ⟨w⟩ := root_matched_of_tie input mol single charge c node data rootAddress
    state [] left right tie
  have different : referenceAt input mol c node data left ≠
      referenceAt input mol c node data right :=
    fun equality => distinct (referenceAt_injective input mol c node data equality)
  refine ⟨{
    symmetry := w.symmetry
    rank := refineRank w.rank
    rankInjective := refineRank_injective w.rank
    fixedHistory := w.fixedHistory
    entry := w.entry
    fixedReferences := w.fixedReferences
    execution := ?_
    matched := ?_ }⟩
  · intro p valid
    have fresh : referenceAt input mol c node data left ∉ data.target.1.node.history := by
      intro member
      exact different ((w.fixedHistory _ member).symm.trans w.entry)
    obtain ⟨child, edge, _, _, descent⟩ :=
      actual_fresh_boundary_path_descent input mol agreement admissible supported single
        node reached _ data.target data.found data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left _
        w.leftCurrent w.leftReal fresh p valid
    exact ⟨⟨child, edge, descent⟩,
      boundary_query_adequate input mol agreement single data.target data.real _ p valid node⟩
  · intro d member
    obtain ⟨p, terminal, _, labels, lower, higher⟩ := w.matched d member
    refine ⟨p, terminal, ?_, fun y present => refineRank_lt w.rank (lower y present),
      fun y residual different => refineRank_lt w.rank (higher y residual different)⟩
    have mappedHead : (p.1.map (w.symmetry : Equiv.Perm input.Atom)).head? =
        some (referenceAt input mol c node data right) := by
      rw [List.head?_map, p.2.head, Option.map_some, w.entry]
    have leftSelected := onLeft p.1 p.2.head
    have rightSelected := onRight (p.1.map (w.symmetry : Equiv.Perm input.Atom)) mappedHead
    have leftLookup : state.factAt?
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) =
      stateL.factAt? (rawPathNode data.target.1.root (boundaryPath data.target p.1)) := by
      change (splice select stateL stateR).find? _ = _
      rw [find_splice, leftSelected]
      rfl
    have rightLookup : state.factAt?
        (rawPathNode data.target.1.root
          (boundaryPath data.target (p.1.map (w.symmetry : Equiv.Perm input.Atom)))) =
      stateR.factAt? (rawPathNode data.target.1.root
        (boundaryPath data.target (p.1.map (w.symmetry : Equiv.Perm input.Atom)))) := by
      change (splice select stateL stateR).find? _ = _
      rw [find_splice, rightSelected]
      rfl
    rw [leftLookup, rightLookup] at labels
    exact labels

include agreement admissible supported charge reached rootAddress distinct in
/-- The same spliced comparison also supplies every recursive query's structural branch
certificate. Thus signed correction yields physical mirror transport without an assumed
query adapter, desired labels, or a correction oracle. -/
theorem mirrorTransport_of_spliced_tie
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates
        input input.detectedMultiCenterMolecule cfg d)
    (current : node.atom = c.1.val)
    (select : CanonicalOccurrenceKey → Bool)
    (onLeft : ∀ p : List input.Atom,
      p.head? = some (referenceAt input mol c node data left) →
      select (canonicalOccurrenceKey
        (rawPathNode data.target.1.root (boundaryPath data.target p))) = true)
    (onRight : ∀ p : List input.Atom,
      p.head? = some (referenceAt input mol c node data right) →
      select (canonicalOccurrenceKey
        (rawPathNode data.target.1.root (boundaryPath data.target p))) = false)
    (tie : slotKeys input mol single c node data
        (splice select (originalState input mol node (inputGeometry input) [])
          (originalState input mol node (mirror (inputGeometry input)) [])) [] left =
      slotKeys input mol single c node data
        (splice select (originalState input mol node (inputGeometry input) [])
          (originalState input mol node (mirror (inputGeometry input)) [])) [] right) :
    RootedTetrahedralBranchSymmetry.MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right) := by
  obtain ⟨W⟩ := exists_mirrorWitness_of_spliced_tie input mol agreement admissible supported
    single charge c node data reached rootAddress left right distinct select onLeft onRight tie
  apply LocalizedChemicalRingJointPreparedRootMirrorTransport.mirrorTransport_of_witness
    input mol c node data cfg agreement admissible supported single charge calibrated reached
    rootAddress current [] left right W
  intro p valid d query payload actual
  exact Classical.choice (LocalizedChemicalRingJointPreparedRootBranch.query_branch
    input mol single c node data rootAddress
    (splice select (originalState input mol node (inputGeometry input) [])
      (originalState input mol node (mirror (inputGeometry input)) [])) []
    left right distinct tie p valid d query payload actual)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSplicedMirrorWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSplicedMirrorWitness.exists_mirrorWitness_of_spliced_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSplicedMirrorWitness.mirrorTransport_of_spliced_tie
