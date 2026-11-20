import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmPrior
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorObservation
import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorKeySeparation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
Reflected-geometry companion of the separation at `o+ = [0,28,32,27,26]`.

On the actual snapshot below `o+` generated under the reflected geometry with inherited
reference 28, the actual marked keys and the actual Rules-1-5 keys of the two O18 attachments
differ. The decoder is the accepted covered-history mirror decoder; label presence under the
reflected geometry comes from the accepted original execution. Both geometry sides are then
packaged with `observedGeometry`. No label value or physical sign is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmMirror

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitCoveringPath LocalizedChemicalRingReferenceOrbitStabilizer
open LocalizedChemicalRingReferenceConsensusSymmetry LocalizedChemicalRingReferenceConsensusArmSeparation
open LocalizedChemicalRingReferenceConsensusArmPrior
open LocalizedChemicalRingInheritedRefusalCases (observedGeometry referenceAt)
open LocalizedChemicalRingSelectedRefusalWitness LocalizedChemicalRingSelectedOutwardTie
open LocalizedChemicalRingCoveredPathMirrorOrientation LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingPrescribedPathFactMatch
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (mirror)
open RetainedRingSymmetryReconstruction (BondedChain)

noncomputable section
open scoped Classical

private theorem tail_valid' :
    ResidualObsPath graph armData.target.1.node.history.reverse (34 : Fin 46) tailPath := by
  rw [arm_history, List.reverse_reverse]
  refine ⟨by decide, rfl, by decide, ?_, ?_⟩
  · decide +kernel
  · simp only [tailPath, BondedChain]
    decide +kernel

private theorem tail_query' :
    rawPathNode armData.target.1.root (boundaryPath armData.target tailPath) = coveringNode := by
  unfold boundaryPath
  rw [arm_history, arm_root]
  rfl

private theorem o18_image' (e : graph.Aut) (entry : e.val (34 : Fin 46) = (35 : Fin 46)) :
    e.val (30 : Fin 46) = (31 : Fin 46) := by
  have finite : ∀ x : Fin 46, graph.Adj 35 x → graph.atomZ x = graph.atomZ 30 →
      graph.atomMass x = graph.atomMass 30 → x = 31 := by
    intro x
    fin_cases x <;> decide +kernel
  apply finite
  · rw [← entry]
    exact (MoleculeGraph.Aut.adj_iff (m := graph) e 34 30).mpr (by decide +kernel)
  · exact MoleculeGraph.Aut.atomZ_eq (m := graph) e 30
  · exact MoleculeGraph.Aut.atomMass_eq (m := graph) e 30

/-- The covering terminal's label is present in the reflected snapshot below `o+`. -/
theorem arm_mirror_covering_label_present (depth : Nat) (adequate : 13 ≤ depth) :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
      (mirror (inputGeometry certified)) armNode 28).factAt? coveringNode).map factLabel ≠ none := by
  intro absent
  have budget : coveringNode.history.length ≤ depth + armNode.history.length := by
    have lengths : coveringNode.history.length = 18 ∧ armNode.history.length = 5 := by
      decide +kernel
    omega
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol depth (mirror (inputGeometry certified)) armNode armChild coveringNode 28
    arm_selected_child arm_child_descent budget absent
  obtain ⟨value, computed⟩ :=
    LocalizedChemicalRingReferenceOrbitMirrorObservation.covering_mirror_descriptor_exists_at
      (28 : Fin 46) (depth + armNode.history.length - coveringNode.history.length)
  have computed' : LocalizedChemicalRingInheritedFallback.descriptor? mol
      (sparseOperations certified mol) (depth + armNode.history.length - coveringNode.history.length)
      (mirror (inputGeometry certified)) [] (some 28) coveringNode = some value := computed
  rw [computed'] at refused
  cases refused

/-- **Reflected separation at `o+`** for the actual marked keys of reference 28. -/
theorem arm_mirror_refined_separate (depth : Nat) (adequate : 13 ≤ depth) :
    refinedKey certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (mirror (inputGeometry certified)) armNode 28)
        armData.target armData.real armUnit rfl (28 : Fin 46)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) slot34 ≠
      refinedKey certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (mirror (inputGeometry certified)) armNode 28)
        armData.target armData.real armUnit rfl (28 : Fin 46)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) slot35 := by
  intro tie
  let state := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
    (mirror (inputGeometry certified)) armNode 28
  let branch := Classical.choice arm_tied_branch
  obtain ⟨center, centerCurrent⟩ := certified.localizedRerootCursor_current_exists
    (⟨armData.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
  obtain ⟨_, pair, _, _, _, _, _, targetEq, leftEq, rightEq, _, _, _, realL, realR⟩ :=
    selected_refined_tie_real_outward certified single_bonded
      branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
      branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
      branch.built branch.built' branch.tie state armData.target armData.real branch.inside
      branch.nonroot center centerCurrent armUnit rfl (28 : Fin 46) (retainedCarrierFuel certified)
      (2 * (retainedCarrierFuel certified + 1)) slot34 slot35 slots_distinct tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at realL
  rw [rightEq] at realR
  have currentL := slot_current state slot34 34 slot_atoms.1
  have currentR := slot_current state slot35 35 slot_atoms.2
  obtain ⟨_, matched⟩ := actual_outward_default_tie_prescribed_fact_match certified single_bonded
    state armData.target armData.real armUnit rfl (28 : Fin 46) slot34 slot35 (34 : Fin 46) (35 : Fin 46)
    currentL currentR realL realR rootL rootR pair.leftSlot pair.rightSlot addressL addressR tie
    ⟨0, constant_charge⟩
  have detected : IsDetectedCenter graph (pathTerminal tailPath tail_valid'.nonempty) :=
    (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
      ((graph.mem_tetrahedralCenterSet _).mp current.2)
  obtain ⟨π, automorphism, historyFixed, entry, referenceFixed, _, _, _, _, facts⟩ :=
    matched ⟨tailPath, tail_valid'⟩ detected
  let e : physical.Aut := graph.detectedMultiCenterAutOfGraphAut ⟨π, automorphism⟩
  have rootFixed : π (0 : Fin 46) = (0 : Fin 46) :=
    historyFixed (0 : Fin 46) (by rw [arm_history]; decide)
  obtain ⟨centerFixed, negative⟩ := other_exchange_lower_negative cfg e rootFixed referenceFixed
    (o18_image' ⟨π, automorphism⟩ entry)
  have imageCalibrated : LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates
      certified physical cfg (physical.centerPerm e current) := by
    rw [centerFixed]
    exact calibrated
  have boundaryFixed : ∀ atom ∈ armData.target.1.node.history.reverse, e.val atom = atom := by
    intro atom member
    exact historyFixed atom (List.mem_reverse.mp member)
  have covered : ∀ c : physical.Center, c.1.val ∈
      (rawPathNode armData.target.1.root (boundaryPath armData.target tailPath)).history := by
    intro c
    rw [tail_query']
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨c.1, covering_detected c.1 c.2, rfl⟩)
  cases observed : (state.factAt? (rawPathNode armData.target.1.root
      (boundaryPath armData.target tailPath))).map factLabel with
  | none =>
      rw [tail_query'] at observed
      exact arm_mirror_covering_label_present depth adequate observed
  | some label =>
      have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
        certified mol structure_agreement admissible supported e
      have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
        certified mol structure_agreement admissible supported single_bonded e
      have stepMap := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1 admissible.1.2
        (raw_single mol certified structure_agreement admissible.1.1 admissible.1.2 supported
          single_bonded) cov
      have proper := relativeSign_of_covered_mirror_snapshot certified mol structure_agreement
        admissible supported single_bonded cfg e LocalizedChemicalRingInheritedFallback.rawStep? stepMap
        (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations certified mol))
        (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations certified mol))
        armData.target (28 : Fin 46) (34 : Fin 46) boundaryFixed referenceFixed tailPath tail_valid'
        current rfl calibrated imageCalibrated covered depth armNode arm_reached facts label observed
      rw [negative] at proper
      norm_num at proper

/-- **Reflected ordinary separation at `o+`.** -/
theorem arm_mirror_prior_separate (depth : Nat) (adequate : 13 ≤ depth) :
    rawStateKeys certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (mirror (inputGeometry certified)) armNode 28)
        armData.target armData.real armUnit rfl slot34 ≠
      rawStateKeys certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (mirror (inputGeometry certified)) armNode 28)
        armData.target armData.real armUnit rfl slot35 := by
  intro prior
  let state := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
    (mirror (inputGeometry certified)) armNode 28
  obtain ⟨center, centerCurrent⟩ := certified.localizedRerootCursor_current_exists
    (⟨armData.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
  obtain ⟨pair, targetEq, leftEq, rightEq, realL, realR⟩ := prior_tie_real_outward certified
    single_bonded state armData.target armData.real armUnit rfl (Classical.choice arm_tied_branch)
    center centerCurrent slot34 slot35 slots_distinct prior
  have currentL : pair.left.occurrence.1.node.current? = some (34 : Fin 46) := by
    rw [leftEq]
    exact slot_current state slot34 34 slot_atoms.1
  have currentR : pair.right.occurrence.1.node.current? = some (35 : Fin 46) := by
    rw [rightEq]
    exact slot_current state slot35 35 slot_atoms.2
  have sealedHistory : ∀ neighbor, graph.Adj neighbor (28 : Fin 46) →
      neighbor ∈ armData.target.1.node.history := by
    rw [arm_history]
    have finite : ∀ n : Fin 46, graph.Adj n (28 : Fin 46) → n ∈ armPath.reverse := by
      intro n
      fin_cases n <;> decide +kernel
    exact finite
  apply arm_mirror_refined_separate depth adequate
  exact refined_tie_of_sealed_prior_tie certified single_bonded state armData.target armData.real
    armUnit rfl (28 : Fin 46) (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1))
    slot34 slot35 pair targetEq leftEq rightEq realL realR (34 : Fin 46) (35 : Fin 46) currentL currentR
    (by decide) (by decide) sealedHistory (by decide +kernel) (by decide +kernel) prior

/-- Both geometry sides: the actual Rules-1-5 keys at `o+` separate the O18 attachments. -/
theorem arm_prior_separate_side (side : Bool) (depth : Nat) (adequate : 13 ≤ depth) :
    rawStateKeys certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (observedGeometry certified side) armNode 28)
        armData.target armData.real armUnit rfl slot34 ≠
      rawStateKeys certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (observedGeometry certified side) armNode 28)
        armData.target armData.real armUnit rfl slot35 := by
  cases side
  · exact arm_prior_separate depth adequate
  · exact arm_mirror_prior_separate depth adequate

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmMirror

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmMirror.arm_mirror_covering_label_present
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmMirror.arm_mirror_refined_separate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmMirror.arm_mirror_prior_separate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmMirror.arm_prior_separate_side
