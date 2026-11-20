import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessOrientation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
An actual query whose history contains every detected center has no real detected
strict descendant. Its descendant readbacks therefore agree under any molecular
relabeling, without a physical-sign induction hypothesis or calibration of other centers.
A matched successful observation at this query decodes the physical sign using only
the source and image center's coordinate calibrations.

Coverage and successful observation are explicit here. Concrete instances must derive
both from actual paths and execution; optional label equality alone is insufficient.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingBoundaryWitnessOrientation LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingWitnessExecution LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedConfigurationTransport (readback_none_of_missing)
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedGenericMarkedRecalculation (frameAtoms? readback? mirror flatMap_congr_mem)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- A real strict descendant cannot revisit any atom of the source history. -/
theorem strictDescendant_outside_history {mol : RawMolecule}
    {source target : RawMolecule.CanonicalBranchNode}
    (path : StrictDescendant mol source target) (real : target.forcedLeaf = false) :
    target.atom ∉ source.history := by
  obtain ⟨child, first, rest⟩ := path
  induction rest with
  | refl => exact (LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol source child first).2.1 real
  | @tail parent target path edge ih =>
      intro present
      have member := history_mono ((Relation.ReflTransGen.single first).trans path) present
      exact (LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol parent target edge).2.1 real member

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)

include agreement admissible supported single in
/-- Only the two frames actually being compared need coordinate calibration. -/
theorem readback_pullback_local
    (d : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg
      (input.detectedMultiCenterMolecule.centerPerm e d))
    (node : RawMolecule.CanonicalBranchNode) (atomEq : node.atom = d.1.val)
    (reached : Reached mol node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (L : List Nat) (sub : ∀ x ∈ L, x ∈ atoms) :
    readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) L =
      flipBy (relativeSign input.detectedMultiCenterMolecule cfg e d)
        (readback? (inputGeometry input) L) := by
  rw [← readback_map]
  by_cases good : L.length = 4 ∧ L.Nodup
  · obtain ⟨π, rfl⟩ := exists_enumeration input mol agreement admissible supported single d node
      atomEq reached atoms frame L sub good
    exact readback_relabel input cfg e d calibrated imageCalibrated π
  · rw [readback_none_of_not_good _ _ (not_good_map _ L good), readback_none_of_not_good _ L good,
      flipBy_none]

include agreement admissible supported single in
/-- Once all detected centers have been visited, descendant frame readbacks need no
assumed signs. Ring-return duplicates have no frame; degree-three frames refuse readback. -/
theorem agreeOn_of_covered (source : RawMolecule.CanonicalBranchNode)
    (sourceReached : Reached mol source)
    (covered : ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val ∈ source.history) :
    AgreeOn (StrictDescendant mol source) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))
      (inputGeometry input) := by
  intro node descent atoms frame L sub
  have reached : Reached mol node := by
    obtain ⟨child, edge, rest⟩ := descent
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  have real : node.forcedLeaf = false := by
    cases leaf : node.forcedLeaf with
    | false => rfl
    | true => rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol node leaf] at frame; cases frame
  have outside := strictDescendant_outside_history descent real
  have valid := reached_atom_valid mol admissible.1.1 node reached
  have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
  rcases frame_atoms_perm_neighbors mol admissible.1.1 rawSingle node reached atoms frame with
    ⟨four, _⟩ | ⟨three, perm⟩
  · let d : input.detectedMultiCenterMolecule.Center :=
      ⟨atomOf mol input agreement node.atom valid,
        center_of_degree mol input agreement admissible.1.1 admissible.1.2 supported node.atom valid four⟩
    exact False.elim (outside (covered d))
  · rw [← readback_map]
    have phantomNone : inputGeometry input mol.atomCount = none :=
      inputGeometry_outside input _ (by rw [count mol input agreement])
    by_cases phantom : mol.atomCount ∈ L
    · have left : readback? (inputGeometry input)
          (L.map (relabelOf input (e : Equiv.Perm input.Atom))) = none := by
        refine readback_none_of_missing _ _ (relabelOf input _ mol.atomCount)
          (List.mem_map_of_mem phantom) ?_
        rw [relabelOf_outside input _ _ (by rw [count mol input agreement])]
        exact phantomNone
      rw [left, readback_none_of_missing _ L _ phantom phantomNone]
    · have subNeighbors : ∀ y ∈ L, y ∈ mol.canonicalIncidentNeighbors node.atom := by
        intro y hy
        have member := perm.mem_iff.mp (sub y hy)
        rw [List.mem_append, List.mem_singleton] at member
        rcases member with inside | isPhantom
        · exact inside
        · exact absurd (isPhantom ▸ hy) phantom
      have bad : ¬ (L.length = 4 ∧ L.Nodup) := by
        rintro ⟨four, nodup⟩
        have := (nodup.subperm subNeighbors).length_le
        rw [four, three] at this
        omega
      rw [readback_none_of_not_good _ _ (not_good_map _ L bad), readback_none_of_not_good _ L bad]

include agreement admissible supported single in
/-- The covered-history decoder derives descendant-state agreement, including mirrors,
instead of assuming it or assuming any other center's physical sign. -/
theorem relativeSign_of_covered_executions
    (d : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg
      (input.detectedMultiCenterMolecule.centerPerm e d))
    (node : RawMolecule.CanonicalBranchNode) (atomEq : node.atom = d.1.val)
    (reached : Reached mol node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (covered : ∀ c : input.detectedMultiCenterMolecule.Center, c.1.val ∈ node.history)
    (ops : Operations) (step : Step) (stepCongr : StepCongr step mol ops)
    (stepFlip : StepFlip mol ops step) (depth : Nat) (state : OccurrenceAuxState) (ctx : Option Nat)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (original : descriptorWith step mol ops depth (inputGeometry input) state ctx node = some label)
    (pulled : descriptorWith step mol ops depth
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state ctx node =
        some label) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have agree := agreeOn_of_covered input mol agreement admissible supported single e node reached covered
  have closed : ∀ parent child, StrictDescendant mol node parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol node child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  have below : ∀ mark, underWith mol ops
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state node
      (factsWith step mol ops depth) mark =
      underWith mol ops (inputGeometry input) state node (factsWith step mol ops depth) mark := by
    intro mark
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol node) closed stepCongr depth _ _ agree
      state (some mark) child ⟨child, mem_tiedChildren_actual mol ops state node child member, .refl⟩
  have belowMirror : ∀ mark, underWith mol ops
      (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))) state node
      (factsWith step mol ops depth) mark =
      underWith mol ops (mirror (inputGeometry input)) state node (factsWith step mol ops depth) mark := by
    intro mark
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol node) closed stepCongr depth _ _ agree.mirror
      state (some mark) child ⟨child, mem_tiedChildren_actual mol ops state node child member, .refl⟩
  have flipped := descriptorWith_flip mol ops step stepFlip _ _ _ depth node atoms frame
    (readback_pullback_local input mol agreement admissible supported single cfg e d calibrated
      imageCalibrated node atomEq reached atoms frame) state ctx below belowMirror
  rw [original, pulled] at flipped
  exact flipDescriptorBy_some_eq _ (relativeSign_eq_one_or_neg_one _ cfg e d) label flipped.symm

include agreement admissible supported single in
/-- Actual full-history snapshot matches give a proper sign at a covered terminal.
Only its two calibrated frames are required; no other-residual-sign premise remains. -/
theorem relativeSign_of_covered_snapshot (step : Step)
    (stepMap : StepMap step mol (sparseOperations input mol)
      (relabelOf input (e : Equiv.Perm input.Atom)))
    (stepCongr : StepCongr step mol (sparseOperations input mol))
    (stepFlip : StepFlip mol (sparseOperations input mol) step)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (reference entry : input.Atom)
    (fixedBoundary : ∀ atom ∈ target.1.node.history.reverse, (e : Equiv.Perm input.Atom) atom = atom)
    (fixedReference : (e : Equiv.Perm input.Atom) reference = reference)
    (path : List input.Atom)
    (valid : ResidualObsPath input.moleculeGraph target.1.node.history.reverse entry path)
    (d : input.detectedMultiCenterMolecule.Center) (terminal : pathTerminal path valid.nonempty = d.1)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (imageCalibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg
      (input.detectedMultiCenterMolecule.centerPerm e d))
    (covered : ∀ c : input.detectedMultiCenterMolecule.Center,
      c.1.val ∈ (rawPathNode target.1.root (boundaryPath target path)).history)
    (depth : Nat) (source : RawMolecule.CanonicalBranchNode) (sourceReached : Reached mol source)
    (matched : ((snapshotWith step input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel =
      ((snapshotWith step input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root
          (boundaryPath target (path.map (e : Equiv.Perm input.Atom))))).map factLabel)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (observed : ((snapshotWith step input mol depth (inputGeometry input) source reference.val).factAt?
        (rawPathNode target.1.root (boundaryPath target path))).map factLabel = some label) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  obtain ⟨original, pulled⟩ := snapshot_boundary_matched_pullback input mol agreement admissible
    supported single e step stepMap target reference fixedBoundary fixedReference path depth
    (inputGeometry input) source sourceReached matched label observed
  have reached := snapshot_path_reached target.1.root (boundaryPath target path) step
    mol (sparseOperations input mol) depth (inputGeometry input) [] source sourceReached
    reference.val label observed
  have atomEq := (witness_boundary input single target entry path valid).1
  rw [terminal] at atomEq
  have frame := LocalizedMarkedDetectedFrames.detected_frame mol input agreement admissible
    supported single d _ reached rfl atomEq.symm
  exact relativeSign_of_covered_executions input mol agreement admissible supported single cfg e d
    calibrated imageCalibrated _ atomEq.symm reached _ frame covered _ step stepCongr stepFlip
    _ [] (some reference.val) label original pulled

end TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation.strictDescendant_outside_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation.readback_pullback_local
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation.agreeOn_of_covered
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation.relativeSign_of_covered_executions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation.relativeSign_of_covered_snapshot
