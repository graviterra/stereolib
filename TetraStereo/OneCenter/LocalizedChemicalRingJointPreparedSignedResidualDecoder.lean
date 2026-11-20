import TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Mirror-normalized signed residual decoder for the prepared ring evaluator

The accepted `LocalizedChemicalRingJointPreparedResidualDecoder` decodes a common proper
residual sense (`relativeSign = 1`) into actual prepared child-state equality between the
pulled-back geometry and the original geometry.  This module proves the mirror analogue needed
by the signed `SourceMirror` rank loop: a common residual sense `relativeSign = -1` controls the
prepared child states of the mirrored pulled-back geometry
`pullback σ (mirror inputGeometry)`.

The spatial reflection flips uppercase raw letters but leaves pseudo lowercase letters
unchanged in the generated case classification (`flipDescriptorBy` flips both).  Accordingly no
physical sign is inferred here from a swapped pseudo label.  The proof first normalizes
`pullback σ (mirror G)` to `mirror (pullback σ G)`, uses the accepted uniform readback flip
`flipsBy_input` at every reached frame, and then complements by `RS.swap`.  At a residual
centre the local sign is `-1`, so the two mirror normalizations cancel; at degree-three
(phantom) and forced-leaf frames the relevant readbacks are proved `none`, so no blanket
successful-frame premise is added.

At the current frame, calibration supplies the descriptor flip by `-(relativeSign d)`.  Two
successful equal labels therefore force `-relativeSign d = 1`, hence `relativeSign d = -1`.
The arbitrary reference lists, all depths, both geometry sides, and the actual reached frame
query are retained.  No whole-state equality, invented geometry calibration, desired label, or
sign information from a pseudo descriptor is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingOrientationInduction
open LocalizedChemicalRingCompletenessStrict LocalizedChemicalRingCompletenessMarked
open LocalizedChemicalRingCompletenessMirror LocalizedChemicalRingCompletenessOrbit
open LocalizedChemicalRingCompletenessRefusal
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessPermutationTransport (descriptorWith_map)
open LocalizedChemicalRingRawResidualDescendants
open LocalizedChemicalRingJointPreparedGeometryCongruence (preparedFacts_congr)
open LocalizedChemicalRingJointPreparedGeometryFlip (preparedDescriptor_flip)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations)
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors reached_atom_valid SingleBonded)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single raw_atom_bound)
open LocalizedMarkedConfigurationTransport (readback_none_of_missing)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? consensus mirror
  caseFromMirror? readback_mirror flatMap_congr_mem structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (B : List input.Atom) (source : RawMolecule.CanonicalBranchNode)
  (entry : input.Atom) (entryEq : entry.val = source.atom) (outside : entry ∉ B)
  (carried : ∀ atom ∈ B, atom.val ∈ source.history) (sourceReached : Reached mol source)
  (properNeg : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph B entry d.1 → d.1 ≠ entry →
      relativeSign input.detectedMultiCenterMolecule cfg e d = -1)

/-! ## The two sign normalizations -/

/-- Complementation of a raw letter commutes with a `-1` flip: if `x` is flipped once more by
spatial reflection, the result is `x` again. -/
theorem flipBy_neg_one_map (x : Option RS) :
    (flipBy (-1 : ℝ) x).map RS.swap = x := by
  have step : flipBy (-1 : ℝ) x = x.map RS.swap := by
    unfold flipBy
    rw [if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
  rw [step]
  cases x with
  | none => rfl
  | some v => simp only [Option.map_some, swap_swap]

/-- A unit sign `s` and its negation act as opposite letter flips after spatial reflection. -/
theorem flipBy_neg (s : ℝ) (unit : s = 1 ∨ s = -1) (x : Option RS) :
    (flipBy s x).map RS.swap = flipBy (-s) x := by
  rcases unit with rfl | rfl
  · have lhs : flipBy (1 : ℝ) x = x :=
      congrFun (flipBy_eq_id (1 : ℝ) rfl) x
    have rhs : flipBy (-(1 : ℝ)) x = x.map RS.swap := by
      have neg : -(1 : ℝ) = -1 := by norm_num
      rw [neg]
      unfold flipBy
      rw [if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
    rw [lhs, rhs]
  · have lhs : (flipBy (-1 : ℝ) x).map RS.swap = x := flipBy_neg_one_map x
    have rhs : flipBy (-(-1 : ℝ)) x = x := by
      have neg : -(-1 : ℝ) = 1 := by norm_num
      rw [neg]
      exact congrFun (flipBy_eq_id (1 : ℝ) rfl) x
    rw [lhs, rhs]

/-! ## Descendant agreement under negative residual signs -/

include agreement admissible supported single calibrated entryEq outside carried sourceReached properNeg in
/-- The mirrored pulled-back geometry reads exactly like the original geometry on every list
drawn from the frame of a strict residual descendant, including forced leaves and degree-three
phantom frames. -/
theorem agreeOn_strictDescendants_mirror :
    AgreeOn (StrictDescendant mol source) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (mirror (inputGeometry input)))
      (inputGeometry input) := by
  intro node descent atoms frame L sub
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have reached : Reached mol node := by
    obtain ⟨child, edge, rest⟩ := descent
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  have real : node.forcedLeaf = false := by
    cases leaf : node.forcedLeaf with
    | false => rfl
    | true =>
        rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol node leaf] at frame
        cases frame
  obtain ⟨child, edge, rest⟩ := descent
  obtain ⟨atom, atomEq, connected⟩ := descendant_component input mol agreement admissible supported
    single B source node entry entryEq outside carried
    ((Relation.ReflTransGen.single edge).trans rest) real
  have different : atom ≠ entry := by
    intro same
    apply strictDescendant_atom_ne sourceReached ⟨child, edge, rest⟩ real
    rw [← atomEq, same, entryEq]
  have flips := flipsBy_input input mol agreement admissible supported single cfg e calibrated
    node reached atoms frame L sub
  by_cases four : node.atom < mol.atomCount ∧
      (mol.canonicalIncidentNeighbors node.atom).length = 4
  · have negSign : nodeSign input mol agreement admissible supported cfg e node = -1 := by
      unfold nodeSign
      rw [dif_pos four]
      apply properNeg
      · have same : atomOf mol input agreement node.atom four.1 = atom := by
          apply Fin.ext
          exact atomEq.symm
        simpa only [same] using connected
      · intro same
        apply different
        apply Fin.ext
        simpa only [atomOf_val, atomEq] using congrArg Fin.val same
    calc
      readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
          (mirror (inputGeometry input))) L
          = readback? (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
              (inputGeometry input))) L := by
              exact congrArg (fun geom => readback? geom L)
                (mirror_pullback (relabelOf input (e : Equiv.Perm input.Atom))
                  (inputGeometry input)).symm
      _ = (readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
              (inputGeometry input)) L).map RS.swap :=
              readback_mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
                (inputGeometry input)) L
      _ = (flipBy (nodeSign input mol agreement admissible supported cfg e node)
              (readback? (inputGeometry input) L)).map RS.swap := by
              rw [flips]
      _ = readback? (inputGeometry input) L := by
              rw [negSign]
              exact flipBy_neg_one_map (readback? (inputGeometry input) L)
  · have signOne : nodeSign input mol agreement admissible supported cfg e node = 1 := by
      unfold nodeSign
      rw [dif_neg four]
    have noneRead : readback? (inputGeometry input) L = none := by
      have valid : node.atom < mol.atomCount :=
        reached_atom_valid mol wellFormed node reached
      rcases frame_atoms_perm_neighbors mol wellFormed rawSingle node reached atoms frame with
        ⟨fourLen, _⟩ | ⟨three, perm⟩
      · exact absurd ⟨valid, fourLen⟩ four
      · have phantomNone : inputGeometry input mol.atomCount = none :=
          inputGeometry_outside input _ (by rw [count mol input agreement])
        by_cases phantom : mol.atomCount ∈ L
        · exact readback_none_of_missing (inputGeometry input) L mol.atomCount phantom phantomNone
        · have subNeighbors : ∀ y ∈ L, y ∈ mol.canonicalIncidentNeighbors node.atom := by
            intro y hy
            have member := perm.mem_iff.mp (sub y hy)
            rw [List.mem_append, List.mem_singleton] at member
            rcases member with inside | isPhantom
            · exact inside
            · exact absurd (isPhantom ▸ hy) phantom
          have bad : ¬ (L.length = 4 ∧ L.Nodup) := by
            rintro ⟨len, nodup⟩
            have := (nodup.subperm subNeighbors).length_le
            rw [len, three] at this
            omega
          exact readback_none_of_not_good (inputGeometry input) L bad
    calc
      readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
          (mirror (inputGeometry input))) L
          = readback? (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
              (inputGeometry input))) L := by
              exact congrArg (fun geom => readback? geom L)
                (mirror_pullback (relabelOf input (e : Equiv.Perm input.Atom))
                  (inputGeometry input)).symm
      _ = (readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
              (inputGeometry input)) L).map RS.swap :=
              readback_mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
                (inputGeometry input)) L
      _ = (flipBy (nodeSign input mol agreement admissible supported cfg e node)
              (readback? (inputGeometry input) L)).map RS.swap := by
              rw [flips]
      _ = (flipBy (1 : ℝ) (readback? (inputGeometry input) L)).map RS.swap := by
              rw [signOne]
      _ = (readback? (inputGeometry input) L).map RS.swap := by
              exact congrArg (fun y => y.map RS.swap)
                (congrFun (flipBy_eq_id (1 : ℝ) rfl) (readback? (inputGeometry input) L))
      _ = readback? (inputGeometry input) L := by
              rw [noneRead]
              rfl

include agreement admissible supported single calibrated entryEq outside carried sourceReached properNeg in
/-- At every strict descendant, the prepared facts under the mirrored pulled-back geometry equal
the prepared facts under the original geometry, at every depth and every reference context, on
both geometry sides. -/
theorem preparedFacts_eq_of_residual_mirror_signs (ops : MultiOperations) (depth : Nat)
    (state : OccurrenceAuxState) (M : List Nat) (node : RawMolecule.CanonicalBranchNode)
    (descent : StrictDescendant mol source node) :
    preparedFacts mol ops depth
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (mirror (inputGeometry input)))
        state M node =
      preparedFacts mol ops depth (inputGeometry input) state M node ∧
    preparedFacts mol ops depth
        (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
          (mirror (inputGeometry input)))) state M node =
      preparedFacts mol ops depth (mirror (inputGeometry input)) state M node := by
  have agree := agreeOn_strictDescendants_mirror input mol agreement admissible supported single
    cfg e calibrated B source entry entryEq outside carried sourceReached properNeg
  have closed : ∀ parent child, StrictDescendant mol source parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol source child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  exact ⟨preparedFacts_congr mol ops (StrictDescendant mol source) closed depth _ _ agree
      state M node descent,
    preparedFacts_congr mol ops (StrictDescendant mol source) closed depth _ _ agree.mirror
      state M node descent⟩

include agreement admissible supported single calibrated entryEq outside carried sourceReached properNeg in
/-- Actual child continuations under the mirrored pulled-back geometry equal the original child
continuations at every reference context, on both geometry sides. -/
theorem childrenUnder_eq_of_residual_mirror_signs (ops : MultiOperations) (depth : Nat)
    (state : OccurrenceAuxState) (M : List Nat) :
    childrenUnder mol (preparedFacts mol ops depth)
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (mirror (inputGeometry input)))
        state source M =
      childrenUnder mol (preparedFacts mol ops depth) (inputGeometry input) state source M ∧
    childrenUnder mol (preparedFacts mol ops depth)
        (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
          (mirror (inputGeometry input)))) state source M =
      childrenUnder mol (preparedFacts mol ops depth) (mirror (inputGeometry input)) state source M := by
  have agree := agreeOn_strictDescendants_mirror input mol agreement admissible supported single
    cfg e calibrated B source entry entryEq outside carried sourceReached properNeg
  have closed : ∀ parent child, StrictDescendant mol source parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol source child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  constructor
  · unfold childrenUnder
    exact flatMap_congr_mem _ _ _ fun child member =>
      preparedFacts_congr mol ops (StrictDescendant mol source) closed depth _ _ agree
        state M child ⟨child, member, .refl⟩
  · unfold childrenUnder
    exact flatMap_congr_mem _ _ _ fun child member =>
      preparedFacts_congr mol ops (StrictDescendant mol source) closed depth _ _ agree.mirror
        state M child ⟨child, member, .refl⟩

include agreement admissible supported single calibrated entryEq outside carried sourceReached properNeg in
/-- The actual prepared descriptor under `pullback σ (mirror G)` is the descriptor under `G`
flipped by the negated current physical sign.  Descendant state equality is derived above, not
assumed. -/
theorem descriptor_flip_of_residual_mirror_signs (ops : MultiOperations)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : source.atom = d.1.val)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (depth : Nat) (state : OccurrenceAuxState) (M : List Nat) :
    preparedDescriptor? mol ops depth
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (mirror (inputGeometry input)))
        state M source =
      flipDescriptorBy (-(relativeSign input.detectedMultiCenterMolecule cfg e d))
        (preparedDescriptor? mol ops depth (inputGeometry input) state M source) := by
  have below := childrenUnder_eq_of_residual_mirror_signs input mol agreement admissible supported
    single cfg e calibrated B source entry entryEq outside carried sourceReached properNeg ops depth
    state
  have flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
          (mirror (inputGeometry input))) L =
        flipBy (-(relativeSign input.detectedMultiCenterMolecule cfg e d))
          (readback? (inputGeometry input) L) := by
    intro L sub
    calc
      readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
          (mirror (inputGeometry input))) L
          = readback? (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
              (inputGeometry input))) L := by
              exact congrArg (fun geom => readback? geom L)
                (mirror_pullback (relabelOf input (e : Equiv.Perm input.Atom))
                  (inputGeometry input)).symm
      _ = (readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom))
              (inputGeometry input)) L).map RS.swap :=
              readback_mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom))
                (inputGeometry input)) L
      _ = (flipBy (relativeSign input.detectedMultiCenterMolecule cfg e d)
              (readback? (inputGeometry input) L)).map RS.swap := by
              rw [readback_pullback_frame input mol agreement admissible supported single cfg e
                calibrated d source atomEq sourceReached atoms frame L sub]
      _ = flipBy (-(relativeSign input.detectedMultiCenterMolecule cfg e d))
              (readback? (inputGeometry input) L) :=
              flipBy_neg (relativeSign input.detectedMultiCenterMolecule cfg e d)
                (relativeSign_eq_one_or_neg_one _ cfg e d)
                (readback? (inputGeometry input) L)
  exact preparedDescriptor_flip mol ops
    (-(relativeSign input.detectedMultiCenterMolecule cfg e d))
    _ _ depth source atoms frame flip state M (fun L => (below L).1) (fun L => (below L).2)

include agreement admissible supported single calibrated entryEq outside carried sourceReached properNeg in
/-- **Signed decoder.** Two successful equal actual prepared labels, one under the original
geometry and one under the mirrored pulled-back geometry, force the current relative sign to be
`-1`. -/
theorem relativeSign_eq_neg_one_of_residual_mirror_signs (ops : MultiOperations)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : source.atom = d.1.val)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (depth : Nat) (state : OccurrenceAuxState) (M : List Nat)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (original : preparedDescriptor? mol ops depth (inputGeometry input) state M source =
      some label)
    (pulled : preparedDescriptor? mol ops depth
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (mirror (inputGeometry input)))
      state M source = some label) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = -1 := by
  have flip := descriptor_flip_of_residual_mirror_signs input mol agreement admissible supported
    single cfg e calibrated B source entry entryEq outside carried sourceReached properNeg ops d
    atomEq atoms frame depth state M
  rw [original, pulled] at flip
  have unit : (-(relativeSign input.detectedMultiCenterMolecule cfg e d)) = 1 ∨
      (-(relativeSign input.detectedMultiCenterMolecule cfg e d)) = -1 := by
    rcases relativeSign_eq_one_or_neg_one _ cfg e d with h | h <;> norm_num [h]
  have positive : -(relativeSign input.detectedMultiCenterMolecule cfg e d) = 1 :=
    flipDescriptorBy_some_eq _ unit label flip.symm
  rcases relativeSign_eq_one_or_neg_one _ cfg e d with h | h
  · rw [h] at positive
    norm_num at positive
  · exact h

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder.flipBy_neg_one_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder.flipBy_neg
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder.agreeOn_strictDescendants_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder.preparedFacts_eq_of_residual_mirror_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder.childrenUnder_eq_of_residual_mirror_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder.descriptor_flip_of_residual_mirror_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSignedResidualDecoder.relativeSign_eq_neg_one_of_residual_mirror_signs
