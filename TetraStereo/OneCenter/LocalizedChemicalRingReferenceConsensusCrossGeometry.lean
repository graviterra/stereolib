import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusPriorTie
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitConsensusExecution
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
**Original and reflected actual root rankings of the 46-atom input are the same permutation.**

The actual prior keys of the common generated state are injective:
* A prior tie with no selected Rule-4b reference would leave an arm without uppercase labels, but
  a terminal occurrence at center 3 covering all centers carries an actual uppercase label.
* A prior tie with opposite references would reflect that label. Every root-fixing automorphism is
  proper at center 3 in the actual coordinates, and nothing below a covered occurrence is reversed,
  so the label is preserved instead.
* A prior tie with equal references would equate the actual labels at `o±` or `q±`, which the
  double exchange makes complementary.
* Slots of different isotopes are never exchanged by an automorphism.

Reflection then keeps the order of every pair of slots. Hence the reflected reading is the swap of
the original reading and the no-context assignment is uppercase, at the coordinate-derived letter
`referenceRaw false 28`.

No concrete R or S is evaluated: the letter is the stated function of the actual configuration sign
and the handedness of the actual common ranking. No label, sign, ranking, comparison or success is
assumed. This concerns one input and one center; universal ring correctness is not asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitRootEligibility
open LocalizedChemicalRingReferenceOrbitActualReferenceReading
open LocalizedChemicalRingReferenceOrbitConsensusExecution
open LocalizedChemicalRingReferenceOrbitRootMirrorCriterion
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry (candidate)
open LocalizedChemicalRingReferenceOrbitArmSymmetry (armSwap physicalAut raw_root_history_fixed)
open LocalizedChemicalRingReferenceOrbitOtherArmSymmetry (otherArmSwap)
open LocalizedChemicalRingReferenceConsensusSymmetry LocalizedChemicalRingReferenceConsensusStabilizer
open LocalizedChemicalRingReferenceConsensusArmSeparation (armNode armData)
open LocalizedChemicalRingReferenceConsensusArmTwin (twinNode twin_descends)
open LocalizedChemicalRingReferenceConsensusContext LocalizedChemicalRingReferenceConsensusFacts
open LocalizedChemicalRingReferenceConsensusRoot
open LocalizedChemicalRingReferenceConsensusPriorTie LocalizedChemicalRingReferenceConsensusReflection
open LocalizedChemicalRingReferenceOrbitRootLabelReadback (rootUnit)
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingInheritedReferenceTie
open LocalizedChemicalRingCoveredPathOrientation LocalizedChemicalRingWitnessExecution
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingSelectedFactCompleteness
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback LocalizedChemicalRingCompletenessPermutationTransport
open LocalizedChemicalRingDescriptorSpatialMirror
open LocalizedChemicalRingOrientationInduction (descriptorWith_mirror_none_iff mirror_mirror)
open LocalizedChemicalRingCompletenessMarked (slotPerm)
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedPromotedRanking (RefinedKey)
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors reached_atom_valid)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedConfigurationTransport (readback_none_of_missing)
open LocalizedMarkedDetectedFrames (detected_frame)
open LocalizedMarkedOperationEvaluator (Operations underWith tiedChildren mem_tiedChildren_actual)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_iff transportedSign)
open LocalizedGenericMarkedRecalculation (frameAtoms? readback? mirror readback_mirror flatMap_congr_mem
  structuralDepth caseFromMirror?)
open LocalizedChemicalRingMovedSlotEligibility (moved_child_selected)
open LocalizedActualPhysicalBranchDecision (coordinateCfg)
open RetainedRingSymmetryReconstruction (BondedChain)
open RootedTetrahedralBranchSymmetry

noncomputable section
open scoped Classical

private abbrev step := LocalizedChemicalRingInheritedFallback.rawStep?
private abbrev ops := sparseOperations certified mol
private abbrev G := observedGeometry certified false
private abbrev D := structuralDepth mol (canonicalCenterRoot 0)
private abbrev S : OccurrenceAuxState := gen (canonicalCenterRoot 0) D false 28

private theorem depth_bound : 17 ≤ D := by decide +kernel

private theorem root_reached : Reached mol (canonicalCenterRoot 0) := reached_root mol 0 (by decide)

/-! ## Every root-fixing automorphism is proper at center 3 -/

private def center3 : physical.Center := ⟨(3 : Fin 46), by
  change (3 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

private theorem proper_transfer {n : MultiCenterMolecule (Fin 46)}
    (same : canon.reindexFrames frameChange = n) (e : n.Aut) (d : n.Center)
    (at3 : d.1 = (3 : Fin 46)) (root : e.val (0 : Fin 46) = (0 : Fin 46)) :
    relativeSign n (Eq.mp (congrArg MultiCenterMolecule.Configuration same)
      (canon.reindexConfiguration frameChange (coordinateCfg certified))) e d = 1 := by
  subst same
  let e0 : canon.Aut := canon.autUnreindex frameChange e
  have image : canon.autReindex frameChange e0 = e := canon.autReindex_autUnreindex frameChange e
  have rootE0 : e0.val (0 : Fin 46) = (0 : Fin 46) := root
  have anchored := canonical_anchor_proper e0 rootE0
  rw [relativeSign_eq_iff]
  unfold transportedSign
  have transported := (MultiCenterMolecule.branchTransportSign_reindexFrames_iff canon frameChange
    (coordinateCfg certified) e0 ⟨d.1, d.2⟩ false).mpr (by
      have dEq : (⟨d.1, d.2⟩ : canon.Center) = ⟨(3 : Fin 46), by
          change (3 : Fin 46) ∈ graph.tetrahedralCenterSet
          rw [detected_inventory]
          decide⟩ := Subtype.ext at3
      rw [dEq]
      simpa only [Bool.false_eq_true, if_false, one_mul] using anchored)
  rw [image] at transported
  simpa only [Bool.false_eq_true, if_false] using transported

/-- The accepted coordinates give sign one at center 3 for every root-fixing automorphism. -/
theorem center3_proper (e : physical.Aut) (root : e.val (0 : Fin 46) = (0 : Fin 46)) :
    relativeSign physical cfg e center3 = 1 :=
  proper_transfer frameChange_spec e center3 rfl root

/-! ## Covered occurrences -/

private theorem center_cases (c : physical.Center) :
    c.1 = (0 : Fin 46) ∨ c.1 = (2 : Fin 46) ∨ c.1 = (3 : Fin 46) ∨ c.1 = (4 : Fin 46) ∨
      c.1 = (26 : Fin 46) := by
  obtain ⟨a, member⟩ := c
  change a ∈ graph.tetrahedralCenterSet at member
  rw [detected_inventory] at member
  simpa only [Finset.mem_insert, Finset.mem_singleton] using member

/-- Actual occurrence data of a real covered occurrence, in a form checked on concrete paths. -/
structure Terminal (a : Fin 46) (p : List (Fin 46)) : Prop where
  mark : RootMark a
  selected : nodeOf [0, a.val] ∈ tiedChildren mol ops [] (canonicalCenterRoot 0)
  valid : ResidualObsPath graph [(0 : Fin 46)] a p
  terminal : p.getLast? = some (3 : Fin 46)
  descends : Descends mol (nodeOf [0, a.val]) (rawPathNode (0 : Fin 46) p)
  atom3 : (rawPathNode (0 : Fin 46) p).atom = 3
  forced : (rawPathNode (0 : Fin 46) p).forcedLeaf = false
  length : (rawPathNode (0 : Fin 46) p).history.length = p.length + 1
  bound : p.length + 1 ≤ 17
  centers : (0 : Nat) ∈ (rawPathNode (0 : Fin 46) p).history ∧
    (2 : Nat) ∈ (rawPathNode (0 : Fin 46) p).history ∧
    (3 : Nat) ∈ (rawPathNode (0 : Fin 46) p).history ∧
    (4 : Nat) ∈ (rawPathNode (0 : Fin 46) p).history ∧
    (26 : Nat) ∈ (rawPathNode (0 : Fin 46) p).history
  lower : (5 : Nat) ∈ (rawPathNode (0 : Fin 46) p).history
  notArm : rawPathNode (0 : Fin 46) p ≠ armNode
  notTwin : rawPathNode (0 : Fin 46) p ≠ twinNode

private theorem covered_of {a : Fin 46} {p : List (Fin 46)} (t : Terminal a p)
    (c : physical.Center) : c.1.val ∈ (rawPathNode (0 : Fin 46) p).history := by
  obtain ⟨h0, h2, h3, h4, h26⟩ := t.centers
  rcases center_cases c with h | h | h | h | h <;> rw [h]
  · exact h0
  · exact h2
  · exact h3
  · exact h4
  · exact h26

private theorem arm_reached (a : Fin 46) (allowed : RootMark a) :
    Reached mol (nodeOf [0, a.val]) := by
  refine reached_child mol (canonicalCenterRoot 0) _ root_reached ?_
  rcases allowed with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem terminal_reached {a : Fin 46} {p : List (Fin 46)} (t : Terminal a p) :
    Reached mol (rawPathNode (0 : Fin 46) p) :=
  descendant_reached (arm_reached a t.mark) t.descends

private theorem real_of (node : RawMolecule.CanonicalBranchNode)
    (leaf : node.forcedLeaf = false) : node.provenance = .realAtom := by
  unfold RawMolecule.CanonicalBranchNode.forcedLeaf at leaf
  cases h : node.provenance <;> simp_all

/-- Keys at a covered terminal are injective in every state: no tie can be classified. -/
private theorem terminal_injective {a : Fin 46} {p : List (Fin 46)} (t : Terminal a p)
    (state : OccurrenceAuxState)
    (data : OccurrenceData certified mol center3 (rawPathNode (0 : Fin 46) p)) :
    Function.Injective (rawStateKeys certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl) := by
  intro left right tie
  by_contra different
  rcases tie_classified a t.mark center3 _ data t.descends t.forced t.atom3 state left right
    different tie with occurrence | same | same
  · have moved := occurrence.1 5 t.lower
    exact absurd moved (by decide +kernel)
  · exact t.notArm same
  · exact t.notTwin same

/-- Injective ordinary keys on both sides give a present actual descriptor. -/
private theorem descriptor_present (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) (reference : Fin 46) (depth : Nat)
    (injective : ∀ side, Function.Injective (rawStateKeys certified single_bonded
      (gen node depth side reference.val) data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl)) :
    descriptorWith step mol ops depth G [] (some reference.val) node ≠ none := by
  intro absent
  obtain ⟨reflected, left, right, _, different, tie⟩ := descriptor_none_original_reference_tie
    certified mol structure_agreement admissible supported single_bonded cfg c (all_calibrated c)
    node data depth reference absent
  exact different (injective reflected (congrArg (fun key : RefinedKey => (ofLex key).1) tie))

/-- Nothing below a covered occurrence reads a nondegenerate frame. -/
private theorem readback_none_below {a : Fin 46} {p : List (Fin 46)} (t : Terminal a p)
    (below : RawMolecule.CanonicalBranchNode)
    (descent : StrictDescendant mol (rawPathNode (0 : Fin 46) p) below)
    (atoms : List Nat) (frame : frameAtoms? mol below = some atoms) (L : List Nat)
    (sub : ∀ x ∈ L, x ∈ atoms) : readback? (inputGeometry certified) L = none := by
  have reached : Reached mol below := by
    obtain ⟨child, edge, rest⟩ := descent
    exact descendant_reached (reached_child mol _ child (terminal_reached t) edge) rest
  have real : below.forcedLeaf = false := by
    cases leaf : below.forcedLeaf with
    | false => rfl
    | true =>
        rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol below leaf] at frame
        cases frame
  have outside := strictDescendant_outside_history descent real
  have valid := reached_atom_valid mol admissible.1.1 below reached
  have rawSingle := raw_single mol certified structure_agreement admissible.1.1 admissible.1.2
    supported single_bonded
  rcases frame_atoms_perm_neighbors mol admissible.1.1 rawSingle below reached atoms frame with
    ⟨four, _⟩ | ⟨three, perm⟩
  · let d : physical.Center :=
      ⟨atomOf mol certified structure_agreement below.atom valid,
        center_of_degree mol certified structure_agreement admissible.1.1 admissible.1.2 supported
          below.atom valid four⟩
    exact False.elim (outside (covered_of t d))
  · have phantomNone : inputGeometry certified mol.atomCount = none :=
      inputGeometry_outside certified _ (by rw [count mol certified structure_agreement])
    by_cases phantom : mol.atomCount ∈ L
    · exact readback_none_of_missing _ L _ phantom phantomNone
    · have subNeighbors : ∀ y ∈ L, y ∈ mol.canonicalIncidentNeighbors below.atom := by
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
      exact readback_none_of_not_good _ L bad

private theorem closed (node : RawMolecule.CanonicalBranchNode) :
    ∀ parent child, StrictDescendant mol node parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol node child := by
  rintro parent child ⟨first, edge, rest⟩ next
  exact ⟨first, edge, rest.tail next⟩

/-- The actual descriptor at a covered terminal is never lowercase. -/
private theorem terminal_not_pseudo {a : Fin 46} {p : List (Fin 46)} (t : Terminal a p)
    (depth : Nat) (ctx : Option Nat) (x)
    (lower : descriptorWith step mol ops depth G [] ctx (rawPathNode (0 : Fin 46) p) =
      some (.pseudoasymmetric x)) : False := by
  obtain ⟨frameList, frame⟩ : ∃ atoms, frameAtoms? mol (rawPathNode (0 : Fin 46) p) = some atoms :=
    ⟨_, detected_frame mol certified structure_agreement admissible supported single_bonded
      center3 _ (terminal_reached t) (real_of _ t.forced) t.atom3⟩
  have agree : AgreeOn (StrictDescendant mol (rawPathNode (0 : Fin 46) p)) mol
      (mirror (inputGeometry certified)) (inputGeometry certified) := by
    intro below descent atoms frameBelow L sub
    rw [readback_mirror, readback_none_below t below descent atoms frameBelow L sub]
    rfl
  have stepCongr := LocalizedChemicalRingInheritedFallback.stepCongr mol ops
  have below : ∀ mark', underWith mol ops (mirror (inputGeometry certified)) [] (rawPathNode (0 : Fin 46) p)
      (factsWith step mol ops depth) mark' =
      underWith mol ops (inputGeometry certified) [] (rawPathNode (0 : Fin 46) p)
        (factsWith step mol ops depth) mark' := by
    intro mark'
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol _) (closed _) stepCongr depth _ _ agree
      [] (some mark') child ⟨child, mem_tiedChildren_actual mol ops [] _ child member, .refl⟩
  have belowMirror : ∀ mark', underWith mol ops (mirror (mirror (inputGeometry certified))) []
      (rawPathNode (0 : Fin 46) p) (factsWith step mol ops depth) mark' =
      underWith mol ops (mirror (inputGeometry certified)) [] (rawPathNode (0 : Fin 46) p)
        (factsWith step mol ops depth) mark' := by
    intro mark'
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol _) (closed _) stepCongr depth _ _ agree.mirror
      [] (some mark') child ⟨child, mem_tiedChildren_actual mol ops [] _ child member, .refl⟩
  have flip : ∀ L : List Nat, (∀ y ∈ L, y ∈ frameList) →
      readback? (mirror (inputGeometry certified)) L =
        flipBy (-1) (readback? (inputGeometry certified) L) := by
    intro L _
    rw [readback_mirror]
    unfold flipBy
    rw [if_neg (by norm_num)]
  have flipped := descriptorWith_flip mol ops step
    (LocalizedChemicalRingInheritedFallback.stepFlip mol ops) (-1) _ _ depth _ _ frame flip [] ctx
    below belowMirror
  have mirrored := descriptorWith_spatialMirror step mol ops depth (inputGeometry certified) [] ctx
    (rawPathNode (0 : Fin 46) p)
  have sameLabel : flipDescriptorBy (-1) (some (LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric x)) =
      some (.pseudoasymmetric x) := by
    have original : descriptorWith step mol ops depth (inputGeometry certified) [] ctx
        (rawPathNode (0 : Fin 46) p) = some (.pseudoasymmetric x) := lower
    rw [original] at flipped mirrored
    exact flipped.symm.trans mirrored
  have impossible := flipDescriptorBy_some_eq (-1) (Or.inr rfl) _ sameLabel
  norm_num at impossible

private abbrev L (p : List (Fin 46)) : Option LocalizedAuxiliaryLabel :=
  (S.factAt? (rawPathNode (0 : Fin 46) p)).map factLabel

/-- The actual common state records an uppercase label at a covered terminal. -/
private theorem terminal_label {a : Fin 46} {p : List (Fin 46)} (t : Terminal a p) :
    ∃ d : RS, L p = some (.chiral d) := by
  have bound := depth_bound
  have rootLength : (canonicalCenterRoot 0).history.length = 1 := rfl
  have lengthBound := t.bound
  have lengthEq := t.length
  have adequate : (rawPathNode (0 : Fin 46) p).history.length ≤
      D + (canonicalCenterRoot 0).history.length := by omega
  cases observed : L p with
  | none =>
      obtain ⟨data⟩ := occurrenceData_exists certified mol structure_agreement admissible supported
        single_bonded center3 _ (terminal_reached t) (real_of _ t.forced) t.atom3
      exact (descriptor_present center3 _ data 28 _ (fun _ => terminal_injective t _ data)
        (underWith_absence_refusal step mol ops D G [] (canonicalCenterRoot 0) _ _ 28 t.selected
          t.descends adequate observed)).elim
  | some label =>
      have executed := snapshot_path_execution (0 : Fin 46) p step mol ops D G []
        (canonicalCenterRoot 0) root_reached 28 label observed
      rcases label with d | x
      · exact ⟨d, rfl⟩
      · exact (terminal_not_pseudo t _ _ x executed).elim

private theorem mark_of_adj (m : Fin 46) (adjacent : graph.Adj 0 m) : RootMark m := by
  revert adjacent
  unfold RootMark
  fin_cases m <;> decide +kernel

/-- An actual opposite-reference correspondence contradicts properness at center 3. -/
private theorem opposite_impossible {a : Fin 46} {p : List (Fin 46)} (t : Terminal a p)
    (π : Equiv.Perm (Fin 46)) (aut : graph.IsAutomorphism π) (root : π 0 = 0)
    (corr : LabelCorr true (L p) (L (p.map π))) : False := by
  obtain ⟨d, label⟩ := terminal_label t
  have image := corr.1 d label
  simp only [if_true] at image
  let graphAut : graph.Aut := ⟨π, aut⟩
  let e : physical.Aut := graph.detectedMultiCenterAutOfGraphAut graphAut
  let σ : Nat → Nat := relabelOf certified e.val
  have bound := depth_bound
  have rootLength : (canonicalCenterRoot 0).history.length = 1 := rfl
  have lengthBound := t.bound
  have lengthEq := t.length
  let remaining := D + (canonicalCenterRoot 0).history.length - (p.length + 1)
  have source := snapshot_path_execution (0 : Fin 46) p step mol ops D G [] (canonicalCenterRoot 0)
    root_reached 28 _ label
  have target := snapshot_path_execution (0 : Fin 46) (p.map π) step mol ops D G []
    (canonicalCenterRoot 0) root_reached 28 _ image
  rw [List.length_map] at target
  have mapped : mapNode σ (rawPathNode (0 : Fin 46) p) = rawPathNode (0 : Fin 46) (p.map π) := by
    have transported := LocalizedChemicalRingWitnessPhysicalExecution.rawPathNode_map certified
      e.val (0 : Fin 46) p
    have rootImage : e.val (0 : Fin 46) = (0 : Fin 46) := root
    rw [rootImage] at transported
    exact transported
  let m0 : Fin 46 := π.symm 28
  have m0Image : σ m0.val = 28 := by
    have value := relabelOf_val certified e.val m0
    have computed : e.val m0 = (28 : Fin 46) := π.apply_symm_apply 28
    rw [computed] at value
    exact value
  have m0Mark : RootMark m0 := by
    apply mark_of_adj
    have adjacent : graph.Adj (π 0) (π m0) := by
      rw [root, π.apply_symm_apply]
      decide +kernel
    exact (MoleculeGraph.Aut.adj_iff graph graphAut 0 m0).mp adjacent
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
    certified mol structure_agreement admissible supported e
  have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
    certified mol structure_agreement admissible supported single_bonded e
  have rawSingle := raw_single mol certified structure_agreement admissible.1.1 admissible.1.2
    supported single_bonded
  have stepMap := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1 admissible.1.2
    rawSingle cov
  have transported := descriptorWith_map sym admissible.1.1 admissible.1.2 rawSingle cov step stepMap
    remaining (inputGeometry certified) (some m0.val) (rawPathNode (0 : Fin 46) p) (terminal_reached t)
  have centerFixed := center3_proper e root
  obtain ⟨frameList, frame⟩ : ∃ atoms, frameAtoms? mol (rawPathNode (0 : Fin 46) p) = some atoms :=
    ⟨_, detected_frame mol certified structure_agreement admissible supported single_bonded
      center3 _ (terminal_reached t) (real_of _ t.forced) t.atom3⟩
  have agree := agreeOn_of_covered certified mol structure_agreement admissible supported single_bonded
    e _ (terminal_reached t) (covered_of t)
  have stepCongr := LocalizedChemicalRingInheritedFallback.stepCongr mol ops
  have below : ∀ mark', underWith mol ops (pullback σ (inputGeometry certified)) []
      (rawPathNode (0 : Fin 46) p) (factsWith step mol ops remaining) mark' =
      underWith mol ops (inputGeometry certified) [] (rawPathNode (0 : Fin 46) p)
        (factsWith step mol ops remaining) mark' := by
    intro mark'
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol _) (closed _) stepCongr remaining _ _ agree
      [] (some mark') child ⟨child, mem_tiedChildren_actual mol ops [] _ child member, .refl⟩
  have belowMirror : ∀ mark', underWith mol ops (mirror (pullback σ (inputGeometry certified))) []
      (rawPathNode (0 : Fin 46) p) (factsWith step mol ops remaining) mark' =
      underWith mol ops (mirror (inputGeometry certified)) [] (rawPathNode (0 : Fin 46) p)
        (factsWith step mol ops remaining) mark' := by
    intro mark'
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol _) (closed _) stepCongr remaining _ _ agree.mirror
      [] (some mark') child ⟨child, mem_tiedChildren_actual mol ops [] _ child member, .refl⟩
  have flip : ∀ X : List Nat, (∀ y ∈ X, y ∈ frameList) →
      readback? (pullback σ (inputGeometry certified)) X =
        flipBy 1 (readback? (inputGeometry certified) X) := by
    intro X sub
    have localAction := readback_pullback_local certified mol structure_agreement admissible supported
      single_bonded cfg e center3 (all_calibrated _) (all_calibrated _) _ t.atom3 (terminal_reached t)
      _ frame X sub
    rw [centerFixed] at localAction
    exact localAction
  have flipped := descriptorWith_flip mol ops step
    (LocalizedChemicalRingInheritedFallback.stepFlip mol ops) 1 _ _ remaining _ _ frame flip []
    (some m0.val) below belowMirror
  have equalized : descriptorWith step mol ops remaining G [] (some 28)
      (rawPathNode (0 : Fin 46) (p.map π)) =
      descriptorWith step mol ops remaining G [] (some m0.val) (rawPathNode (0 : Fin 46) p) := by
    have rewritten : descriptorWith step mol ops remaining (inputGeometry certified) []
        (some (σ m0.val)) (mapNode σ (rawPathNode (0 : Fin 46) p)) =
        flipDescriptorBy 1 (descriptorWith step mol ops remaining (inputGeometry certified) []
          (some m0.val) (rawPathNode (0 : Fin 46) p)) :=
      transported.trans flipped
    rw [m0Image, mapped, flipDescriptorBy, if_pos rfl] at rewritten
    exact rewritten
  have independent := arm_descriptor_independent remaining (rawPathNode (0 : Fin 46) p) a t.mark
    t.descends (by omega) false m0 28 m0Mark (Or.inl rfl)
  have chain := target.symm.trans (equalized.trans (independent.trans source))
  rw [Option.some.injEq] at chain
  have letters : RS.swap d = d := by
    have injected := LocalizedTetrahedralRSPseudoDescriptor.chiral.inj chain
    exact injected
  cases d <;> cases letters

/-! ## Equal-reference ties at `o±` and `q±` -/

/-- Complementary labels at a pair of images under the double exchange cannot be equal. -/
private theorem complementary_impossible (first second : List (Fin 46))
    (nPlus nMinus : RawMolecule.CanonicalBranchNode)
    (rawPlus : rawPathNode (0 : Fin 46) first = nPlus)
    (rawMinus : rawPathNode (0 : Fin 46) second = nMinus)
    (sameLength : first.length = second.length)
    (lengthPlus : nPlus.history.length = first.length + 1)
    (lengthMinus : nMinus.history.length = first.length + 1)
    (firstBound : first.length + 1 ≤ 5)
    (child : RawMolecule.CanonicalBranchNode)
    (selected : child ∈ tiedChildren mol ops [] (canonicalCenterRoot 0))
    (path : Descends mol child nPlus)
    (reachedPlus : Reached mol nPlus) (real : nPlus.provenance = .realAtom) (atom26 : nPlus.atom = 26)
    (has26 : (26 : Nat) ∈ nPlus.history)
    (image : mapNode (relabelOf certified twistAut.val) nPlus = nMinus)
    (present : ∀ depth, 13 ≤ depth → descriptorWith step mol ops depth G [] (some 28) nPlus ≠ none)
    (independent : ∀ depth, 18 ≤ nMinus.history.length + depth →
      descriptorWith step mol ops depth G [] (some 29) nMinus =
        descriptorWith step mol ops depth G [] (some 28) nMinus)
    (corr : LabelCorr false ((S.factAt? nPlus).map factLabel) ((S.factAt? nMinus).map factLabel)) :
    False := by
  have bound := depth_bound
  have rootLength : (canonicalCenterRoot 0).history.length = 1 := rfl
  have adequate : nPlus.history.length ≤ D + (canonicalCenterRoot 0).history.length := by omega
  have remainingBound : 13 ≤ D + (canonicalCenterRoot 0).history.length - nPlus.history.length := by
    omega
  cases observed : (S.factAt? nPlus).map factLabel with
  | none =>
      exact present _ remainingBound
        (underWith_absence_refusal step mol ops D G [] (canonicalCenterRoot 0) child nPlus
          28 selected path adequate observed)
  | some label =>
      have labels : (S.factAt? nMinus).map factLabel = some label := by
        rcases label with d | x
        · simpa only [Bool.false_eq_true, if_false] using corr.1 d observed
        · exact corr.2 x observed
      subst rawPlus rawMinus
      have plusDescriptor := snapshot_path_execution (0 : Fin 46) first step mol ops D G []
        (canonicalCenterRoot 0) root_reached 28 label observed
      have minusDescriptor := snapshot_path_execution (0 : Fin 46) second step mol ops D G []
        (canonicalCenterRoot 0) root_reached 28 label labels
      rw [← sameLength] at minusDescriptor
      have remainingBound' : 18 ≤ (rawPathNode (0 : Fin 46) second).history.length +
          (D + (canonicalCenterRoot 0).history.length - (first.length + 1)) := by
        omega
      have flipped : descriptorWith step mol ops
          (D + (canonicalCenterRoot 0).history.length - (first.length + 1)) G []
          (some (relabelOf certified twistAut.val 28))
          (mapNode (relabelOf certified twistAut.val) (rawPathNode (0 : Fin 46) first)) =
          flipDescriptorBy (-1) (descriptorWith step mol ops
            (D + (canonicalCenterRoot 0).history.length - (first.length + 1)) G [] (some 28)
            (rawPathNode (0 : Fin 46) first)) :=
        twist_flip _ reachedPlus real atom26 has26 _ false 28
      have sigma28 : relabelOf certified twistAut.val 28 = 29 :=
        relabelOf_val certified twistAut.val (28 : Fin 46)
      rw [sigma28, image, independent _ remainingBound', minusDescriptor, plusDescriptor] at flipped
      have impossible := flipDescriptorBy_some_eq (-1) (Or.inr rfl) label flipped.symm
      norm_num at impossible

private def qPlus : RawMolecule.CanonicalBranchNode := nodeOf [0, 30, 34, 26]
private def qMinus : RawMolecule.CanonicalBranchNode := nodeOf [0, 31, 35, 26]

private theorem qPlus_descends : Descends mol (nodeOf [0, 30]) qPlus :=
  have first : nodeOf [0, 30, 34] ∈ mol.canonicalChildren (nodeOf [0, 30]) := by decide +kernel
  have second : qPlus ∈ mol.canonicalChildren (nodeOf [0, 30, 34]) := by decide +kernel
  (Relation.ReflTransGen.refl.tail first).tail second

private theorem qMinus_descends : Descends mol (nodeOf [0, 31]) qMinus :=
  have first : nodeOf [0, 31, 35] ∈ mol.canonicalChildren (nodeOf [0, 31]) := by decide +kernel
  have second : qMinus ∈ mol.canonicalChildren (nodeOf [0, 31, 35]) := by decide +kernel
  (Relation.ReflTransGen.refl.tail first).tail second

private theorem armNode_image : mapNode (relabelOf certified twistAut.val) armNode = twinNode :=
  LocalizedChemicalRingWitnessPhysicalExecution.rawPathNode_map certified twistAut.val
    (0 : Fin 46) ([28, 32, 27, 26] : List (Fin 46))

private theorem qPlus_image : mapNode (relabelOf certified twistAut.val) qPlus = qMinus :=
  LocalizedChemicalRingWitnessPhysicalExecution.rawPathNode_map certified twistAut.val
    (0 : Fin 46) ([30, 34, 26] : List (Fin 46))

private theorem o_impossible
    (corr : LabelCorr false (L [28, 32, 27, 26]) (L [29, 33, 27, 26])) : False := by
  apply complementary_impossible [28, 32, 27, 26] [29, 33, 27, 26] armNode twinNode rfl rfl rfl rfl rfl
    (by decide) (nodeOf [0, 28]) LocalizedChemicalRingReferenceOrbitBranch.shortcut_selected_first_child
    plus_descends (descendant_reached (arm_reached 28 (Or.inl rfl)) plus_descends) rfl rfl (by decide)
    armNode_image
  · intro depth adequate
    exact descriptor_present otherCurrent armNode armData 28 depth
      (fun s => plus_injective s depth adequate)
  · intro depth adequate
    exact arm_descriptor_independent depth twinNode 29 (Or.inr (Or.inl rfl)) twin_descends
      adequate false 29 28 (Or.inr (Or.inl rfl)) (Or.inl rfl)
  · exact corr

private theorem q_injective (state : OccurrenceAuxState)
    (data : OccurrenceData certified mol otherCurrent qPlus) :
    Function.Injective (rawStateKeys certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl) := by
  intro left right tie
  by_contra different
  rcases tie_classified 30 (Or.inr (Or.inr (Or.inl rfl))) otherCurrent qPlus data qPlus_descends rfl rfl
    state left right different tie with occurrence | same | same
  · rcases occurrence.2 with h | h | h <;> cases h
  · exact absurd same (by decide +kernel)
  · exact absurd same (by decide +kernel)

private theorem q_impossible
    (corr : LabelCorr false (L [30, 34, 26]) (L [31, 35, 26])) : False := by
  have qReached : Reached mol qPlus :=
    descendant_reached (arm_reached 30 (Or.inr (Or.inr (Or.inl rfl)))) qPlus_descends
  obtain ⟨data⟩ := occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded otherCurrent qPlus qReached rfl rfl
  apply complementary_impossible [30, 34, 26] [31, 35, 26] qPlus qMinus rfl rfl rfl rfl rfl (by decide)
    (nodeOf [0, 30]) LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_selected_first_child
    qPlus_descends qReached rfl rfl (by decide) qPlus_image
  · intro depth _
    exact descriptor_present otherCurrent qPlus data 28 depth (fun s => q_injective _ data)
  · intro depth adequate
    exact arm_descriptor_independent depth qMinus 31 (Or.inr (Or.inr (Or.inr rfl))) qMinus_descends
      adequate false 29 28 (Or.inr (Or.inl rfl)) (Or.inl rfl)
  · exact corr

/-! ## The concrete terminals -/

private def chainChecked : List Nat → List Nat → Bool
  | _, [] => true
  | lead, x :: rest =>
      decide (nodeOf (lead ++ [x]) ∈ mol.canonicalChildren (nodeOf lead)) && chainChecked (lead ++ [x]) rest

private theorem chain_descends : ∀ (rest lead : List Nat), chainChecked lead rest = true →
    Descends mol (nodeOf lead) (nodeOf (lead ++ rest))
  | [], lead, _ => by simpa using (Relation.ReflTransGen.refl : Descends mol (nodeOf lead) (nodeOf lead))
  | x :: rest, lead, checked => by
      simp only [chainChecked, Bool.and_eq_true, decide_eq_true_eq] at checked
      have tail := chain_descends rest (lead ++ [x]) checked.2
      have same : lead ++ [x] ++ rest = lead ++ x :: rest := by simp
      rw [same] at tail
      exact Relation.ReflTransGen.head checked.1 tail

private def t28 : List (Fin 46) := [28, 32, 27, 26, 1, 2, 5, 8, 15, 4, 41, 44, 38, 42, 40, 3]
private def t29 : List (Fin 46) := [29, 33, 27, 26, 1, 2, 5, 8, 15, 4, 41, 44, 38, 42, 40, 3]
private def t30 : List (Fin 46) := [30, 34, 26, 1, 2, 5, 8, 15, 4, 41, 44, 38, 42, 40, 3]

private theorem selected29 : nodeOf [0, 29] ∈ tiedChildren mol ops [] (canonicalCenterRoot 0) :=
  moved_child_selected certified mol structure_agreement admissible supported single_bonded
    physicalAut rootCenter (canonicalCenterRoot 0) rootData root_reached
    raw_root_history_fixed (29 : Fin 46) (by decide +kernel)
    (by change (28 : Fin 46) ≠ (29 : Fin 46); decide)
    (nodeOf [0, 29]) (by decide +kernel) rfl

private theorem valid_chain (a : Fin 46) (p : List (Fin 46)) (head : p.head? = some a) (nonempty : p ≠ [])
    (nodup : p.Nodup) (outside : ∀ x ∈ p, x ∉ [(0 : Fin 46)]) (chain : BondedChain graph p) :
    ResidualObsPath graph [(0 : Fin 46)] a p :=
  ⟨nonempty, head, nodup, outside, chain⟩

private theorem terminal28 : Terminal 28 t28 where
  mark := Or.inl rfl
  selected := LocalizedChemicalRingReferenceOrbitBranch.shortcut_selected_first_child
  valid := valid_chain _ _ rfl (by decide) (by decide) (by decide +kernel) (by
    simp only [t28, BondedChain]
    decide +kernel)
  terminal := rfl
  descends := chain_descends [32, 27, 26, 1, 2, 5, 8, 15, 4, 41, 44, 38, 42, 40, 3] [0, 28] (by decide +kernel)
  atom3 := rfl
  forced := rfl
  length := rfl
  bound := by decide
  centers := by decide +kernel
  lower := by decide +kernel
  notArm := by decide +kernel
  notTwin := by decide +kernel

private theorem terminal29 : Terminal 29 t29 where
  mark := Or.inr (Or.inl rfl)
  selected := selected29
  valid := valid_chain _ _ rfl (by decide) (by decide) (by decide +kernel) (by
    simp only [t29, BondedChain]
    decide +kernel)
  terminal := rfl
  descends := chain_descends [33, 27, 26, 1, 2, 5, 8, 15, 4, 41, 44, 38, 42, 40, 3] [0, 29] (by decide +kernel)
  atom3 := rfl
  forced := rfl
  length := rfl
  bound := by decide
  centers := by decide +kernel
  lower := by decide +kernel
  notArm := by decide +kernel
  notTwin := by decide +kernel

private theorem terminal30 : Terminal 30 t30 where
  mark := Or.inr (Or.inr (Or.inl rfl))
  selected := LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_selected_first_child
  valid := valid_chain _ _ rfl (by decide) (by decide) (by decide +kernel) (by
    simp only [t30, BondedChain]
    decide +kernel)
  terminal := rfl
  descends := chain_descends [34, 26, 1, 2, 5, 8, 15, 4, 41, 44, 38, 42, 40, 3] [0, 30] (by decide +kernel)
  atom3 := rfl
  forced := rfl
  length := rfl
  bound := by decide
  centers := by decide +kernel
  lower := by decide +kernel
  notArm := by decide +kernel
  notTwin := by decide +kernel

/-! ## Root prior keys are injective -/

private abbrev Keys := rawStateKeys certified single_bonded S rootData.target rootData.real rootUnit rfl

private theorem root_root : rootData.target.1.root = (0 : Fin 46) := by
  have history : rootData.target.1.node.history = [(0 : Fin 46)] := by
    apply List.map_injective_iff.mpr Fin.val_injective
    exact (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ rootData.found).history
  have head := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceHead
  simpa [history] using head.symm

private theorem root_address : rootData.target.1.address = [] := by
  have history : rootData.target.1.node.history = [(0 : Fin 46)] := by
    apply List.map_injective_iff.mpr Fin.val_injective
    exact (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ rootData.found).history
  have address := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceAddress
  rw [address]
  simp [CertifiedLocalizedCIPInput.canonicalAddress, history]

private theorem slot_current (slot : Fin 4) (a : Fin 46)
    (atAtom : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot = a) :
    ((rawStateFrames certified single_bonded S rootData.target rootData.real rootUnit rfl).frame.cursorAt
      slot).occurrence.1.node.current? = some a := by
  have frameEq : (rawStateFrames certified single_bonded S rootData.target rootData.real rootUnit rfl).frame =
      rootData.frame := Option.some.inj ((rawStateFrames certified single_bonded S rootData.target
        rootData.real rootUnit rfl).frameComputed.symm.trans rootData.frameExec)
  have mapped : (((rawStateFrames certified single_bonded S rootData.target rootData.real rootUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current?).map Fin.val = some a.val := by
    change LocalizedChemicalRingFrameReadback.atomAt certified _ slot = some a.val
    rw [frameEq, rootData.atomAt_eq]
    exact congrArg (fun x : Fin 46 => some x.val) atAtom
  cases found : ((rawStateFrames certified single_bonded S rootData.target rootData.real rootUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some b =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

private theorem slot_mark (slot : Fin 4) :
    RootMark (referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot) :=
  mark_of_adj _ (physical.ligandAtomAt_adj rootCenter (rootData.ligandOf slot))

private theorem root_center_values : rootData.target.1.root = (0 : Fin 46) := root_root

/-- One prior tie, decoded and tested against a terminal: the mirror flag must be `false`, the
automorphism at the terminal is available, and an uppercase-free arm is impossible. -/
private theorem tie_flag (left right : Fin 4) (a b : Fin 46)
    (atLeft : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = a)
    (atRight : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = b)
    (tie : (ofLex (Keys left)).1 = (ofLex (Keys right)).1) {p : List (Fin 46)} (t : Terminal a p) :
    (∃ π : Equiv.Perm (Fin 46), graph.IsAutomorphism π ∧ π 0 = 0 ∧ π a = b) ∧
    ∀ (q : List (Fin 46)) (valid : ResidualObsPath graph [(0 : Fin 46)] a q),
      IsDetectedCenter graph (pathTerminal q valid.nonempty) →
      ∃ π : Equiv.Perm (Fin 46), graph.IsAutomorphism π ∧ π 0 = 0 ∧ π a = b ∧
        LabelCorr false (L q) (L (q.map π)) := by
  have decoded := prior_tie_path_cases certified single_bonded S rootData.target rootData.real rootUnit
    rfl root_address ⟨0, constant_charge⟩ left right a b (slot_current left a atLeft)
    (slot_current right b atRight) tie
  rw [root_root] at decoded
  have validT : ResidualObsPath graph [(0 : Fin 46)] a p := t.valid
  have detected3 : IsDetectedCenter graph (3 : Fin 46) := by
    apply (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
    apply (graph.mem_tetrahedralCenterSet _).mp
    rw [detected_inventory]
    decide
  have terminalEq : pathTerminal p validT.nonempty = (3 : Fin 46) := by
    have last := List.getLast?_eq_some_getLast validT.nonempty
    rw [t.terminal] at last
    exact (Option.some.inj last).symm
  have detectedT : IsDetectedCenter graph (pathTerminal p validT.nonempty) := by
    rw [terminalEq]
    exact detected3
  rcases decoded with free | ⟨flag, corr⟩
  · obtain ⟨d, label⟩ := terminal_label t
    exact (free p validT detectedT d label).elim
  · obtain ⟨π, aut, root, entry, atT⟩ := corr p validT detectedT
    cases flag with
    | true => exact (opposite_impossible t π aut root atT).elim
    | false => exact ⟨⟨π, aut, root, entry⟩, corr⟩

private theorem masses_ne {a b : Fin 46} (different : graph.atomMass a ≠ graph.atomMass b)
    (exists_aut : ∃ π : Equiv.Perm (Fin 46), graph.IsAutomorphism π ∧ π 0 = 0 ∧ π a = b) : False := by
  obtain ⟨π, aut, _, entry⟩ := exists_aut
  apply different
  have preserved := MoleculeGraph.Aut.atomMass_eq (m := graph) ⟨π, aut⟩ a
  rw [← entry]
  exact preserved.symm

private theorem image_o (π : Equiv.Perm (Fin 46)) (aut : graph.IsAutomorphism π) (root : π 0 = 0)
    (entry : π 28 = 29) : ([28, 32, 27, 26] : List (Fin 46)).map π = [29, 33, 27, 26] := by
  obtain ⟨k, a, r, same⟩ := root_aut_normal_form ⟨π, aut⟩ root
  have form : π = candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1) := same
  rw [form] at entry ⊢
  revert entry
  fin_cases k <;> cases a <;> cases r <;> decide +kernel

private theorem image_q (π : Equiv.Perm (Fin 46)) (aut : graph.IsAutomorphism π) (root : π 0 = 0)
    (entry : π 30 = 31) : ([30, 34, 26] : List (Fin 46)).map π = [31, 35, 26] := by
  obtain ⟨k, a, r, same⟩ := root_aut_normal_form ⟨π, aut⟩ root
  have form : π = candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1) := same
  rw [form] at entry ⊢
  revert entry
  fin_cases k <;> cases a <;> cases r <;> decide +kernel

private theorem detected26 : IsDetectedCenter graph (26 : Fin 46) := by
  apply (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
  apply (graph.mem_tetrahedralCenterSet _).mp
  rw [detected_inventory]
  decide

/-- **The actual prior keys of the common root state are injective.** -/
theorem root_prior_keys_injective :
    Function.Injective fun slot => (ofLex (Keys slot)).1 := by
  intro left right tie
  by_contra different
  have distinct : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left ≠
      referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right :=
    fun same => different (referenceAt_injective rootCenter _ rootData same)
  have cross : graph.atomMass (28 : Fin 46) ≠ graph.atomMass (30 : Fin 46) := by decide +kernel
  have cross31 : graph.atomMass (28 : Fin 46) ≠ graph.atomMass (31 : Fin 46) := by decide +kernel
  have cross29 : graph.atomMass (29 : Fin 46) ≠ graph.atomMass (30 : Fin 46) := by decide +kernel
  have cross2931 : graph.atomMass (29 : Fin 46) ≠ graph.atomMass (31 : Fin 46) := by decide +kernel
  have pair28 (x y : Fin 4)
      (atX : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData x = (28 : Fin 46))
      (atY : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData y = (29 : Fin 46))
      (tied : (ofLex (Keys x)).1 = (ofLex (Keys y)).1) : False := by
    obtain ⟨_, corr⟩ := tie_flag x y 28 29 atX atY tied terminal28
    have valid : ResidualObsPath graph [(0 : Fin 46)] (28 : Fin 46) [28, 32, 27, 26] :=
      valid_chain _ _ rfl (by decide) (by decide) (by decide +kernel) (by
        simp only [BondedChain]
        decide +kernel)
    obtain ⟨π, aut, root, entry, atO⟩ := corr _ valid (by
      have value : pathTerminal ([28, 32, 27, 26] : List (Fin 46)) valid.nonempty = (26 : Fin 46) := rfl
      rw [value]
      exact detected26)
    rw [image_o π aut root entry] at atO
    exact o_impossible atO
  have pair30 (x y : Fin 4)
      (atX : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData x = (30 : Fin 46))
      (atY : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData y = (31 : Fin 46))
      (tied : (ofLex (Keys x)).1 = (ofLex (Keys y)).1) : False := by
    obtain ⟨_, corr⟩ := tie_flag x y 30 31 atX atY tied terminal30
    have valid : ResidualObsPath graph [(0 : Fin 46)] (30 : Fin 46) [30, 34, 26] :=
      valid_chain _ _ rfl (by decide) (by decide) (by decide +kernel) (by
        simp only [BondedChain]
        decide +kernel)
    obtain ⟨π, aut, root, entry, atQ⟩ := corr _ valid (by
      have value : pathTerminal ([30, 34, 26] : List (Fin 46)) valid.nonempty = (26 : Fin 46) := rfl
      rw [value]
      exact detected26)
    rw [image_q π aut root entry] at atQ
    exact q_impossible atQ
  rcases slot_mark left with h | h | h | h <;> rcases slot_mark right with g | g | g | g
  · exact distinct (h.trans g.symm)
  · exact pair28 left right h g tie
  · exact masses_ne cross (tie_flag left right _ _ h g tie terminal28).1
  · exact masses_ne cross31 (tie_flag left right _ _ h g tie terminal28).1
  · exact pair28 right left g h tie.symm
  · exact distinct (h.trans g.symm)
  · exact masses_ne cross29 (tie_flag left right _ _ h g tie terminal29).1
  · exact masses_ne cross2931 (tie_flag left right _ _ h g tie terminal29).1
  · exact masses_ne cross (tie_flag right left _ _ g h tie.symm terminal28).1
  · exact masses_ne cross29 (tie_flag right left _ _ g h tie.symm terminal29).1
  · exact distinct (h.trans g.symm)
  · exact pair30 left right h g tie
  · exact masses_ne cross31 (tie_flag right left _ _ g h tie.symm terminal28).1
  · exact masses_ne cross2931 (tie_flag right left _ _ g h tie.symm terminal29).1
  · exact pair30 right left g h tie.symm
  · exact distinct (h.trans g.symm)

/-! ## The cross-geometry endpoints -/

theorem reflected_state :
    gen (canonicalCenterRoot 0) D true 28 = S.map mirrorFact :=
  underWith_mirror step mol ops D (inputGeometry certified) [] (canonicalCenterRoot 0) 28

private theorem common_rank_cross :
    rank certified mol rootCenter (canonicalCenterRoot 0) rootData
        (rawStateKeys certified single_bonded (gen (canonicalCenterRoot 0) D true 28)
          rootData.target rootData.real rootUnit rfl) =
      rank certified mol rootCenter (canonicalCenterRoot 0) rootData
        (rawStateKeys certified single_bonded S rootData.target rootData.real rootUnit rfl) := by
  unfold rank
  rw [reflected_state, slotPerm_mirror_of_prior_injective certified single_bonded S rootData.target
    rootData.real rootUnit rfl root_prior_keys_injective]

/-- **The actual ranking of every eligible reference is the same under original and reflected
geometry**: literally one permutation, for any two eligible marks. -/
theorem referenceRank_cross (first second : Fin 46)
    (firstEligible : first.val ∈ rootEligible) (secondEligible : second.val ∈ rootEligible) :
    referenceRank true first = referenceRank false second := by
  rw [referenceRank_eq_common true first firstEligible,
    referenceRank_eq_common false second secondEligible]
  exact common_rank_cross

/-- The requested parity equality. -/
theorem referenceRank_handedness_cross :
    permHandedness (referenceRank false 28) = permHandedness (referenceRank true 28) := by
  have member : ((28 : Fin 46)).val ∈ rootEligible := (root_eligible_iff 28).mpr (by decide)
  rw [referenceRank_cross 28 28 member member]

theorem referenceRaw_true : referenceRaw true 28 = (referenceRaw false 28).swap := by
  have member : ((28 : Fin 46)).val ∈ rootEligible := (root_eligible_iff 28).mpr (by decide)
  unfold referenceRaw
  rw [referenceRank_cross 28 28 member member]
  rfl

/-- The actual reflected inherited reading is the swap of the original reading. -/
theorem actualReading_cross (first second : Fin 46)
    (firstEligible : first.val ∈ rootEligible) (secondEligible : second.val ∈ rootEligible) :
    actualReading true first = (actualReading false second).map RS.swap := by
  have member : ((28 : Fin 46)).val ∈ rootEligible := (root_eligible_iff 28).mpr (by decide)
  rw [actualReading_eq true first firstEligible, actualReading_eq false second secondEligible]
  have ranks : referenceRank true first = referenceRank false second :=
    referenceRank_cross first second firstEligible secondEligible
  unfold referenceRaw
  rw [ranks]
  rfl

/-- **The actual no-context assignment at the root is uppercase, at the coordinate-derived letter.**
The letter is `referenceRaw false 28`: the sign of the actual root configuration times the
handedness of the actual common ranking. No concrete R or S is evaluated here. -/
theorem root_assignCenter_chiral :
    LocalizedChemicalRingInheritedFallback.assignCenter? mol (sparseOperations certified mol)
      (inputGeometry certified) 0 = some (.chiral (referenceRaw false 28)) := by
  rw [root_assignCenter_eq, referenceRaw_true]
  cases referenceRaw false 28 <;> rfl

theorem referenceRaw_false_formula :
    referenceRaw false 28 = letterOfSign
      (physical.configurationSign cfg rootCenter * permHandedness (referenceRank false 28)) := rfl

/-- The declarative count of prior-tied root pairs of the actual keys is zero, matching the
independent physical count of enantiomorphic root pairs. -/
theorem root_prior_pair_count_eq_physical :
    completeRule5PairCount Keys = physicalEnantiomorphicPairCount physical cfg rootCenter := by
  rw [root_pair_count_zero]
  have noPair : ∀ left right, ¬ CompletePriorPair Keys left right := by
    rintro left right ⟨different, tied⟩
    exact different (root_prior_keys_injective tied)
  simp [completeRule5PairCount, sourceEnantiomorphicPairCount, noPair]

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.center3_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.root_prior_keys_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.reflected_state
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.referenceRank_cross
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.referenceRank_handedness_cross
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.referenceRaw_true
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.actualReading_cross
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.root_assignCenter_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCrossGeometry.root_prior_pair_count_eq_physical
