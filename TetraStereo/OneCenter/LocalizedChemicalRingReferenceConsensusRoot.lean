import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitActualReferenceReading
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
**Common handedness of the four actual root reference rankings.**

The actual generated state is the same for all four eligible references. On that common state
the actual ordinary root keys are injective:
* the two isotope classes differ in the atom label of the slot itself;
* a tie of 28/29 would equate the actual labels at `o+`/`o-`, and a tie of 30/31 those at
  `q+ = [0,30,34,26]`/`q- = [0,31,35,26]`. The double exchange `twist` carries each occurrence to
  its partner, acts trivially on every center below them, and reverses center 26, so the two
  labels are complementary. Presence of the first label is derived.

Hence the marker of each reference is never decisive at the root: all four actual reference
rankings are literally the same permutation, on each geometry side. No label value, physical
sign, comparison outcome or reading agreement is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitRootEligibility
open LocalizedChemicalRingReferenceOrbitActualReferenceReading
open LocalizedChemicalRingReferenceConsensusSymmetry LocalizedChemicalRingReferenceConsensusStabilizer
open LocalizedChemicalRingReferenceConsensusArmSeparation (armNode armData armUnit)
open LocalizedChemicalRingReferenceConsensusArmTwin (twinNode)
open LocalizedChemicalRingReferenceConsensusContext LocalizedChemicalRingReferenceConsensusFacts
open LocalizedChemicalRingReferenceOrbitRootLabelReadback (rootUnit o_labels_of_root_tie
  q_labels_of_root_tie root_tie_pathMatch)
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingInheritedReferenceTie
open LocalizedChemicalRingCoveredPathOrientation LocalizedChemicalRingWitnessExecution
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingSelectedFactCompleteness
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedChemicalRingOrientationReadback LocalizedChemicalRingCompletenessPermutationTransport
open LocalizedChemicalRingOrientationInduction (descriptorWith_mirror_none_iff mirror_mirror)
open LocalizedChemicalRingHereditaryTie LocalizedChemicalRingActualFullLabelMatch
open LocalizedChemicalRingDecodedRelation
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking (RefinedKey)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors reached_atom_valid)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedConfigurationTransport (readback_none_of_missing)
open LocalizedMarkedDetectedFrames (detected_frame)
open LocalizedMarkedOperationEvaluator (Operations underWith tiedChildren mem_tiedChildren_actual)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedGenericMarkedRecalculation (frameAtoms? readback? mirror readback_mirror flatMap_congr_mem
  structuralDepth)

noncomputable section
open scoped Classical

private abbrev σ : Nat → Nat := relabelOf certified twistAut.val
private abbrev Geo := observedGeometry certified
private abbrev step := LocalizedChemicalRingInheritedFallback.rawStep?
private abbrev ops := sparseOperations certified mol

/-! ## The double exchange reverses exactly center 26 -/

/-- Below an occurrence whose history contains 26, the pulled-back geometry is the original. -/
private theorem agree_below (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (has26 : (26 : Nat) ∈ node.history) :
    AgreeOn (StrictDescendant mol node) mol (pullback σ (inputGeometry certified))
      (inputGeometry certified) := by
  intro below descent atoms frame L sub
  have belowReached : Reached mol below := by
    obtain ⟨child, edge, rest⟩ := descent
    exact descendant_reached (reached_child mol node child reached edge) rest
  have real : below.forcedLeaf = false := by
    cases leaf : below.forcedLeaf with
    | false => rfl
    | true =>
        rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol below leaf] at frame
        cases frame
  have outside := strictDescendant_outside_history descent real
  have valid := reached_atom_valid mol admissible.1.1 below belowReached
  have rawSingle := raw_single mol certified structure_agreement admissible.1.1 admissible.1.2
    supported single_bonded
  rcases frame_atoms_perm_neighbors mol admissible.1.1 rawSingle below belowReached atoms frame with
    ⟨four, _⟩ | ⟨three, perm⟩
  · let d : physical.Center :=
      ⟨atomOf mol certified structure_agreement below.atom valid,
        center_of_degree mol certified structure_agreement admissible.1.1 admissible.1.2 supported
          below.atom valid four⟩
    have lower : d.1 ≠ (26 : Fin 46) := by
      intro same
      apply outside
      have atom : below.atom = 26 := congrArg Fin.val same
      rw [atom]
      exact has26
    have localAction := readback_pullback_local certified mol structure_agreement admissible supported
      single_bonded cfg twistAut d (all_calibrated d) (all_calibrated _) below rfl belowReached
      atoms frame L sub
    rw [twist_relativeSign_lower cfg d lower] at localAction
    simpa only [flipBy, if_true] using localAction
  · rw [← readback_map]
    have phantomNone : inputGeometry certified mol.atomCount = none :=
      inputGeometry_outside certified _ (by rw [count mol certified structure_agreement])
    by_cases phantom : mol.atomCount ∈ L
    · have left : readback? (inputGeometry certified) (L.map σ) = none := by
        refine readback_none_of_missing _ _ (σ mol.atomCount) (List.mem_map_of_mem phantom) ?_
        have outsideValue : σ mol.atomCount = mol.atomCount :=
          relabelOf_outside certified _ _ (by rw [count mol certified structure_agreement])
        rw [outsideValue]
        exact phantomNone
      rw [left, readback_none_of_missing _ L _ phantom phantomNone]
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
      rw [readback_none_of_not_good _ _ (not_good_map _ L bad), readback_none_of_not_good _ L bad]

private theorem agree_side (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (has26 : (26 : Nat) ∈ node.history) (side : Bool) :
    AgreeOn (StrictDescendant mol node) mol (pullback σ (Geo side)) (Geo side) := by
  cases side with
  | false => exact agree_below node reached has26
  | true => exact (agree_below node reached has26).mirror

private theorem flipBy_swap (s : ℝ) (x : Option RS) :
    (flipBy s x).map RS.swap = flipBy s (x.map RS.swap) := by
  unfold flipBy
  split_ifs <;> rfl

private theorem flip_side (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atom26 : node.atom = 26) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) (side : Bool) :
    ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (pullback σ (Geo side)) L = flipBy (-1) (readback? (Geo side) L) := by
  intro L sub
  obtain ⟨fixed, negative⟩ := twist_relativeSign_other cfg
  have localAction := readback_pullback_local certified mol structure_agreement admissible supported
    single_bonded cfg twistAut otherCurrent (all_calibrated _) (all_calibrated _) node atom26 reached
    atoms frame L sub
  rw [negative] at localAction
  cases side with
  | false => exact localAction
  | true =>
      change readback? (mirror (pullback σ (inputGeometry certified))) L =
        flipBy (-1) (readback? (mirror (inputGeometry certified)) L)
      rw [readback_mirror, readback_mirror, localAction, flipBy_swap]

/-- The actual descriptor at the image occurrence is the complement of the source's. -/
theorem twist_flip (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (real : node.provenance = .realAtom) (atom26 : node.atom = 26)
    (has26 : (26 : Nat) ∈ node.history) (depth : Nat) (side : Bool) (mark : Nat) :
    descriptorWith step mol ops depth (Geo side) [] (some (σ mark)) (mapNode σ node) =
      flipDescriptorBy (-1) (descriptorWith step mol ops depth (Geo side) [] (some mark) node) := by
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
    certified mol structure_agreement admissible supported twistAut
  have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
    certified mol structure_agreement admissible supported single_bonded twistAut
  have rawSingle := raw_single mol certified structure_agreement admissible.1.1 admissible.1.2
    supported single_bonded
  have stepMap := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1 admissible.1.2
    rawSingle cov
  have mapped := descriptorWith_map sym admissible.1.1 admissible.1.2 rawSingle cov step stepMap
    depth (Geo side) (some mark) node reached
  have frame := detected_frame mol certified structure_agreement admissible supported single_bonded
    otherCurrent node reached real atom26
  have closed : ∀ parent child, StrictDescendant mol node parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol node child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  have stepCongr := LocalizedChemicalRingInheritedFallback.stepCongr mol ops
  have agree := agree_side node reached has26 side
  have below : ∀ mark', underWith mol ops (pullback σ (Geo side)) [] node
      (factsWith step mol ops depth) mark' =
      underWith mol ops (Geo side) [] node (factsWith step mol ops depth) mark' := by
    intro mark'
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol node) closed stepCongr depth _ _ agree
      [] (some mark') child ⟨child, mem_tiedChildren_actual mol ops [] node child member, .refl⟩
  have belowMirror : ∀ mark', underWith mol ops (mirror (pullback σ (Geo side))) [] node
      (factsWith step mol ops depth) mark' =
      underWith mol ops (mirror (Geo side)) [] node (factsWith step mol ops depth) mark' := by
    intro mark'
    unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol node) closed stepCongr depth _ _ agree.mirror
      [] (some mark') child ⟨child, mem_tiedChildren_actual mol ops [] node child member, .refl⟩
  have flipped := descriptorWith_flip mol ops step
    (LocalizedChemicalRingInheritedFallback.stepFlip mol ops) (-1) _ _ depth node _ frame
    (flip_side node reached atom26 _ frame side) [] (some mark) below belowMirror
  exact mapped.trans flipped

/-! ## Presence of the first label -/

/-- Injective ordinary keys on both sides give a present actual descriptor. -/
private theorem descriptor_present (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) (reference : Fin 46) (depth : Nat)
    (injective : ∀ side, Function.Injective (rawStateKeys certified single_bonded
      (gen node depth side reference.val) data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl)) (side : Bool) :
    descriptorWith step mol ops depth (Geo side) [] (some reference.val) node ≠ none := by
  intro absent
  have original : LocalizedChemicalRingInheritedFallback.descriptor? mol ops depth
      (inputGeometry certified) [] (some reference.val) node = none := by
    cases side with
    | false => exact absent
    | true =>
        exact (descriptorWith_mirror_none_iff mol ops step depth (inputGeometry certified) []
          (some reference.val) node).mp absent
  obtain ⟨reflected, left, right, _, different, tie⟩ := descriptor_none_original_reference_tie
    certified mol structure_agreement admissible supported single_bonded cfg c (all_calibrated c)
    node data depth reference original
  exact different (injective reflected (congrArg (fun key : RefinedKey => (ofLex key).1) tie))

/-! ## Same-isotope ties are impossible -/

private abbrev D := structuralDepth mol (canonicalCenterRoot 0)

private theorem depth_bound : 17 ≤ D := by decide +kernel

private theorem root_reached : Reached mol (canonicalCenterRoot 0) := reached_root mol 0 (by decide)

/-- A tie between partner root slots contradicts complementary labels. -/
private theorem pair_impossible (side : Bool) (first second : List (Fin 46))
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
    (armPath : Reached mol nPlus) (real : nPlus.provenance = .realAtom) (atom26 : nPlus.atom = 26)
    (has26 : (26 : Nat) ∈ nPlus.history)
    (image : mapNode σ nPlus = nMinus)
    (present : ∀ depth, 13 ≤ depth →
      descriptorWith step mol ops depth (Geo side) [] (some 28) nPlus ≠ none)
    (independent : ∀ depth, 18 ≤ nMinus.history.length + depth →
      descriptorWith step mol ops depth (Geo side) [] (some 29) nMinus =
        descriptorWith step mol ops depth (Geo side) [] (some 28) nMinus)
    (labels : ((gen (canonicalCenterRoot 0) D side 28).factAt? nPlus).map factLabel =
      ((gen (canonicalCenterRoot 0) D side 28).factAt? nMinus).map factLabel) : False := by
  have bound := depth_bound
  have rootLength : (canonicalCenterRoot 0).history.length = 1 := rfl
  have adequate : nPlus.history.length ≤ D + (canonicalCenterRoot 0).history.length := by omega
  have remainingBound : 13 ≤ D + (canonicalCenterRoot 0).history.length - nPlus.history.length := by
    omega
  cases observed : ((gen (canonicalCenterRoot 0) D side 28).factAt? nPlus).map factLabel with
  | none =>
      exact present _ remainingBound
        (underWith_absence_refusal step mol ops D (Geo side) [] (canonicalCenterRoot 0) child nPlus
          28 selected path adequate observed)
  | some label =>
      have rawMatched : ((gen (canonicalCenterRoot 0) D side 28).factAt?
          (rawPathNode (0 : Fin 46) first)).map factLabel =
          ((gen (canonicalCenterRoot 0) D side 28).factAt?
            (rawPathNode (0 : Fin 46) second)).map factLabel := by
        rw [rawPlus, rawMinus]
        exact labels
      have rawObserved : ((gen (canonicalCenterRoot 0) D side 28).factAt?
          (rawPathNode (0 : Fin 46) first)).map factLabel = some label := by
        rw [rawPlus]
        exact observed
      obtain ⟨plusDescriptor, minusDescriptor⟩ := matched_paths_execute (0 : Fin 46) first second
        sameLength step mol ops D (Geo side) [] (canonicalCenterRoot 0) root_reached 28
        rawMatched label rawObserved
      rw [rawPlus] at plusDescriptor
      rw [rawMinus] at minusDescriptor
      have remainingBound' : 18 ≤ nMinus.history.length +
          (D + (canonicalCenterRoot 0).history.length - (first.length + 1)) := by
        omega
      have flipped := twist_flip nPlus armPath real atom26 has26
        (D + (canonicalCenterRoot 0).history.length - (first.length + 1)) side 28
      have sigma28 : σ 28 = 29 := relabelOf_val certified twistAut.val (28 : Fin 46)
      rw [sigma28, image, independent _ remainingBound', minusDescriptor, plusDescriptor] at flipped
      have impossible := flipDescriptorBy_some_eq (-1) (Or.inr rfl) label flipped.symm
      norm_num at impossible

private theorem armNode_descends : Descends mol (nodeOf [0, 28]) armNode := plus_descends

private theorem twinNode_descends : Descends mol (nodeOf [0, 29]) twinNode :=
  LocalizedChemicalRingReferenceConsensusArmTwin.twin_descends

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

private theorem arm_reached (a : Fin 46) (allowed : RootMark a) :
    Reached mol (nodeOf [0, a.val]) := by
  refine reached_child mol (canonicalCenterRoot 0) _ root_reached ?_
  rcases allowed with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem armNode_image : mapNode σ armNode = twinNode := by
  have mapped := LocalizedChemicalRingWitnessPhysicalExecution.rawPathNode_map certified twistAut.val
    (0 : Fin 46) ([28, 32, 27, 26] : List (Fin 46))
  exact mapped

private theorem qPlus_image : mapNode σ qPlus = qMinus := by
  have mapped := LocalizedChemicalRingWitnessPhysicalExecution.rawPathNode_map certified twistAut.val
    (0 : Fin 46) ([30, 34, 26] : List (Fin 46))
  exact mapped

private theorem o_pair_impossible (side : Bool) (left right : Fin 4)
    (atLeft : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = (28 : Fin 46))
    (atRight : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = (29 : Fin 46))
    (tie : rawStateKeys certified single_bonded (gen (canonicalCenterRoot 0) D side 28)
        rootData.target rootData.real rootUnit rfl left =
      rawStateKeys certified single_bonded (gen (canonicalCenterRoot 0) D side 28)
        rootData.target rootData.real rootUnit rfl right) : False := by
  apply pair_impossible side [28, 32, 27, 26] [29, 33, 27, 26] armNode twinNode rfl rfl rfl rfl rfl
    (by decide) (nodeOf [0, 28]) LocalizedChemicalRingReferenceOrbitBranch.shortcut_selected_first_child
    armNode_descends
    (descendant_reached (arm_reached 28 (Or.inl rfl)) armNode_descends) rfl rfl (by decide)
    armNode_image
  · intro depth adequate
    exact descriptor_present otherCurrent armNode armData 28 depth
      (fun s => plus_injective s depth adequate) side
  · intro depth adequate
    exact arm_descriptor_independent depth twinNode 29 (Or.inr (Or.inl rfl)) twinNode_descends
      adequate side 29 28 (Or.inr (Or.inl rfl)) (Or.inl rfl)
  · exact o_labels_of_root_tie _ left right atLeft atRight tie

/-- `q+` has injective ordinary keys in every state: the classification excludes any tie. -/
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

private theorem q_pair_impossible (side : Bool) (left right : Fin 4)
    (atLeft : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = (30 : Fin 46))
    (atRight : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = (31 : Fin 46))
    (tie : rawStateKeys certified single_bonded (gen (canonicalCenterRoot 0) D side 28)
        rootData.target rootData.real rootUnit rfl left =
      rawStateKeys certified single_bonded (gen (canonicalCenterRoot 0) D side 28)
        rootData.target rootData.real rootUnit rfl right) : False := by
  have qReached : Reached mol qPlus :=
    descendant_reached (arm_reached 30 (Or.inr (Or.inr (Or.inl rfl)))) qPlus_descends
  obtain ⟨data⟩ := occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded otherCurrent qPlus qReached rfl rfl
  apply pair_impossible side [30, 34, 26] [31, 35, 26] qPlus qMinus rfl rfl rfl rfl rfl (by decide)
    (nodeOf [0, 30]) LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_selected_first_child
    qPlus_descends qReached rfl rfl (by decide) qPlus_image
  · intro depth _
    exact descriptor_present otherCurrent qPlus data 28 depth (fun s => q_injective _ data) side
  · intro depth adequate
    exact arm_descriptor_independent depth qMinus 31 (Or.inr (Or.inr (Or.inr rfl))) qMinus_descends
      adequate side 29 28 (Or.inr (Or.inl rfl)) (Or.inl rfl)
  · exact q_labels_of_root_tie _ left right atLeft atRight tie

/-! ## Injectivity of the ordinary root keys -/

/-- Slots with different isotopes never tie: their atom labels differ. -/
private theorem isotope_impossible (state : OccurrenceAuxState) (left right : Fin 4) (a b : Fin 46)
    (atLeft : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = a)
    (atRight : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = b)
    (masses : graph.atomMass a ≠ graph.atomMass b)
    (tie : rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl left =
      rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl right) :
    False := by
  obtain ⟨x, y, _, _, nodeL, nodeR, keyL, keyR, builtL, builtR, tied⟩ :=
    root_tie_pathMatch state left right a b atLeft atRight tie
  obtain ⟨treeL, treeR, sourceL, sourceR, realL, realR, same⟩ :=
    full_tie_same_observations _ _ _ _ _ _ _ _ builtL builtR
      (congrArg ConstitutionalRule5Comparison.ordering tied)
  have label := related_atomLabel (shape_eq_of_observation_eq treeL treeR same) realL realR
    (shapePositionCursorRelation_sources _ sourceL sourceR)
  rw [nodeL, nodeR, officialNodeAtomLabel_eq_of_observed (input := certified) rfl rfl,
    officialNodeAtomLabel_eq_of_observed (input := certified) rfl rfl] at label
  exact masses (congrArg (fun value => (ofLex value).2) label)

private theorem slot_mark (slot : Fin 4) :
    RootMark (referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot) := by
  have adjacent : graph.Adj 0 (referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot) :=
    physical.ligandAtomAt_adj rootCenter (rootData.ligandOf slot)
  have finite : ∀ a : Fin 46, graph.Adj 0 a → RootMark a := by
    intro a
    unfold RootMark
    fin_cases a <;> decide +kernel
  exact finite _ adjacent

/-- **The actual ordinary root keys are injective on the common generated state.** -/
theorem root_prior_injective (side : Bool) :
    Function.Injective (rawStateKeys certified single_bonded (gen (canonicalCenterRoot 0) D side 28)
      rootData.target rootData.real rootUnit rfl) := by
  intro left right tie
  by_contra different
  have distinct : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left ≠
      referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right :=
    fun same => different (referenceAt_injective rootCenter _ rootData same)
  have m16 : graph.atomMass (28 : Fin 46) = graph.atomMass (29 : Fin 46) := by decide +kernel
  have cross : graph.atomMass (28 : Fin 46) ≠ graph.atomMass (30 : Fin 46) := by decide +kernel
  have cross29 : graph.atomMass (29 : Fin 46) ≠ graph.atomMass (30 : Fin 46) := m16 ▸ cross
  have cross31 : graph.atomMass (28 : Fin 46) ≠ graph.atomMass (31 : Fin 46) := by decide +kernel
  have cross2931 : graph.atomMass (29 : Fin 46) ≠ graph.atomMass (31 : Fin 46) := m16 ▸ cross31
  rcases slot_mark left with h | h | h | h <;> rcases slot_mark right with g | g | g | g
  · exact distinct (h.trans g.symm)
  · exact o_pair_impossible side left right h g tie
  · exact isotope_impossible _ left right _ _ h g cross tie
  · exact isotope_impossible _ left right _ _ h g cross31 tie
  · exact o_pair_impossible side right left g h tie.symm
  · exact distinct (h.trans g.symm)
  · exact isotope_impossible _ left right _ _ h g cross29 tie
  · exact isotope_impossible _ left right _ _ h g cross2931 tie
  · exact isotope_impossible _ right left _ _ g h cross tie.symm
  · exact isotope_impossible _ right left _ _ g h cross29 tie.symm
  · exact distinct (h.trans g.symm)
  · exact q_pair_impossible side left right h g tie
  · exact isotope_impossible _ right left _ _ g h cross31 tie.symm
  · exact isotope_impossible _ right left _ _ g h cross2931 tie.symm
  · exact q_pair_impossible side right left g h tie.symm
  · exact distinct (h.trans g.symm)

private theorem eligible_mark (mark : Fin 46) (member : mark.val ∈ rootEligible) : RootMark mark := by
  have values := (root_eligible_iff mark.val).mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at values
  rcases values with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- **Each actual reference ranking is the common ordinary ranking.** -/
theorem referenceRank_eq_common (side : Bool) (mark : Fin 46) (member : mark.val ∈ rootEligible) :
    referenceRank side mark =
      rank certified mol rootCenter (canonicalCenterRoot 0) rootData
        (rawStateKeys certified single_bonded (gen (canonicalCenterRoot 0) D side 28)
          rootData.target rootData.real rootUnit rfl) := by
  have same := generated_independent side mark 28 (eligible_mark mark member) (Or.inl rfl)
  have stateEq : gen (canonicalCenterRoot 0) D side mark.val = gen (canonicalCenterRoot 0) D side 28 :=
    same
  unfold referenceRank
  change rank certified mol rootCenter (canonicalCenterRoot 0) rootData
    (markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
      (gen (canonicalCenterRoot 0) D side mark.val) mark) = _
  rw [stateEq]
  exact rank_marked_eq rootCenter _ rootData _ mark (root_prior_injective side)

/-- **Common handedness.** All actually eligible root references rank the ligands with the
same permutation, separately under the original and the reflected geometry. -/
theorem referenceRank_common (side : Bool) (first second : Fin 46)
    (firstEligible : first.val ∈ rootEligible) (secondEligible : second.val ∈ rootEligible) :
    referenceRank side first = referenceRank side second := by
  rw [referenceRank_eq_common side first firstEligible, referenceRank_eq_common side second secondEligible]

/-- The parity form requested for the no-context consensus. -/
theorem referenceRank_handedness (side : Bool) (first second : Fin 46)
    (firstEligible : first.val ∈ rootEligible) (secondEligible : second.val ∈ rootEligible) :
    permHandedness (referenceRank side first) = permHandedness (referenceRank side second) := by
  rw [referenceRank_common side first second firstEligible secondEligible]

/-- All four actual inherited root readings agree on each geometry side. -/
theorem actualReading_consensus (side : Bool) (first second : Fin 46)
    (firstEligible : first.val ∈ rootEligible) (secondEligible : second.val ∈ rootEligible) :
    actualReading side first = actualReading side second :=
  actualReading_eq_of_parity side first second firstEligible secondEligible
    (referenceRank_handedness side first second firstEligible secondEligible)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot.twist_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot.root_prior_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot.referenceRank_eq_common
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot.referenceRank_common
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot.referenceRank_handedness
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusRoot.actualReading_consensus
