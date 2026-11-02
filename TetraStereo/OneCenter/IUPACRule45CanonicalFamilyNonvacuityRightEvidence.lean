import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuityLeftEvidence

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace Rule45CanonicalFamilyNonvacuity

open AuthoritativeChemicalInput
open CertifiedLocalizedCIPInput

/-! ## Generic strict-four-ligand compiler used by the mirrored branch -/

theorem compareAt_of_rule3_gt
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (keys.keyAt left).rule3 (keys.keyAt right).rule3 = .gt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simp [AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At,
    strict]

theorem compareAt_of_rule3_lt
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (keys.keyAt left).rule3 (keys.keyAt right).rule3 = .lt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right =
      ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simp [AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At,
    strict]

theorem safeTracked_strict_iodine_bromine_carbon_hydrogen
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (zeroOne : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionZero positionOne = { ordering := .lt, pseudo := false })
    (zeroTwo : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionZero positionTwo = { ordering := .lt, pseudo := false })
    (oneTwo : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionOne positionTwo = { ordering := .lt, pseudo := false })
    (zeroThree : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionZero positionThree = { ordering := .gt, pseudo := false })
    (twoOne : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionTwo positionOne = { ordering := .gt, pseudo := false })
    (twoZero : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionTwo positionZero = { ordering := .gt, pseudo := false })
    (twoThree : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionTwo positionThree = { ordering := .gt, pseudo := false })
    (oneZero : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionOne positionZero = { ordering := .gt, pseudo := false })
    (oneThree : source.compareAromaticCanonicalOccurrenceRule3Through5At
      keys positionOne positionThree = { ordering := .gt, pseudo := false }) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some leftTracked := by
  have raw : source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      some leftTracked := by
    unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5TrackedOrder?
    rw [sortFourLocalizedLigandsTracked, sortLocalizedLigandsTracked, finRange_four]
    norm_num [AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At?,
      AuthoritativeChemicalInput.aromaticCanonicalRule3Through5DescriptorComparison,
      sortLocalizedLigandsTrackedFrom, insertLocalizedLigandTracked,
      zeroOne, zeroTwo, oneTwo, zeroThree, leftTracked]
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      keys leftTracked.highestFirst = true := by
    norm_num [AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5OrderCoherent,
      AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5OrderPairStrict,
      leftTracked, twoOne, twoZero, twoThree, oneZero, oneThree, zeroThree]
  simp [AuthoritativeChemicalInput.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
    raw, coherent]

/-! ## Mirrored right branch -/

def rawCenterSix : Fin rawMolecule.atomCount := ⟨6, by decide⟩

def rawCenterSixSpec : AtomSpec :=
  { element := .C
    explicitHydrogens? := some 0
    tetrahedral? := some .clockwise }

theorem raw_center_six_frame :
    rawMolecule.OrdinaryConnectivityOnlyTetrahedralFrameAt rawCenterSix := by
  refine ⟨⟨rawCenterSixSpec, by decide, by decide, by decide⟩, by decide⟩

def rightCenterAtom : source.AromaticCanonicalAtom :=
  rawMolecule.convertedAtomIndex source converted rawCenterSix

theorem right_center_detected :
    rightCenterAtom ∈ source.aromaticCanonicalTetrahedralCenterSet := by
  exact (rawMolecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_convertedCenter_mem
    source converted raw_writtenExact raw_resolved rawCenterSix).mp raw_center_six_frame

def rightCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨rightCenterAtom, right_center_detected⟩

@[simp] theorem rightCenterAtom_eq_branchAtomSix :
    rightCenterAtom = branchAtomSix := by
  apply Fin.ext
  rfl

set_option maxRecDepth 10000 in
theorem right_center_computed :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? rightOccurrence = some rightCenter := by
  classical
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceTetrahedralCenter?
  have real : rightOccurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
    rfl
  rw [dif_pos real]
  have current : rightOccurrence.1.node.current? = some rightCenterAtom := by
    rw [rightCenterAtom_eq_branchAtomSix]
    exact rootAt_three_current
  rw [current]
  simp only
  rw [dif_pos right_center_detected]
  rfl

noncomputable def rightRoots : List (source.AromaticCanonicalRerootCursor carrierFuel) :=
  source.aromaticCanonicalRerootChildren { occurrence := rightOccurrence, previous? := none }

set_option maxRecDepth 10000 in
theorem right_roots_length : rightRoots.length = 4 := by
  rfl

noncomputable def rightBase : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel :=
  { roots := rightRoots, rootsLength := right_roots_length }

set_option maxRecDepth 10000 in
theorem right_base_computed :
    source.aromaticCanonicalOccurrenceFourLigandFrame? rightOccurrence = some rightBase := by
  rfl

set_option maxRecDepth 10000 in
theorem right_roots_computed :
    source.aromaticCanonicalOccurrenceLigandFrame? rightOccurrence = some rightRoots := by
  rfl

theorem right_roots_valid :
    ∀ cursor ∈ rightRoots, source.AromaticCanonicalRerootCursorValid cursor :=
  source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid
    rightOccurrence rightRoots right_roots_computed

theorem right_rule3_topology : ∀ rawKeys,
    rightRoots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel) =
        some rawKeys →
      source.AromaticCanonicalRule3TopologyUnambiguous rawKeys := by
  intro rawKeys computed
  exact (source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_noDouble
    source_no_ordinary_double_bond rightRoots rawKeys computed).2.2

theorem right_rule3_frame_exists :
    ∃ frame, source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      ruleFuel rightRoots = some frame := by
  obtain ⟨frame, computed⟩ :=
    source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_at_twice
      left_rule3_resolved rightRoots right_roots_valid (by
        intro rawKeys rawComputed
        exact right_rule3_topology rawKeys (by
          simpa [carrierFuel, ruleFuel] using rawComputed))
  exact ⟨frame, by simpa [carrierFuel, ruleFuel] using computed⟩

noncomputable def rightRule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame :=
  Classical.choose right_rule3_frame_exists

theorem right_rule3_frame_computed :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? ruleFuel rightRoots =
      some rightRule3Frame :=
  Classical.choose_spec right_rule3_frame_exists

theorem right_rule3_frame_length : rightRule3Frame.keys.length = 4 := by
  have canonical :=
    (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
      ruleFuel rightRoots rightRule3Frame).mp right_rule3_frame_computed
  rw [canonical_rule3_except_list_length canonical.2.2.2, right_roots_length]

private theorem exists_mapM_right_rule45 :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key?
          rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence)
          ruleFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
          rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence)
          cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ := exists_mapM_right_rule45 cursors
        (fun child present => valid child (by simp [present]))
      have keyComputed' :
          source.buildAromaticCanonicalRerootCompoundRule45Key? rightOccurrence
              (source.aromaticCanonicalDependencyView state rightOccurrence)
              ruleFuel cursor = some key := by
        simpa [carrierFuel, ruleFuel] using keyComputed
      refine ⟨key :: keys, ?_⟩
      rw [List.mapM_cons, keyComputed', keysComputed]
      rfl

theorem right_rule45_keys_exists :
    ∃ keys, rightRoots.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45Key?
        rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence)
          ruleFuel) = some keys :=
  exists_mapM_right_rule45 rightRoots right_roots_valid

noncomputable def rightRule45Keys : List source.AromaticCanonicalRerootCompoundRule45Key :=
  Classical.choose right_rule45_keys_exists

theorem right_rule45_keys_computed :
    rightRoots.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45Key?
        rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence)
          ruleFuel) = some rightRule45Keys :=
  Classical.choose_spec right_rule45_keys_exists

theorem right_rule45_keys_length : rightRule45Keys.length = 4 := by
  rw [mapM_length_eq_of_eq_some
    (source.buildAromaticCanonicalRerootCompoundRule45Key?
      rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence) ruleFuel)
    rightRoots rightRule45Keys right_rule45_keys_computed, right_roots_length]

noncomputable def rightKeysExplicit :
    source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel :=
  { rule3Frame := rightRule3Frame
    rule3Length := right_rule3_frame_length
    rule45Keys := rightRule45Keys
    rule45Length := right_rule45_keys_length }

theorem right_keys_explicit_computed :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence)
        ruleFuel rightRoots = some rightKeysExplicit := by
  unfold AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
  rw [right_rule3_frame_computed]
  simp [right_rule3_frame_length, right_rule45_keys_computed,
    right_rule45_keys_length, rightKeysExplicit]

noncomputable def rightCursorAt (position : Fin 4) :
    source.AromaticCanonicalRerootCursor carrierFuel :=
  rightRoots.get (Fin.cast right_roots_length.symm position)

noncomputable def rightRule3KeyAt (position : Fin 4) :
    source.AromaticCanonicalUncancelledRule3SpatialKey :=
  rightRule3Frame.keys.get (Fin.cast right_rule3_frame_length.symm position)

theorem rightRule3KeyAt_canonical (position : Fin 4) :
    source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      rightRule3Frame.excluded ruleFuel (rightCursorAt position) (rightRule3KeyAt position) := by
  have frameCanonical :=
    (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
      ruleFuel rightRoots rightRule3Frame).mp right_rule3_frame_computed
  have pointwise := canonical_rule3_except_list_forall₂ frameCanonical.2.2.2
  exact pointwise.get (by rw [right_roots_length]; exact position.2)
    (by rw [right_rule3_frame_length]; exact position.2)

set_option maxRecDepth 10000 in
theorem right_cursor_rule1a_zero :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (rightCursorAt positionZero).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 6 := by
  rfl

set_option maxRecDepth 10000 in
theorem right_cursor_rule1a_one :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (rightCursorAt positionOne).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 35 := by
  rfl

set_option maxRecDepth 10000 in
theorem right_cursor_rule1a_two :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (rightCursorAt positionTwo).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 53 := by
  rfl

set_option maxRecDepth 10000 in
theorem right_cursor_rule1a_three :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (rightCursorAt positionThree).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 1 := by
  rfl

theorem right_rule3_compare_gt
    (left right : Fin 4) (leftZ rightZ : Nat)
    (leftObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (rightCursorAt left).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat leftZ)
    (rightObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (rightCursorAt right).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat rightZ)
    (higher : rightZ < leftZ) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt left) (rightRule3KeyAt right) = .gt :=
  rule3_compare_gt_of_canonical_atomic_heads
    (rightRule3KeyAt_canonical left) (rightRule3KeyAt_canonical right)
    leftZ rightZ leftObservation rightObservation higher

theorem right_rule3_compare_lt
    (left right : Fin 4) (leftZ rightZ : Nat)
    (leftObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (rightCursorAt left).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat leftZ)
    (rightObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (rightCursorAt right).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat rightZ)
    (lower : leftZ < rightZ) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt left) (rightRule3KeyAt right) = .lt :=
  rule3_compare_lt_of_canonical_atomic_heads
    (rightRule3KeyAt_canonical left) (rightRule3KeyAt_canonical right)
    leftZ rightZ leftObservation rightObservation lower

theorem right_rule3_two_one :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionTwo) (rightRule3KeyAt positionOne) = .gt :=
  right_rule3_compare_gt positionTwo positionOne 53 35
    right_cursor_rule1a_two right_cursor_rule1a_one (by decide)

theorem right_rule3_two_zero :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionTwo) (rightRule3KeyAt positionZero) = .gt :=
  right_rule3_compare_gt positionTwo positionZero 53 6
    right_cursor_rule1a_two right_cursor_rule1a_zero (by decide)

theorem right_rule3_two_three :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionTwo) (rightRule3KeyAt positionThree) = .gt :=
  right_rule3_compare_gt positionTwo positionThree 53 1
    right_cursor_rule1a_two right_cursor_rule1a_three (by decide)

theorem right_rule3_one_zero :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionOne) (rightRule3KeyAt positionZero) = .gt :=
  right_rule3_compare_gt positionOne positionZero 35 6
    right_cursor_rule1a_one right_cursor_rule1a_zero (by decide)

theorem right_rule3_one_three :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionOne) (rightRule3KeyAt positionThree) = .gt :=
  right_rule3_compare_gt positionOne positionThree 35 1
    right_cursor_rule1a_one right_cursor_rule1a_three (by decide)

theorem right_rule3_zero_three :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionZero) (rightRule3KeyAt positionThree) = .gt :=
  right_rule3_compare_gt positionZero positionThree 6 1
    right_cursor_rule1a_zero right_cursor_rule1a_three (by decide)

theorem right_rule3_zero_one :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionZero) (rightRule3KeyAt positionOne) = .lt :=
  right_rule3_compare_lt positionZero positionOne 6 35
    right_cursor_rule1a_zero right_cursor_rule1a_one (by decide)

theorem right_rule3_zero_two :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionZero) (rightRule3KeyAt positionTwo) = .lt :=
  right_rule3_compare_lt positionZero positionTwo 6 53
    right_cursor_rule1a_zero right_cursor_rule1a_two (by decide)

theorem right_rule3_one_two :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt positionOne) (rightRule3KeyAt positionTwo) = .lt :=
  right_rule3_compare_lt positionOne positionTwo 35 53
    right_cursor_rule1a_one right_cursor_rule1a_two (by decide)

@[simp] theorem rightKeysExplicit_rule3_keyAt (position : Fin 4) :
    (rightKeysExplicit.keyAt position).rule3 = rightRule3KeyAt position := by
  rfl

theorem right_compare_gt (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt left) (rightRule3KeyAt right) = .gt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
      rightKeysExplicit left right = { ordering := .gt, pseudo := false } := by
  apply compareAt_of_rule3_gt
  simpa using strict

theorem right_compare_lt (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (rightRule3KeyAt left) (rightRule3KeyAt right) = .lt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
      rightKeysExplicit left right = { ordering := .lt, pseudo := false } := by
  apply compareAt_of_rule3_lt
  simpa using strict

theorem right_tracked_computed :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? rightKeysExplicit =
      some leftTracked := by
  apply safeTracked_strict_iodine_bromine_carbon_hydrogen
  · exact right_compare_lt positionZero positionOne right_rule3_zero_one
  · exact right_compare_lt positionZero positionTwo right_rule3_zero_two
  · exact right_compare_lt positionOne positionTwo right_rule3_one_two
  · exact right_compare_gt positionZero positionThree right_rule3_zero_three
  · exact right_compare_gt positionTwo positionOne right_rule3_two_one
  · exact right_compare_gt positionTwo positionZero right_rule3_two_zero
  · exact right_compare_gt positionTwo positionThree right_rule3_two_three
  · exact right_compare_gt positionOne positionZero right_rule3_one_zero
  · exact right_compare_gt positionOne positionThree right_rule3_one_three

@[simp] theorem rightBase_cursorAt_eq_rightCursorAt (position : Fin 4) :
    rightBase.cursorAt position = rightCursorAt position := by
  rfl

set_option maxRecDepth 10000 in
theorem right_cursor_point_two :
    source.aromaticCanonicalRerootSpatialPoint? (rightCursorAt positionTwo) =
      some (symmetricPoint 8) := by
  rfl

set_option maxRecDepth 10000 in
theorem right_cursor_point_one :
    source.aromaticCanonicalRerootSpatialPoint? (rightCursorAt positionOne) =
      some (symmetricPoint 7) := by
  rfl

set_option maxRecDepth 10000 in
theorem right_cursor_point_zero :
    source.aromaticCanonicalRerootSpatialPoint? (rightCursorAt positionZero) =
      some (symmetricPoint 1) := by
  rfl

set_option maxRecDepth 10000 in
theorem right_cursor_point_three :
    source.aromaticCanonicalRerootSpatialPoint? (rightCursorAt positionThree) =
      some (symmetricPoint 10) := by
  rfl

theorem right_points_computed :
    leftTracked.highestFirst.mapM (fun index =>
      source.aromaticCanonicalRerootSpatialPoint? (rightBase.cursorAt index)) =
        some rightPriorityPoints := by
  simp [leftTracked, rightPriorityPoints, right_cursor_point_two,
    right_cursor_point_one, right_cursor_point_zero, right_cursor_point_three]

noncomputable def rightEvidence :
    source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel :=
  { center := rightCenter
    base := rightBase
    keys := rightKeysExplicit
    tracked := leftTracked
    points := rightPriorityPoints }

theorem right_evidence_computed :
    source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
      rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence) ruleFuel =
        some rightEvidence := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
  rw [right_center_computed, right_base_computed]
  change ((source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      rightOccurrence (source.aromaticCanonicalDependencyView state rightOccurrence)
        ruleFuel rightRoots).bind fun keys =>
      (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys).bind fun tracked =>
        (tracked.highestFirst.mapM fun index =>
          source.aromaticCanonicalRerootSpatialPoint? (rightBase.cursorAt index)).bind fun points =>
            some { center := rightCenter, base := rightBase, keys, tracked, points }) =
      some rightEvidence
  rw [right_keys_explicit_computed]
  simp only [Option.bind_some]
  rw [right_tracked_computed]
  simp only [Option.bind_some]
  rw [right_points_computed]
  rfl

/-- The mirrored right branch has exact oriented volume `-3`; under the corrected contract
negative volume is `R`. -/
theorem right_evidence_geometry :
    RationalTetrahedralDescriptor rightEvidence.points .R := by
  exact (descriptorOfPriorityOrderedPoints?_eq_some_iff rightPriorityPoints .R).mp
    rightPriorityPoints_descriptor

theorem right_state_chiral_R : state rightOccurrence = some (.chiral .R) := by
  have assigned := source.aromaticCanonicalOccurrenceRule3Through5Model_eq_some_of_spatialEvidence
    state (source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics)
    rightOccurrence rightEvidence .R right_evidence_computed right_evidence_geometry
  simpa [rightEvidence, leftTracked] using assigned

/-- Historical API key retained for the pinned kernel certificate.  The corrected tetrahedral
contract makes the right branch `R`, so this declaration's statement is the corrected one; the
accurately named sibling is `right_state_chiral_R`. -/
theorem right_state_chiral_S : state rightOccurrence = some (.chiral .R) :=
  right_state_chiral_R

end Rule45CanonicalFamilyNonvacuity
end IUPACNormativeProvision
end TetraStereo.OneCenter
