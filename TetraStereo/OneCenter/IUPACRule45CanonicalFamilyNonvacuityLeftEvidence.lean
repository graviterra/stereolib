import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuity

set_option autoImplicit false

namespace TetraStereo.OneCenter.IUPACNormativeProvision
namespace Rule45CanonicalFamilyNonvacuity

open AuthoritativeChemicalInput
open CertifiedLocalizedCIPInput

def rawCenterThree : Fin rawMolecule.atomCount := ⟨3, by decide⟩

def rawCenterThreeSpec : AtomSpec :=
  { element := .C
    explicitHydrogens? := some 0
    tetrahedral? := some .anticlockwise }

theorem raw_center_three_frame :
    rawMolecule.OrdinaryConnectivityOnlyTetrahedralFrameAt rawCenterThree := by
  refine ⟨⟨rawCenterThreeSpec, by decide, by decide, by decide⟩, by decide⟩

def leftCenterAtom : source.AromaticCanonicalAtom :=
  rawMolecule.convertedAtomIndex source converted rawCenterThree

theorem left_center_detected :
    leftCenterAtom ∈ source.aromaticCanonicalTetrahedralCenterSet := by
  exact (rawMolecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_convertedCenter_mem
    source converted raw_writtenExact raw_resolved rawCenterThree).mp raw_center_three_frame

def leftCenter : source.AromaticCanonicalTetrahedralCenter :=
  ⟨leftCenterAtom, left_center_detected⟩

@[simp] theorem leftCenterAtom_eq_branchAtomThree :
    leftCenterAtom = branchAtomThree := by
  apply Fin.ext
  rfl

set_option maxRecDepth 10000 in
theorem left_center_computed :
    source.aromaticCanonicalOccurrenceTetrahedralCenter? leftOccurrence = some leftCenter := by
  classical
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceTetrahedralCenter?
  have real : leftOccurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
    rfl
  rw [dif_pos real]
  have current : leftOccurrence.1.node.current? = some leftCenterAtom := by
    rw [leftCenterAtom_eq_branchAtomThree]
    exact rootAt_two_current
  rw [current]
  simp only
  rw [dif_pos left_center_detected]
  rfl

noncomputable def leftRoots : List (source.AromaticCanonicalRerootCursor carrierFuel) :=
  source.aromaticCanonicalRerootChildren { occurrence := leftOccurrence, previous? := none }

set_option maxRecDepth 10000 in
theorem left_roots_length : leftRoots.length = 4 := by
  rfl

noncomputable def leftBase : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel :=
  { roots := leftRoots, rootsLength := left_roots_length }

set_option maxRecDepth 10000 in
theorem left_base_computed :
    source.aromaticCanonicalOccurrenceFourLigandFrame? leftOccurrence = some leftBase := by
  rfl

set_option maxRecDepth 10000 in
theorem left_roots_computed :
    source.aromaticCanonicalOccurrenceLigandFrame? leftOccurrence = some leftRoots := by
  rfl

theorem left_roots_valid :
    ∀ cursor ∈ leftRoots, source.AromaticCanonicalRerootCursorValid cursor :=
  source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid
    leftOccurrence leftRoots left_roots_computed

theorem left_rule3_resolved :
    source.AromaticCanonicalRule3SpatiallyResolved carrierFuel :=
  source.aromaticCanonicalRule3SpatiallyResolved_of_noDouble
    source_no_ordinary_double_bond carrierFuel

theorem left_rule3_topology : ∀ rawKeys,
    leftRoots.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey? ruleFuel) =
        some rawKeys →
      source.AromaticCanonicalRule3TopologyUnambiguous rawKeys := by
  intro rawKeys computed
  exact (source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_noDouble
    source_no_ordinary_double_bond leftRoots rawKeys computed).2.2

theorem canonical_rule3_except_list_length
    {fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (canonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    keys.length = cursors.length :=
  match canonical with
  | .nil _ => rfl
  | .cons _ tail => by
      simp [canonical_rule3_except_list_length tail]

private theorem exists_mapM_left_rule45 :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45Key?
          leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence)
          ruleFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨key, keyComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
          leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence)
          cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ := exists_mapM_left_rule45 cursors
        (fun child present => valid child (by simp [present]))
      have keyComputed' :
          source.buildAromaticCanonicalRerootCompoundRule45Key? leftOccurrence
              (source.aromaticCanonicalDependencyView state leftOccurrence)
              ruleFuel cursor = some key := by
        simpa [carrierFuel, ruleFuel] using keyComputed
      refine ⟨key :: keys, ?_⟩
      rw [List.mapM_cons, keyComputed', keysComputed]
      rfl

theorem left_rule3_frame_exists :
    ∃ frame, source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      ruleFuel leftRoots = some frame := by
  obtain ⟨frame, computed⟩ :=
    source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_at_twice
      left_rule3_resolved leftRoots left_roots_valid (by
        intro rawKeys rawComputed
        exact left_rule3_topology rawKeys (by
          simpa [carrierFuel, ruleFuel] using rawComputed))
  exact ⟨frame, by simpa [carrierFuel, ruleFuel] using computed⟩

noncomputable def leftRule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame :=
  Classical.choose left_rule3_frame_exists

theorem left_rule3_frame_computed :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? ruleFuel leftRoots =
      some leftRule3Frame :=
  Classical.choose_spec left_rule3_frame_exists

theorem left_rule3_frame_length : leftRule3Frame.keys.length = 4 := by
  have canonical :=
    (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
      ruleFuel leftRoots leftRule3Frame).mp left_rule3_frame_computed
  rw [canonical_rule3_except_list_length canonical.2.2.2, left_roots_length]

theorem canonical_rule3_except_list_forall₂
    {fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (canonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    List.Forall₂
      (source.CanonicalAromaticCanonicalRule3SpatialKeyExcept excluded fuel)
      cursors keys :=
  match canonical with
  | .nil _ => .nil
  | .cons head tail => .cons head (canonical_rule3_except_list_forall₂ tail)

theorem canonical_rule3_key_constitutional_head
    {fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (canonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      excluded fuel cursor key) :
    key.constitutional.sourceNodes.head? =
      some [([], cursor.occurrence.1.node)] := by
  cases canonical <;> rfl

noncomputable def leftCursorAt (position : Fin 4) :
    source.AromaticCanonicalRerootCursor carrierFuel :=
  leftRoots.get (Fin.cast left_roots_length.symm position)

noncomputable def leftRule3KeyAt (position : Fin 4) :
    source.AromaticCanonicalUncancelledRule3SpatialKey :=
  leftRule3Frame.keys.get (Fin.cast left_rule3_frame_length.symm position)

theorem leftRule3KeyAt_canonical (position : Fin 4) :
    source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      leftRule3Frame.excluded ruleFuel (leftCursorAt position) (leftRule3KeyAt position) := by
  have frameCanonical :=
    (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
      ruleFuel leftRoots leftRule3Frame).mp left_rule3_frame_computed
  have pointwise := canonical_rule3_except_list_forall₂ frameCanonical.2.2.2
  exact pointwise.get (by simp [left_roots_length])
    (by simp [left_rule3_frame_length])

theorem leftRule3KeyAt_constitutional_head (position : Fin 4) :
    (leftRule3KeyAt position).constitutional.sourceNodes.head? =
      some [([], (leftCursorAt position).occurrence.1.node)] :=
  canonical_rule3_key_constitutional_head (leftRule3KeyAt_canonical position)

set_option maxRecDepth 10000 in
theorem left_cursor_rule1a_zero :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (leftCursorAt ⟨0, by decide⟩).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 6 := by
  rfl

set_option maxRecDepth 10000 in
theorem left_cursor_rule1a_one :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (leftCursorAt ⟨1, by decide⟩).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 35 := by
  rfl

set_option maxRecDepth 10000 in
theorem left_cursor_rule1a_two :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (leftCursorAt ⟨2, by decide⟩).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 53 := by
  rfl

set_option maxRecDepth 10000 in
theorem left_cursor_rule1a_three :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (leftCursorAt ⟨3, by decide⟩).occurrence.1.node =
        DeclarativeCIP.ExactAtomicNumber.ofNat 1 := by
  rfl

theorem rule3_compare_gt_of_canonical_atomic_heads
    {leftCursor rightCursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {leftKey rightKey : source.AromaticCanonicalUncancelledRule3SpatialKey}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    (leftCanonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      excluded ruleFuel leftCursor leftKey)
    (rightCanonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      excluded ruleFuel rightCursor rightKey)
    (leftZ rightZ : Nat)
    (leftObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        leftCursor.occurrence.1.node = DeclarativeCIP.ExactAtomicNumber.ofNat leftZ)
    (rightObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        rightCursor.occurrence.1.node = DeclarativeCIP.ExactAtomicNumber.ofNat rightZ)
    (higher : rightZ < leftZ) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys leftKey rightKey = .gt := by
  have leftHead := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph leftKey.constitutional.sourceNodes
    leftCursor.occurrence.1.node
    (canonical_rule3_key_constitutional_head leftCanonical)
  have rightHead := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph rightKey.constitutional.sourceNodes
    rightCursor.occurrence.1.node
    (canonical_rule3_key_constitutional_head rightCanonical)
  rw [leftObservation] at leftHead
  rw [rightObservation] at rightHead
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_gt_of_heads_gt
    leftHead rightHead higher
  apply source.compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_gt
  simp [ExactOfficialRuleMajorKey.compare,
    ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex, rule1a]

theorem rule3_compare_lt_of_canonical_atomic_heads
    {leftCursor rightCursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {leftKey rightKey : source.AromaticCanonicalUncancelledRule3SpatialKey}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    (leftCanonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      excluded ruleFuel leftCursor leftKey)
    (rightCanonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
      excluded ruleFuel rightCursor rightKey)
    (leftZ rightZ : Nat)
    (leftObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        leftCursor.occurrence.1.node = DeclarativeCIP.ExactAtomicNumber.ofNat leftZ)
    (rightObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        rightCursor.occurrence.1.node = DeclarativeCIP.ExactAtomicNumber.ofNat rightZ)
    (lower : leftZ < rightZ) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys leftKey rightKey = .lt := by
  have leftHead := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph leftKey.constitutional.sourceNodes
    leftCursor.occurrence.1.node
    (canonical_rule3_key_constitutional_head leftCanonical)
  have rightHead := ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head
    source.molecule.toLocalizedMoleculeGraph rightKey.constitutional.sourceNodes
    rightCursor.occurrence.1.node
    (canonical_rule3_key_constitutional_head rightCanonical)
  rw [leftObservation] at leftHead
  rw [rightObservation] at rightHead
  have rule1a := ExactOfficialRuleMajorKey.compareSparseExactRule1a_lt_of_heads_lt
    leftHead rightHead lower
  simp [AuthoritativeChemicalInput.compareAromaticCanonicalUncancelledRule3SpatialKeys,
    ExactOfficialRuleMajorKey.compare,
    ExactOfficialRuleMajorKey.compareAddressedSources, Ordering.byKey, compareLex, rule1a]


theorem left_rule3_compare_gt
    (left right : Fin 4) (leftZ rightZ : Nat)
    (leftObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (leftCursorAt left).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat leftZ)
    (rightObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (leftCursorAt right).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat rightZ)
    (higher : rightZ < leftZ) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (leftRule3KeyAt left) (leftRule3KeyAt right) = .gt :=
  rule3_compare_gt_of_canonical_atomic_heads
    (leftRule3KeyAt_canonical left) (leftRule3KeyAt_canonical right)
    leftZ rightZ leftObservation rightObservation higher

theorem left_rule3_compare_lt
    (left right : Fin 4) (leftZ rightZ : Nat)
    (leftObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (leftCursorAt left).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat leftZ)
    (rightObservation :
      source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        (leftCursorAt right).occurrence.1.node =
          DeclarativeCIP.ExactAtomicNumber.ofNat rightZ)
    (lower : leftZ < rightZ) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (leftRule3KeyAt left) (leftRule3KeyAt right) = .lt :=
  rule3_compare_lt_of_canonical_atomic_heads
    (leftRule3KeyAt_canonical left) (leftRule3KeyAt_canonical right)
    leftZ rightZ leftObservation rightObservation lower

theorem left_rule3_compare_two_one :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨2, by decide⟩) (leftRule3KeyAt ⟨1, by decide⟩) = .gt :=
  left_rule3_compare_gt ⟨2, by decide⟩ ⟨1, by decide⟩ 53 35
    left_cursor_rule1a_two left_cursor_rule1a_one (by decide)

theorem left_rule3_compare_two_zero :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨2, by decide⟩) (leftRule3KeyAt ⟨0, by decide⟩) = .gt :=
  left_rule3_compare_gt ⟨2, by decide⟩ ⟨0, by decide⟩ 53 6
    left_cursor_rule1a_two left_cursor_rule1a_zero (by decide)

theorem left_rule3_compare_two_three :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨2, by decide⟩) (leftRule3KeyAt ⟨3, by decide⟩) = .gt :=
  left_rule3_compare_gt ⟨2, by decide⟩ ⟨3, by decide⟩ 53 1
    left_cursor_rule1a_two left_cursor_rule1a_three (by decide)

theorem left_rule3_compare_one_zero :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨1, by decide⟩) (leftRule3KeyAt ⟨0, by decide⟩) = .gt :=
  left_rule3_compare_gt ⟨1, by decide⟩ ⟨0, by decide⟩ 35 6
    left_cursor_rule1a_one left_cursor_rule1a_zero (by decide)

theorem left_rule3_compare_one_three :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨1, by decide⟩) (leftRule3KeyAt ⟨3, by decide⟩) = .gt :=
  left_rule3_compare_gt ⟨1, by decide⟩ ⟨3, by decide⟩ 35 1
    left_cursor_rule1a_one left_cursor_rule1a_three (by decide)

theorem left_rule3_compare_zero_three :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨0, by decide⟩) (leftRule3KeyAt ⟨3, by decide⟩) = .gt :=
  left_rule3_compare_gt ⟨0, by decide⟩ ⟨3, by decide⟩ 6 1
    left_cursor_rule1a_zero left_cursor_rule1a_three (by decide)

theorem left_rule3_compare_zero_one :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨0, by decide⟩) (leftRule3KeyAt ⟨1, by decide⟩) = .lt :=
  left_rule3_compare_lt ⟨0, by decide⟩ ⟨1, by decide⟩ 6 35
    left_cursor_rule1a_zero left_cursor_rule1a_one (by decide)

theorem left_rule3_compare_zero_two :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨0, by decide⟩) (leftRule3KeyAt ⟨2, by decide⟩) = .lt :=
  left_rule3_compare_lt ⟨0, by decide⟩ ⟨2, by decide⟩ 6 53
    left_cursor_rule1a_zero left_cursor_rule1a_two (by decide)

theorem left_rule3_compare_one_two :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt ⟨1, by decide⟩) (leftRule3KeyAt ⟨2, by decide⟩) = .lt :=
  left_rule3_compare_lt ⟨1, by decide⟩ ⟨2, by decide⟩ 35 53
    left_cursor_rule1a_one left_cursor_rule1a_two (by decide)

theorem left_rule45_keys_exists :
    ∃ keys, leftRoots.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45Key?
        leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence)
          ruleFuel) = some keys :=
  exists_mapM_left_rule45 leftRoots left_roots_valid

noncomputable def leftRule45Keys : List source.AromaticCanonicalRerootCompoundRule45Key :=
  Classical.choose left_rule45_keys_exists

theorem left_rule45_keys_computed :
    leftRoots.mapM
      (source.buildAromaticCanonicalRerootCompoundRule45Key?
        leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence)
          ruleFuel) = some leftRule45Keys :=
  Classical.choose_spec left_rule45_keys_exists

theorem left_rule45_keys_length : leftRule45Keys.length = 4 := by
  rw [mapM_length_eq_of_eq_some
    (source.buildAromaticCanonicalRerootCompoundRule45Key?
      leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence) ruleFuel)
    leftRoots leftRule45Keys left_rule45_keys_computed, left_roots_length]

noncomputable def leftKeysExplicit :
    source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel :=
  { rule3Frame := leftRule3Frame
    rule3Length := left_rule3_frame_length
    rule45Keys := leftRule45Keys
    rule45Length := left_rule45_keys_length }

theorem left_keys_explicit_computed :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence)
        ruleFuel leftRoots = some leftKeysExplicit := by
  unfold AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
  rw [left_rule3_frame_computed]
  simp [left_rule3_frame_length, left_rule45_keys_computed,
    left_rule45_keys_length, leftKeysExplicit]

@[simp] theorem leftKeysExplicit_rule3_keyAt (position : Fin 4) :
    (leftKeysExplicit.keyAt position).rule3 = leftRule3KeyAt position := by
  rfl

theorem left_compareAt_of_rule3_gt (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt left) (leftRule3KeyAt right) = .gt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
      leftKeysExplicit left right =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simp [AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At,
    strict]

theorem left_compareAt_of_rule3_lt (left right : Fin 4)
    (strict : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (leftRule3KeyAt left) (leftRule3KeyAt right) = .lt) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
      leftKeysExplicit left right =
        ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simp [AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At,
    strict]

theorem left_compare_zero_one :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨0, by decide⟩ ⟨1, by decide⟩ =
        ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_lt _ _ left_rule3_compare_zero_one

theorem left_compare_zero_two :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨0, by decide⟩ ⟨2, by decide⟩ =
        ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_lt _ _ left_rule3_compare_zero_two

theorem left_compare_one_two :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨1, by decide⟩ ⟨2, by decide⟩ =
        ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_lt _ _ left_rule3_compare_one_two

theorem left_compare_zero_three :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨0, by decide⟩ ⟨3, by decide⟩ =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_gt _ _ left_rule3_compare_zero_three

theorem left_compare_two_one :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨2, by decide⟩ ⟨1, by decide⟩ =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_gt _ _ left_rule3_compare_two_one

theorem left_compare_two_zero :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨2, by decide⟩ ⟨0, by decide⟩ =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_gt _ _ left_rule3_compare_two_zero

theorem left_compare_two_three :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨2, by decide⟩ ⟨3, by decide⟩ =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_gt _ _ left_rule3_compare_two_three

theorem left_compare_one_zero :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨1, by decide⟩ ⟨0, by decide⟩ =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_gt _ _ left_rule3_compare_one_zero

theorem left_compare_one_three :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      ⟨1, by decide⟩ ⟨3, by decide⟩ =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) :=
  left_compareAt_of_rule3_gt _ _ left_rule3_compare_one_three

def positionZero : Fin 4 := ⟨0, by decide⟩
def positionOne : Fin 4 := ⟨1, by decide⟩
def positionTwo : Fin 4 := ⟨2, by decide⟩
def positionThree : Fin 4 := ⟨3, by decide⟩

theorem finRange_four : List.finRange 4 =
    [positionZero, positionOne, positionTwo, positionThree] := by
  decide

theorem left_compare_position_zero_one :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionZero positionOne =
        ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionZero, positionOne] using left_compare_zero_one

theorem left_compare_position_zero_two :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionZero positionTwo =
        ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionZero, positionTwo] using left_compare_zero_two

theorem left_compare_position_one_two :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionOne positionTwo =
        ({ ordering := .lt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionOne, positionTwo] using left_compare_one_two

theorem left_compare_position_zero_three :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionZero positionThree =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionZero, positionThree] using left_compare_zero_three

theorem left_compare_position_two_one :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionTwo positionOne =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionTwo, positionOne] using left_compare_two_one

theorem left_compare_position_two_zero :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionTwo positionZero =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionTwo, positionZero] using left_compare_two_zero

theorem left_compare_position_two_three :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionTwo positionThree =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionTwo, positionThree] using left_compare_two_three

theorem left_compare_position_one_zero :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionOne positionZero =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionOne, positionZero] using left_compare_one_zero

theorem left_compare_position_one_three :
    source.compareAromaticCanonicalOccurrenceRule3Through5At leftKeysExplicit
      positionOne positionThree =
        ({ ordering := .gt, pseudo := false } : ConstitutionalRule5Comparison) := by
  simpa [positionOne, positionThree] using left_compare_one_three

noncomputable def leftTracked : TrackedLocalizedLigandOrder :=
  { highestFirst := [positionTwo, positionOne, positionZero, positionThree]
    pseudoComparisons := 0 }

theorem left_tracked_raw_computed :
    source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? leftKeysExplicit =
      some leftTracked := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5TrackedOrder?
  rw [sortFourLocalizedLigandsTracked, sortLocalizedLigandsTracked, finRange_four]
  norm_num [
    AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At?,
    AuthoritativeChemicalInput.aromaticCanonicalRule3Through5DescriptorComparison,
    sortLocalizedLigandsTrackedFrom, insertLocalizedLigandTracked,
    left_compare_position_zero_one, left_compare_position_zero_two,
    left_compare_position_one_two, left_compare_position_zero_three, leftTracked]

theorem left_tracked_coherent :
    source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent
      leftKeysExplicit leftTracked.highestFirst = true := by
  norm_num [AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5OrderCoherent,
    AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5OrderPairStrict,
    leftTracked, left_compare_position_two_one, left_compare_position_two_zero,
    left_compare_position_two_three, left_compare_position_one_zero,
    left_compare_position_one_three, left_compare_position_zero_three]

theorem left_tracked_computed :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? leftKeysExplicit =
      some leftTracked := by
  simp [AuthoritativeChemicalInput.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
    left_tracked_raw_computed, left_tracked_coherent]

@[simp] theorem leftBase_cursorAt_eq_leftCursorAt (position : Fin 4) :
    leftBase.cursorAt position = leftCursorAt position := by
  rfl

set_option maxRecDepth 10000 in
theorem left_point_two :
    source.aromaticCanonicalRerootSpatialPoint? (leftBase.cursorAt positionTwo) =
      some (symmetricPoint 5) := by
  rfl

set_option maxRecDepth 10000 in
theorem left_point_one :
    source.aromaticCanonicalRerootSpatialPoint? (leftBase.cursorAt positionOne) =
      some (symmetricPoint 4) := by
  rfl

set_option maxRecDepth 10000 in
theorem left_point_zero :
    source.aromaticCanonicalRerootSpatialPoint? (leftBase.cursorAt positionZero) =
      some (symmetricPoint 1) := by
  rfl

set_option maxRecDepth 10000 in
theorem left_point_three :
    source.aromaticCanonicalRerootSpatialPoint? (leftBase.cursorAt positionThree) =
      some (symmetricPoint 9) := by
  rfl

theorem left_cursor_point_two :
    source.aromaticCanonicalRerootSpatialPoint? (leftCursorAt positionTwo) =
      some (symmetricPoint 5) := by
  simpa using left_point_two

theorem left_cursor_point_one :
    source.aromaticCanonicalRerootSpatialPoint? (leftCursorAt positionOne) =
      some (symmetricPoint 4) := by
  simpa using left_point_one

theorem left_cursor_point_zero :
    source.aromaticCanonicalRerootSpatialPoint? (leftCursorAt positionZero) =
      some (symmetricPoint 1) := by
  simpa using left_point_zero

theorem left_cursor_point_three :
    source.aromaticCanonicalRerootSpatialPoint? (leftCursorAt positionThree) =
      some (symmetricPoint 9) := by
  simpa using left_point_three

theorem left_points_computed :
    leftTracked.highestFirst.mapM (fun index =>
      source.aromaticCanonicalRerootSpatialPoint? (leftBase.cursorAt index)) =
        some leftPriorityPoints := by
  simp [leftTracked, leftPriorityPoints,
    left_cursor_point_two, left_cursor_point_one, left_cursor_point_zero,
    left_cursor_point_three]

noncomputable def leftEvidence :
    source.AromaticCanonicalOccurrenceRule3Through5SpatialEvidence carrierFuel :=
  { center := leftCenter
    base := leftBase
    keys := leftKeysExplicit
    tracked := leftTracked
    points := leftPriorityPoints }

theorem left_evidence_computed :
    source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
      leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence) ruleFuel =
        some leftEvidence := by
  unfold AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
  rw [left_center_computed, left_base_computed]
  change ((source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      leftOccurrence (source.aromaticCanonicalDependencyView state leftOccurrence)
        ruleFuel leftRoots).bind fun keys =>
      (source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys).bind fun tracked =>
        (tracked.highestFirst.mapM fun index =>
          source.aromaticCanonicalRerootSpatialPoint? (leftBase.cursorAt index)).bind fun points =>
            some { center := leftCenter, base := leftBase, keys, tracked, points }) =
      some leftEvidence
  rw [left_keys_explicit_computed]
  simp only [Option.bind_some]
  rw [left_tracked_computed]
  simp only [Option.bind_some]
  rw [left_points_computed]
  rfl

/-- The left branch volume is `+3`; under the corrected contract positive volume is `S`. -/
theorem left_evidence_geometry :
    RationalTetrahedralDescriptor leftEvidence.points .S := by
  exact (descriptorOfPriorityOrderedPoints?_eq_some_iff leftPriorityPoints .S).mp
    leftPriorityPoints_descriptor

theorem left_state_chiral_S : state leftOccurrence = some (.chiral .S) := by
  have assigned := source.aromaticCanonicalOccurrenceRule3Through5Model_eq_some_of_spatialEvidence
    state (source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics)
    leftOccurrence leftEvidence .S left_evidence_computed left_evidence_geometry
  simpa [leftEvidence, leftTracked] using assigned

/-- Historical API key retained for the pinned kernel certificate.  The corrected tetrahedral
contract makes the left branch `S`, so this declaration's statement is the corrected one; the
accurately named sibling is `left_state_chiral_S`. -/
theorem left_state_chiral_R : state leftOccurrence = some (.chiral .S) :=
  left_state_chiral_S

end Rule45CanonicalFamilyNonvacuity
end IUPACNormativeProvision
end TetraStereo.OneCenter
