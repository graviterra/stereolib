import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins
import TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-! Near-root label rows of actual cumulative builds, without evaluating their deeper keys.
The sole-child oxygen frame forces the first two addressed rows independently of sibling
sorts beneath the center. No molecular acyclicity or descriptor output premise is used. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix

open CertifiedLocalizedCIPInput
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame (target frame)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice (reader)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader (factFirstView)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts (twoFacts)

/-- Every successful cumulative key starts with its own actual observation. -/
theorem cumulative_labels_cons (sourceInput : CertifiedLocalizedCIPInput)
    (cache : sourceInput.LocalizedRerootChildReader (retainedCarrierFuel sourceInput))
    (stage : LocalizedCumulativeRule45Stage)
    (read : sourceInput.LocalizedRerootCursor (retainedCarrierFuel sourceInput) → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : sourceInput.LocalizedRerootCursor (retainedCarrierFuel sourceInput))
    (key : sourceInput.LocalizedRerootCumulativeRule45Key)
    (computed : LocalizedChemicalRingCachedOperations.cumulative sourceInput cache stage read fuel cursor =
      some key) :
    ∃ tail, key.labels = [([], read cursor)] :: tail := by
  cases fuel with
  | zero =>
    unfold LocalizedChemicalRingCachedOperations.cumulative at computed
    cases hc : cache.readChildren cursor with
    | none => simp [hc] at computed
    | some children =>
      by_cases terminal : children = []
      · simp [hc, terminal] at computed
        subst key
        exact ⟨[], rfl⟩
      · simp [hc, terminal] at computed
  | succ fuel =>
    unfold LocalizedChemicalRingCachedOperations.cumulative at computed
    cases hc : cache.readChildren cursor with
    | none => simp [hc] at computed
    | some children =>
      by_cases terminal : children = []
      · simp [hc, terminal] at computed
        subst key
        exact ⟨[], rfl⟩
      · cases hm : children.mapM
          (LocalizedChemicalRingCachedOperations.cumulative sourceInput cache stage read fuel) with
        | none => simp [hc, terminal, hm] at computed
        | some keys =>
          simp [hc, terminal, hm] at computed
          subst key
          exact ⟨_, rfl⟩

/-- A sole immediate child fixes the second observation row without building its descendants. -/
theorem cumulative_single_child_prefix (sourceInput : CertifiedLocalizedCIPInput)
    (cache : sourceInput.LocalizedRerootChildReader (retainedCarrierFuel sourceInput))
    (stage : LocalizedCumulativeRule45Stage)
    (read : sourceInput.LocalizedRerootCursor (retainedCarrierFuel sourceInput) → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor child : sourceInput.LocalizedRerootCursor (retainedCarrierFuel sourceInput))
    (oneChild : cache.readChildren cursor = some [child])
    (key : sourceInput.LocalizedRerootCumulativeRule45Key)
    (computed : LocalizedChemicalRingCachedOperations.cumulative sourceInput cache stage read
      (fuel + 1) cursor = some key) :
    ∃ tail, key.labels = [([], read cursor)] :: [([0], read child)] :: tail := by
  rw [LocalizedChemicalRingCachedOperations.cumulative, oneChild] at computed
  cases hchild : LocalizedChemicalRingCachedOperations.cumulative sourceInput cache stage read
      fuel child with
  | none => simp [List.mapM_cons, List.mapM_nil, hchild] at computed
  | some childKey =>
    simp [List.mapM_cons, List.mapM_nil, hchild] at computed
    subst key
    obtain ⟨tail, first⟩ := cumulative_labels_cons sourceInput cache stage read fuel child childKey hchild
    simp only [sortRuleMajorCumulativeKeys, sortKeysBy, insertKeyBy]
    simp [mergeLocalizedRerootLabelChildren,
      localizedRerootLabelChildLayerCount, first, List.range_succ_eq_map,
      OfficialRuleMajorKey.prefixLayer]

abbrev read := LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.read
abbrev oxygenChild := LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins.oxygenChild
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefixPins
  (oxygen4_child oxygen15_child oxygen4_read oxygen15_read center3_read center14_read)

/-- Any actual common-reference cumulative build has the nearest R observation at distance1. -/
theorem oxygen4_prefix (stage : LocalizedCumulativeRule45Stage)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : LocalizedChemicalRingCachedOperations.cumulative input reader stage read 54
      (frame.cursorAt 2) = some key) :
    ∃ tail, key.labels = [([], none)] :: [([0], some (.chiral .R))] :: tail := by
  simpa only [oxygen4_read, center3_read] using cumulative_single_child_prefix input reader stage
    read 53 (frame.cursorAt 2) (oxygenChild 2) oxygen4_child key computed

theorem oxygen15_prefix (stage : LocalizedCumulativeRule45Stage)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : LocalizedChemicalRingCachedOperations.cumulative input reader stage read 54
      (frame.cursorAt 3) = some key) :
    ∃ tail, key.labels = [([], none)] :: [([0], some (.chiral .S))] :: tail := by
  simpa only [oxygen15_read, center14_read] using cumulative_single_child_prefix input reader stage
    read 53 (frame.cursorAt 3) (oxygenChild 3) oxygen15_child key computed


/-- The common-R comparison is decided at the nearest chiral row; deeper rows are irrelevant. -/
theorem commonR_two_rows
    (leftTail rightTail : List (List (OfficialSparseEntry (List Nat)))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      ([ [([], localizedCumulativeRule45Priority (.rule5 .R .R) none)],
         [([0], localizedCumulativeRule45Priority (.rule5 .R .R) (some (.chiral .R)))] ] ++ leftTail)
      ([ [([], localizedCumulativeRule45Priority (.rule5 .S .R) none)],
         [([0], localizedCumulativeRule45Priority (.rule5 .S .R) (some (.chiral .S)))] ] ++ rightTail) =
      .gt := by
  rfl

/-- Common-S reverses exactly the nearest signed decision, independently of deeper rows. -/
theorem commonS_two_rows
    (leftTail rightTail : List (List (OfficialSparseEntry (List Nat)))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      ([ [([], localizedCumulativeRule45Priority (.rule5 .R .S) none)],
         [([0], localizedCumulativeRule45Priority (.rule5 .R .S) (some (.chiral .R)))] ] ++ leftTail)
      ([ [([], localizedCumulativeRule45Priority (.rule5 .S .S) none)],
         [([0], localizedCumulativeRule45Priority (.rule5 .S .S) (some (.chiral .S)))] ] ++ rightTail) =
      .lt := by
  rfl

/-- Transfer actual label-prefix and descriptor-coherence facts to the signed common-R column. -/
theorem commonR_descriptor_gt
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftPrefix : ∃ tail, left.labels = [([], none)] :: [([0], some (.chiral .R))] :: tail)
    (rightPrefix : ∃ tail, right.labels = [([], none)] :: [([0], some (.chiral .S))] :: tail)
    (leftCoherent : left.descriptor = left.labels.map (List.map fun entry =>
      (entry.1, localizedCumulativeRule45Priority (.rule5 .R .R) entry.2)))
    (rightCoherent : right.descriptor = right.labels.map (List.map fun entry =>
      (entry.1, localizedCumulativeRule45Priority (.rule5 .S .R) entry.2))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      left.descriptor right.descriptor = .gt := by
  obtain ⟨leftTail, leftEq⟩ := leftPrefix
  obtain ⟨rightTail, rightEq⟩ := rightPrefix
  rw [leftCoherent, rightCoherent, leftEq, rightEq]
  exact commonR_two_rows _ _


end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix.cumulative_labels_cons
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix.cumulative_single_child_prefix
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix.oxygen4_prefix
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix.oxygen15_prefix

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix.commonR_two_rows
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix.commonS_two_rows
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix.commonR_descriptor_gt
