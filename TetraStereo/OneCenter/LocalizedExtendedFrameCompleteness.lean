import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key
import TetraStereo.OneCenter.LocalizedRule3CoupledTopologyExecutable
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder

set_option autoImplicit false

/-!
# Unconditional observable and parent-assembly facts for localized extended Rule 3

`LocalizedRerootExtendedShortCircuitRule3Key` proves that executable success carries the
independent key/frame meaning (soundness).  This module collects the converse pieces that hold
unconditionally, together with the congruence facts that make separately compiled sibling
assemblies comparable.

Proved unconditionally:

* every successful optional expansion of the underlying pieces is characterized in both directions
  (`List.mapM` completeness, exact children, structural node, exhaustive topology, and the coupled
  frame policy);
* the comparison-visible projection of a Rule-3 spatial key (Rules 1a, 1b, 2 and the Rule-3
  priority projection, but **not** the `observations` field) is exactly characterized, so two
  descending permutations of the same child keys induce the same observation sequence;
* parent-assembly congruence: two descending permutations of the same child keys carry exactly the
  same observable projection and exactly the same physical-unit identities after merging, because
  slot-prefixing re-addresses entries but preserves which physical units appear.

This module deliberately makes **no** whole-frame completeness claim.  Literal recursive
completeness (`DeclarativeLocalizedRerootExtendedShortCircuitRule3Key` /
`DeclarativeLocalizedExtendedShortCircuitRule3Frame` imply executable success with exactly that
key/frame) is neither stated nor assumed here.  Two issues remain for that converse:

1. the independent node relation allows `previous` (and, one level down, `original`) derivations
   on odd/ordinary-route occurrences where the deterministic executable takes the odd/ordinary
   spatial path; agreement of these overlapping derivations remains unproved here;
2. `compareLocalizedRerootRecursiveRule3SpatialKeys` ignores the `observations` field, so a
   descending permutation of child keys is not unique; the compiled sort is one specific choice,
   and equal compared projections do not force equal `observations` payloads.  The unconditional
   observable-congruence statements below are the correct replacement for literal key equality.

Neither point is hidden behind a deferred obligation, a trusted-code escape hatch, or a weakened
hypothesis.  The observations field is never assumed equal; only the comparator-visible projection
and physical-unit membership are transported.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## General `List.mapM` completeness -/

/-- `List.mapM` completeness against a pointwise relation: when every related value maps to its
related result, the whole optional map returns exactly the related result list. -/
theorem mapM_complete_of_forall₂ {α β : Type*} (f : α → Option β) (R : α → β → Prop)
    (complete : ∀ a b, R a b → f a = some b) :
    ∀ as bs, List.Forall₂ R as bs → as.mapM f = some bs
  | [], bs, forall₂ => by
      cases forall₂
      rfl
  | a :: as, b :: bs, forall₂ => by
      cases forall₂ with
      | cons head tail =>
          have rest := mapM_complete_of_forall₂ f R complete as bs tail
          simp [rest, complete a b head]

/-! ## Unconditional two-directional characterizations of the underlying pieces -/

/-- Total executable child expansion is the unique exact zipper expansion. -/
theorem executableLocalizedRerootChildren?_complete
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (derived : input.DeclarativeLocalizedRerootChildren cursor children) :
    input.executableLocalizedRerootChildren? cursor = some children := by
  have executableEq : input.executableLocalizedRerootChildren cursor = children := by
    have viaOptional := (input.localizedRerootChildren?_eq_some_iff cursor children).mpr derived
    rw [input.localizedRerootChildren?_eq_some_executable cursor] at viaOptional
    rw [Option.some.injEq] at viaOptional
    exact viaOptional
  rw [input.executableLocalizedRerootChildren?_eq_some cursor, executableEq]

/-- The executable structural node reader succeeds at exactly the non-edge occurrences. -/
theorem localizedRule3StructuralNodeExec_complete
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (notEdge : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence) :
    input.localizedRule3StructuralNodeExec occurrence = some none :=
  (input.localizedRule3StructuralNodeExec_eq_some_none_iff occurrence).mpr notEdge

/-- The executable exhaustive topology resolver succeeds exactly on the independent resolution
relation. -/
theorem localizedRule3CoupledTopologyResolutionExec?_complete_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (topology : input.LocalizedRule3CoupledTopologyResolution) :
    input.localizedRule3CoupledTopologyResolutionExec? keys = some topology ↔
      input.DeclarativeLocalizedRule3CoupledTopologyResolution keys topology := by
  rw [input.localizedRule3CoupledTopologyResolutionExec?_eq_original]
  exact input.localizedRule3CoupledTopologyResolution?_eq_some_iff keys topology

/-- The independent frame policy determines the executable coupled/excluded projection. -/
theorem DeclarativeLocalizedRule3CoupledFramePolicy_determines
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (topology : input.LocalizedRule3CoupledTopologyResolution)
    (coupled : Bool) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (policy : input.DeclarativeLocalizedRule3CoupledFramePolicy keys topology coupled excluded) :
    coupled = topology.isCoupled ∧
      excluded = input.localizedRule3CoupledExcludedPhysicalUnits keys topology := by
  cases policy with
  | ordinary => constructor <;> rfl
  | coupled matching => constructor <;> rfl

/-! ## The comparison-visible projection of a Rule-3 spatial key

`compareLocalizedRerootRecursiveRule3SpatialKeys` reads the constitutional component (Rules 1a,
1b, 2) and the `rule3` priority projection, but never the `observations` field.  The observable
projection below is therefore exactly what the comparator can see; two descending permutations of
the same child keys induce the same observation sequence, which is the true unconditional
replacement for literal key equality. -/

/-- The comparison-visible projection of one recursively ranked Rule-3 spatial key: the three
constitutional rule projections and the numeric Rule-3 priority projection.  `observations` is
deliberately absent, because the comparator ignores it. -/
structure LocalizedRerootRule3SpatialKeyObservable where
  /-- Addressed Rule-1a atomic-number projection. -/
  rule1a : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-1b duplicate-atom projection. -/
  rule1b : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-2 isotope-mass projection. -/
  rule2 : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-3 priority projection. -/
  rule3 : List (List (OfficialSparseEntry ℕ))
  deriving DecidableEq

/-- Observable comparison, in the nesting used by
`compareLocalizedRerootRecursiveRule3SpatialKeys`: Rule 1a, then Rule 1b, then Rule 2, then the
Rule-3 priority projection. -/
def compareLocalizedRerootRule3SpatialKeyObservable :
    LocalizedRerootRule3SpatialKeyObservable →
      LocalizedRerootRule3SpatialKeyObservable → Ordering :=
  compareLex
    (compareLex
      (Ordering.byKey LocalizedRerootRule3SpatialKeyObservable.rule1a
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
      (compareLex
        (Ordering.byKey LocalizedRerootRule3SpatialKeyObservable.rule1b
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
        (Ordering.byKey LocalizedRerootRule3SpatialKeyObservable.rule2
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))))
    (Ordering.byKey LocalizedRerootRule3SpatialKeyObservable.rule3
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))

/-- Forget a recursively ranked Rule-3 spatial key down to its comparison-visible projection. -/
def localizedRerootRule3SpatialKeyObservable
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    LocalizedRerootRule3SpatialKeyObservable where
  rule1a := key.constitutional.rule1a
  rule1b := key.constitutional.rule1b
  rule2 := key.constitutional.rule2
  rule3 := key.rule3

/-- The observable comparator decides equality exactly on equal observables. -/
theorem compareLocalizedRerootRule3SpatialKeyObservable_eq_iff
    (left right : LocalizedRerootRule3SpatialKeyObservable) :
    compareLocalizedRerootRule3SpatialKeyObservable left right = Ordering.eq ↔ left = right := by
  have rule1aCompare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.eq ↔ left.rule1a = right.rule1a :=
    compareSparseLayers_compareNat_eq_iff left.rule1a right.rule1a
  have rule1bCompare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      left.rule1b right.rule1b = Ordering.eq ↔ left.rule1b = right.rule1b :=
    compareSparseLayers_compareRule1b_eq_iff left.rule1b right.rule1b
  have rule2Compare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule2 right.rule2 = Ordering.eq ↔ left.rule2 = right.rule2 :=
    compareSparseLayers_compareNat_eq_iff left.rule2 right.rule2
  have rule3Compare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule3 right.rule3 = Ordering.eq ↔ left.rule3 = right.rule3 :=
    compareSparseLayers_compareNat_eq_iff left.rule3 right.rule3
  rw [compareLocalizedRerootRule3SpatialKeyObservable, compareLex_eq_eq, compareLex_eq_eq,
    compareLex_eq_eq]
  simp only [Ordering.byKey, rule1aCompare, rule1bCompare, rule2Compare, rule3Compare]
  constructor
  · rintro ⟨⟨h1a, h1b, h2⟩, h3⟩
    cases left with
    | mk leftRule1a leftRule1b leftRule2 leftRule3 =>
      cases right with
      | mk rightRule1a rightRule1b rightRule2 rightRule3 =>
        simp_all
  · intro equal
    rw [equal]
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- The observable comparator is oriented and transitive. -/
theorem compareLocalizedRerootRule3SpatialKeyObservable_transCmp :
    Std.TransCmp compareLocalizedRerootRule3SpatialKeyObservable := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  haveI : Std.TransCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  unfold compareLocalizedRerootRule3SpatialKeyObservable
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- The recursively ranked Rule-3 key comparator is the observable comparator applied to the
observable projection. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys left right =
      compareLocalizedRerootRule3SpatialKeyObservable
        (input.localizedRerootRule3SpatialKeyObservable left)
        (input.localizedRerootRule3SpatialKeyObservable right) :=
  rfl

/-- Descending Rule-3 key order transports to the observable projections. -/
theorem rule3SpatialKey_observable_pairwise_of_descending
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending keys) :
    (keys.map (input.localizedRerootRule3SpatialKeyObservable)).Pairwise
      (fun left right =>
        compareLocalizedRerootRule3SpatialKeyObservable left right ≠ Ordering.lt) := by
  unfold LocalizedRerootRecursiveRule3SpatialKeysDescending at descending
  exact List.Pairwise.map (input.localizedRerootRule3SpatialKeyObservable)
    (fun a b hlt hObservedLt => hlt (by
      rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable a b]
      exact hObservedLt))
    descending

/-- Independent descending permutations of the same Rule-3 child keys induce the same sequence of
comparison-visible observations.  The two lists may have been compiled separately, and their
`observations` components may still differ; this is the true unconditional statement replacing
literal key equality. -/
theorem map_localizedRerootRule3SpatialKeyObservable_eq_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : left.Perm right)
    (leftDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending left)
    (rightDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending right) :
    left.map (input.localizedRerootRule3SpatialKeyObservable) =
      right.map (input.localizedRerootRule3SpatialKeyObservable) := by
  haveI : Std.TransCmp compareLocalizedRerootRule3SpatialKeyObservable :=
    compareLocalizedRerootRule3SpatialKeyObservable_transCmp
  exact List.Perm.eq_of_pairwise
    (le := fun left right =>
      compareLocalizedRerootRule3SpatialKeyObservable left right ≠ Ordering.lt)
    (fun a b _ _ lower upper =>
      (compareLocalizedRerootRule3SpatialKeyObservable_eq_iff a b).mp (by
        refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp lower)
        rw [← Std.OrientedCmp.isGE_eq_isLE]
        exact Ordering.ne_lt_iff_isGE.mp upper))
    (input.rule3SpatialKey_observable_pairwise_of_descending left leftDescending)
    (input.rule3SpatialKey_observable_pairwise_of_descending right rightDescending)
    (permutation.map (input.localizedRerootRule3SpatialKeyObservable))

/-- Re-running the structural descending sort on already descending keys preserves the observation
sequence, so independently compiled sibling lists agree with the compiled sort. -/
theorem map_localizedRerootRule3SpatialKeyObservable_sort_eq_of_descending
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending keys) :
    (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys).map
        (input.localizedRerootRule3SpatialKeyObservable) =
      keys.map (input.localizedRerootRule3SpatialKeyObservable) :=
  input.map_localizedRerootRule3SpatialKeyObservable_eq_of_perm_of_descending
    (input.sortLocalizedRerootRecursiveRule3SpatialKeys keys)
    keys
    (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm keys)
    (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending keys)
    descending

/-! ## Parent assembly: physical-unit identities survive sibling re-addressing -/

private theorem mem_flatten_iff_getD
    {α : Type*} (entry : α) (layers : List (List α)) :
    entry ∈ layers.flatten ↔
      ∃ depth, depth < layers.length ∧ entry ∈ layers.getD depth [] := by
  rw [List.mem_flatten]
  constructor
  · rintro ⟨layer, layerPresent, entryPresent⟩
    obtain ⟨depth, depthLt, layerEq⟩ := List.mem_iff_getElem.mp layerPresent
    refine ⟨depth, depthLt, ?_⟩
    rw [← layerEq] at entryPresent
    simpa [List.getD, depthLt] using entryPresent
  · rintro ⟨depth, depthLt, entryPresent⟩
    refine ⟨layers[depth], List.getElem_mem .., ?_⟩
    simpa [List.getD, depthLt] using entryPresent

private theorem foldl_max_ge_initial {α : Type*} (measure : α → Nat) :
    ∀ (values : List α) (initial : Nat),
      initial ≤ values.foldl
        (fun longest value => max longest (measure value)) initial
  | [], _ => le_rfl
  | value :: values, initial =>
      le_trans (Nat.le_max_left initial (measure value))
        (foldl_max_ge_initial measure values (max initial (measure value)))

private theorem value_le_foldl_max_of_mem {α : Type*} (measure : α → Nat) :
    ∀ (values : List α) (initial : Nat) (value : α), value ∈ values →
      measure value ≤ values.foldl
        (fun longest item => max longest (measure item)) initial
  | [], _, _, present => by simp at present
  | head :: tail, initial, value, present => by
      rcases List.mem_cons.mp present with headEq | tailPresent
      · rw [headEq]
        exact le_trans (Nat.le_max_right initial (measure head))
          (foldl_max_ge_initial measure tail (max initial (measure head)))
      · exact value_le_foldl_max_of_mem measure tail
          (max initial (measure head)) value tailPresent

private theorem child_observationLength_le_count
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (child : input.LocalizedRerootRecursiveRule3SpatialKey)
    (present : child ∈ children) :
    child.observations.length ≤
      input.localizedRerootRule3ObservationChildLayerCount children := by
  unfold localizedRerootRule3ObservationChildLayerCount
  exact value_le_foldl_max_of_mem (fun key => key.observations.length)
    children 0 child present

/-- Prefixing a sibling slot preserves the physical-unit identity carried by every entry. -/
theorem prefixLayer_physicalUnitId_mem
    (input : CertifiedLocalizedCIPInput)
    (slot : Nat) (layer : List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult))
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry ∈ OfficialRuleMajorKey.prefixLayer slot layer,
        entry.2.physicalUnitId = unit) ↔
      (∃ entry ∈ layer, entry.2.physicalUnitId = unit) := by
  constructor
  · rintro ⟨entry, entryPresent, physical⟩
    unfold OfficialRuleMajorKey.prefixLayer at entryPresent
    rw [List.mem_map] at entryPresent
    rcases entryPresent with ⟨source, sourcePresent, rfl⟩
    exact ⟨source, sourcePresent, physical⟩
  · rintro ⟨source, sourcePresent, physical⟩
    refine ⟨(slot :: source.1, source.2), ?_, physical⟩
    unfold OfficialRuleMajorKey.prefixLayer
    rw [List.mem_map]
    exact ⟨source, sourcePresent, rfl⟩

/-- A physical-unit identity is carried by the merged child observations exactly when some child
key carries it.  Slot-prefixing may re-address entries but does not change which units appear;
sibling addresses are irrelevant to physical-unit membership. -/
theorem mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry ∈ (input.mergeLocalizedRerootRule3ObservationChildren children).flatten,
        entry.2.physicalUnitId = unit) ↔
      ∃ child ∈ children, unit ∈ input.localizedRule3PhysicalUnitIds child := by
  constructor
  · rintro ⟨entry, entryInFlatten, physical⟩
    rw [mem_flatten_iff_getD] at entryInFlatten
    rcases entryInFlatten with ⟨depth, depthLt, entryPresent⟩
    have depthLtCount : depth < input.localizedRerootRule3ObservationChildLayerCount children := by
      simpa [mergeLocalizedRerootRule3ObservationChildren] using depthLt
    have inMerged : entry ∈ children.zipIdx.flatMap fun indexed =>
        OfficialRuleMajorKey.prefixLayer indexed.2
          (indexed.1.observations.getD depth []) := by
      simpa [mergeLocalizedRerootRule3ObservationChildren, List.getD, depthLtCount] using entryPresent
    simp only [List.mem_flatMap] at inMerged
    rcases inMerged with ⟨indexed, indexedPresent, inPrefix⟩
    simp only [OfficialRuleMajorKey.prefixLayer, List.mem_map] at inPrefix
    rcases inPrefix with ⟨source, sourcePresent, sourceEq⟩
    have sourcePhysical : source.2.physicalUnitId = unit := by
      subst entry
      simpa using physical
    have depthLtChild : depth < indexed.1.observations.length := by
      by_contra notLt
      simp [List.getD, notLt] at sourcePresent
    have sourceFlatten : source ∈ indexed.1.observations.flatten :=
      (mem_flatten_iff_getD source indexed.1.observations).2
        ⟨depth, depthLtChild, sourcePresent⟩
    rcases List.mem_flatten.mp sourceFlatten with ⟨layer, layerPresent, sourceInLayer⟩
    have unitInChild : unit ∈ input.localizedRule3PhysicalUnitIds indexed.1 :=
      (input.mem_localizedRule3PhysicalUnitIds_iff indexed.1 unit).mpr
        ⟨layer, layerPresent, source, sourceInLayer, sourcePhysical⟩
    exact ⟨indexed.1, List.fst_mem_of_mem_zipIdx indexedPresent, unitInChild⟩
  · rintro ⟨child, childPresent, unitInChild⟩
    rcases (input.mem_localizedRule3PhysicalUnitIds_iff child unit).mp unitInChild with
      ⟨layer, layerPresent, entry, entryPresent, physical⟩
    obtain ⟨depth, depthLtChild, layerEq⟩ := List.mem_iff_getElem.mp layerPresent
    have depthLtCount : depth < input.localizedRerootRule3ObservationChildLayerCount children :=
      lt_of_lt_of_le depthLtChild
        (input.child_observationLength_le_count children child childPresent)
    have entryInLayer : entry ∈ child.observations[depth] := by
      simpa [layerEq] using entryPresent
    have entryInGetD : entry ∈ child.observations.getD depth [] := by
      simpa [List.getD, depthLtChild] using entryInLayer
    rcases List.mem_iff_getElem?.mp childPresent with ⟨idx, childIdxOpt⟩
    have indexedPresent : (child, idx) ∈ children.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr childIdxOpt
    refine ⟨(idx :: entry.1, entry.2), ?_, ?_⟩
    · rw [mem_flatten_iff_getD]
      refine ⟨depth, ?_, ?_⟩
      · simpa [mergeLocalizedRerootRule3ObservationChildren] using depthLtCount
      · have inMerged : (idx :: entry.1, entry.2) ∈
            children.zipIdx.flatMap fun indexed =>
              OfficialRuleMajorKey.prefixLayer indexed.2
                (indexed.1.observations.getD depth []) := by
          simp only [List.mem_flatMap]
          refine ⟨(child, idx), indexedPresent, ?_⟩
          simp only [OfficialRuleMajorKey.prefixLayer, List.mem_map]
          exact ⟨entry, entryInGetD, rfl⟩
        simpa [mergeLocalizedRerootRule3ObservationChildren, List.getD, depthLtCount] using inMerged
    · simpa using physical

/-- Permuting child keys does not change which physical-unit identities they carry. -/
theorem localizedRule3PhysicalUnitIds_mem_eq_of_perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : left.Perm right) (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ left.flatMap input.localizedRule3PhysicalUnitIds ↔
      unit ∈ right.flatMap input.localizedRule3PhysicalUnitIds := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨child, childInLeft, unitInChild⟩
    exact ⟨child, permutation.mem_iff.mp childInLeft, unitInChild⟩
  · rintro ⟨child, childInRight, unitInChild⟩
    exact ⟨child, permutation.mem_iff.mpr childInRight, unitInChild⟩

/-- Permuting child keys re-addresses the merged observations but preserves exactly which physical
units appear. -/
theorem mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_eq_of_perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : left.Perm right) (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry ∈ (input.mergeLocalizedRerootRule3ObservationChildren left).flatten,
        entry.2.physicalUnitId = unit) ↔
      (∃ entry ∈ (input.mergeLocalizedRerootRule3ObservationChildren right).flatten,
        entry.2.physicalUnitId = unit) := by
  rw [input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff left unit,
    input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff right unit]
  simpa only [List.mem_flatMap] using
    input.localizedRule3PhysicalUnitIds_mem_eq_of_perm left right permutation unit

/-- Parent-assembly congruence: two descending permutations of the same child keys induce the same
comparison-visible (numeric) observable projection and carry exactly the same physical-unit
identities, both as a flat child-key union and in the merged addressed observations. -/
theorem parentAssembly_congruence_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : left.Perm right)
    (leftDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending left)
    (rightDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending right) :
    left.map (input.localizedRerootRule3SpatialKeyObservable) =
        right.map (input.localizedRerootRule3SpatialKeyObservable) ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        unit ∈ left.flatMap input.localizedRule3PhysicalUnitIds ↔
          unit ∈ right.flatMap input.localizedRule3PhysicalUnitIds) ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        (∃ entry ∈ (input.mergeLocalizedRerootRule3ObservationChildren left).flatten,
            entry.2.physicalUnitId = unit) ↔
          ∃ entry ∈ (input.mergeLocalizedRerootRule3ObservationChildren right).flatten,
            entry.2.physicalUnitId = unit) :=
  ⟨input.map_localizedRerootRule3SpatialKeyObservable_eq_of_perm_of_descending
    left right permutation leftDescending rightDescending,
   fun unit => input.localizedRule3PhysicalUnitIds_mem_eq_of_perm left right permutation unit,
   fun unit =>
    input.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_eq_of_perm
      left right permutation unit⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
