import TetraStereo.OneCenter.LocalizedRule3TopologyObservableCongruence

set_option autoImplicit false

/-!
# Assembled-parent observable congruence for localized extended Rule 3

`LocalizedExtendedFrameCompleteness.parentAssembly_congruence_of_perm_of_descending` compares two
descending child-key lists *before* a parent node assembles them: it proves that the child
observation sequences and the physical-unit incidences agree.  It does **not** yet show that the
parent key produced by the executable assembly

```
{ constitutional := OfficialRuleMajorKey.assemble rootKey (sorted.map (·.constitutional))
  observations   := rootObservations ++ mergeLocalizedRerootRule3ObservationChildren sorted
  rule3          := rootPriorities   ++ mergeLocalizedRerootRule3PriorityChildren sorted }
```

has the same comparison-visible numeric projection.  This module supplies that missing step.

The key semantic point is that the parent's `LocalizedRerootRule3SpatialKeyObservable` depends on
the child list only through the child observable sequence and, for the physical-unit projection,
through the pointwise unit incidence.  Slot addressing in the merged layers is recomputed from the
list position, so equal observable sequences (or pointwise topology-equivalent keys) give equal
merged Rule-1a/1b/2 and Rule-3 projections.  No literal key equality, no uniqueness of the
descending permutation and no whole-frame completeness statement is assumed; the hidden
`observations` and `sourceNodes` payloads may differ.

The results are:

* `assembledParent_observable_eq_of_map_eq`: equal child observable sequences induce equal parent
  observable projections for any fixed node-level root key/root observation data;
* `assembledParent_physicalUnitIds_mem_iff_of_merged`: equal merged child unit membership induces
  equal parent physical-unit membership (the root observations are fixed);
* `assembledParent_congruence_of_forall₂`: the fully general pointwise
  `LocalizedRule3SpatialKeyTopologyEquivalent` version;
* `assembledParent_congruence_of_perm_of_descending`: the permuted-descending child list bridge,
  stated in exactly the assembled-parent shape used by the compiler;
* `assembledParent_congruence_of_perm_of_descending_node`: the same statement with the concrete
  node-derived root key and root observation projections of
  `buildLocalizedRerootRecursiveRule3SpatialKey?`.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Generic list helpers -/

/-- Flattened membership in terms of addressed layers. -/
private theorem exists_mem_flatten_iff {α : Type*} (P : α → Prop) :
    ∀ (layers : List (List α)),
      (∃ entry, entry ∈ layers.flatten ∧ P entry) ↔
        ∃ layer, layer ∈ layers ∧ ∃ entry, entry ∈ layer ∧ P entry
  | [] => by simp
  | layer :: layers => by
      simp only [List.flatten_cons, List.mem_append, List.mem_cons]
      constructor
      · rintro ⟨entry, entryMem | entryMem, Pentry⟩
        · exact ⟨layer, Or.inl rfl, entry, entryMem, Pentry⟩
        · obtain ⟨found, foundMem, entry, entryMem, Pentry⟩ :=
            (exists_mem_flatten_iff P layers).mp ⟨entry, entryMem, Pentry⟩
          exact ⟨found, Or.inr foundMem, entry, entryMem, Pentry⟩
      · rintro ⟨found, rfl | foundMem, entry, entryMem, Pentry⟩
        · exact ⟨entry, Or.inl entryMem, Pentry⟩
        · obtain ⟨entry, entryMem, Pentry⟩ :=
            (exists_mem_flatten_iff P layers).mpr ⟨found, foundMem, entry, entryMem, Pentry⟩
          exact ⟨entry, Or.inr entryMem, Pentry⟩

/-- Membership in a flat-map of per-key lists is invariant under a pointwise relation whose
membership readings agree. -/
private theorem exists_mem_iff_of_forall₂
    {α γ : Type*} {r : α → α → Prop}
    (f : α → List γ)
    (pointwise : ∀ a b, r a b → ∀ c, c ∈ f a ↔ c ∈ f b)
    (c : γ)
    {left right : List α}
    (related : List.Forall₂ r left right) :
    (∃ a, a ∈ left ∧ c ∈ f a) ↔ (∃ a, a ∈ right ∧ c ∈ f a) := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      simp only [List.mem_cons]
      constructor
      · rintro ⟨a, rfl | tailMem, cMem⟩
        · exact ⟨_, Or.inl rfl, (pointwise _ _ head c).mp cMem⟩
        · obtain ⟨b, bMem, cMem⟩ := ih.mp ⟨a, tailMem, cMem⟩
          exact ⟨b, Or.inr bMem, cMem⟩
      · rintro ⟨b, rfl | tailMem, cMem⟩
        · exact ⟨_, Or.inl rfl, (pointwise _ _ head c).mpr cMem⟩
        · obtain ⟨a, aMem, cMem⟩ := ih.mpr ⟨b, tailMem, cMem⟩
          exact ⟨a, Or.inr aMem, cMem⟩

/-! ## Merging addressed child layers is a function of the projected layers -/

/-- Merge already-projected addressed child layers beneath their list slots.  This is the shared
normal form of `OfficialRuleMajorKey.mergeChildren` and of the localized child merges. -/
private def mergeLayers {α : Type*}
    (children : List (List (List (OfficialSparseEntry α)))) :
    List (List (OfficialSparseEntry α)) :=
  let count := children.foldl (fun longest child => max longest child.length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.getD depth [])

/-- Constitutional child merging only reads the projected child layers. -/
private theorem officialMergeChildren_eq_mergeLayers {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.mergeChildren children layers =
      mergeLayers (children.map layers) := by
  simp only [OfficialRuleMajorKey.mergeChildren, OfficialRuleMajorKey.childLayerCount,
    mergeLayers, List.foldl_map, List.zipIdx_map, List.flatMap_map]
  rfl

/-- Rule-3 priority child merging only reads the projected child priority layers. -/
private theorem localizedRule3PriorityMerge_eq_mergeLayers
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.mergeLocalizedRerootRule3PriorityChildren children =
      mergeLayers (children.map fun child => child.rule3) := by
  simp only [mergeLocalizedRerootRule3PriorityChildren,
    localizedRerootRule3PriorityChildLayerCount, mergeLayers,
    List.foldl_map, List.zipIdx_map, List.flatMap_map]
  rfl

/-! ## Child observable sequences and the assembled parent projection -/

/-- Pointwise topology-equivalent child keys have equal observable sequences. -/
private theorem map_observable_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    left.map input.localizedRerootRule3SpatialKeyObservable =
      right.map input.localizedRerootRule3SpatialKeyObservable := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp [head.1, ih]

/-- Equal child observable sequences induce equal comparison-visible parent projections for fixed
node-level root data.  The parent is assembled exactly as in
`buildLocalizedRerootRecursiveRule3SpatialKey?`; the root key, root observations and root
priorities are held fixed. -/
theorem assembledParent_observable_eq_of_map_eq
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPriorities : List (List (OfficialSparseEntry Nat)))
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (observations : left.map input.localizedRerootRule3SpatialKeyObservable =
      right.map input.localizedRerootRule3SpatialKeyObservable) :
    input.localizedRerootRule3SpatialKeyObservable
        { constitutional :=
            OfficialRuleMajorKey.assemble root (left.map fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren left
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren left } =
      input.localizedRerootRule3SpatialKeyObservable
        { constitutional :=
            OfficialRuleMajorKey.assemble root (right.map fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren right
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren right } := by
  have rule1a := congrArg (List.map LocalizedRerootRule3SpatialKeyObservable.rule1a)
    observations
  have rule1b := congrArg (List.map LocalizedRerootRule3SpatialKeyObservable.rule1b)
    observations
  have rule2 := congrArg (List.map LocalizedRerootRule3SpatialKeyObservable.rule2)
    observations
  have rule3 := congrArg (List.map LocalizedRerootRule3SpatialKeyObservable.rule3)
    observations
  simp only [List.map_map, Function.comp_def,
    localizedRerootRule3SpatialKeyObservable] at rule1a rule1b rule2 rule3
  simp only [localizedRerootRule3SpatialKeyObservable, OfficialRuleMajorKey.assemble,
    officialMergeChildren_eq_mergeLayers, localizedRule3PriorityMerge_eq_mergeLayers,
    List.map_map, Function.comp_def, rule1a, rule1b, rule2, rule3]

/-! ## Physical-unit membership of the assembled parent -/

/-- Pointwise topology-equivalent child lists have the same merged physical-unit membership. -/
theorem mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry, entry ∈
        (input.mergeLocalizedRerootRule3ObservationChildren left).flatten ∧
        entry.2.physicalUnitId = unit) ↔
      ∃ entry, entry ∈
        (input.mergeLocalizedRerootRule3ObservationChildren right).flatten ∧
        entry.2.physicalUnitId = unit := by
  rw [input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff left unit,
    input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff right unit]
  exact exists_mem_iff_of_forall₂
    (fun key => input.localizedRule3PhysicalUnitIds key)
    (fun _ _ keyRelated value => keyRelated.2 value) unit related

/-- A fixed root observation contributes the same physical units to the parent, so parent
physical-unit membership is the disjunction of the root and merged-child contributions. -/
private theorem mem_localizedRule3PhysicalUnitIds_append_iff
    (input : CertifiedLocalizedCIPInput)
    (rootObservations mergedObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (constitutional : OfficialRuleMajorKey input.Atom)
    (rule3 : List (List (OfficialSparseEntry Nat)))
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional := constitutional
          observations := rootObservations ++ mergedObservations
          rule3 := rule3 } ↔
      (∃ entry, entry ∈ rootObservations.flatten ∧
          entry.2.physicalUnitId = unit) ∨
        ∃ entry, entry ∈ mergedObservations.flatten ∧
          entry.2.physicalUnitId = unit := by
  rw [input.mem_localizedRule3PhysicalUnitIds_iff]
  dsimp only
  rw [exists_mem_flatten_iff
        (fun entry : OfficialSparseEntry input.LocalizedRule3SpatialNodeResult =>
          entry.2.physicalUnitId = unit) rootObservations,
    exists_mem_flatten_iff
        (fun entry : OfficialSparseEntry input.LocalizedRule3SpatialNodeResult =>
          entry.2.physicalUnitId = unit) mergedObservations]
  simp only [List.mem_append]
  constructor
  · rintro ⟨layer, layerMem, entry, entryMem, physical⟩
    rcases layerMem with layerMem | layerMem
    · exact Or.inl ⟨layer, layerMem, entry, entryMem, physical⟩
    · exact Or.inr ⟨layer, layerMem, entry, entryMem, physical⟩
  · rintro (⟨layer, layerMem, entry, entryMem, physical⟩ |
      ⟨layer, layerMem, entry, entryMem, physical⟩)
    · exact ⟨layer, Or.inl layerMem, entry, entryMem, physical⟩
    · exact ⟨layer, Or.inr layerMem, entry, entryMem, physical⟩

/-- Equal merged child unit membership induces equal physical-unit membership of the assembled
parent, because the root observations are fixed. -/
theorem assembledParent_physicalUnitIds_mem_iff_of_merged
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPriorities : List (List (OfficialSparseEntry Nat)))
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (merged : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      (∃ entry, entry ∈
          (input.mergeLocalizedRerootRule3ObservationChildren left).flatten ∧
          entry.2.physicalUnitId = unit) ↔
        ∃ entry, entry ∈
          (input.mergeLocalizedRerootRule3ObservationChildren right).flatten ∧
          entry.2.physicalUnitId = unit)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional :=
            OfficialRuleMajorKey.assemble root (left.map fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren left
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren left } ↔
      unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional :=
            OfficialRuleMajorKey.assemble root (right.map fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren right
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren right } := by
  rw [input.mem_localizedRule3PhysicalUnitIds_append_iff rootObservations
        (input.mergeLocalizedRerootRule3ObservationChildren left)
        (OfficialRuleMajorKey.assemble root (left.map fun child => child.constitutional))
        (rootPriorities ++ input.mergeLocalizedRerootRule3PriorityChildren left) unit,
    input.mem_localizedRule3PhysicalUnitIds_append_iff rootObservations
        (input.mergeLocalizedRerootRule3ObservationChildren right)
        (OfficialRuleMajorKey.assemble root (right.map fun child => child.constitutional))
        (rootPriorities ++ input.mergeLocalizedRerootRule3PriorityChildren right) unit]
  constructor
  · rintro (rootMem | mergedMem)
    · exact Or.inl rootMem
    · exact Or.inr ((merged unit).mp mergedMem)
  · rintro (rootMem | mergedMem)
    · exact Or.inl rootMem
    · exact Or.inr ((merged unit).mpr mergedMem)

/-! ## The assembled-parent congruence theorems -/

/-- General pointwise version: child lists related by
`LocalizedRule3SpatialKeyTopologyEquivalent` assemble to parents with the same comparison-visible
projection and the same physical-unit membership in their merged observations.  Only
observable equality and unit incidence are transported; the `observations` and `sourceNodes`
payloads need not agree. -/
theorem assembledParent_congruence_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPriorities : List (List (OfficialSparseEntry Nat)))
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    let parentLeft : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root (left.map fun child => child.constitutional)
        observations := rootObservations ++
          input.mergeLocalizedRerootRule3ObservationChildren left
        rule3 := rootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren left }
    let parentRight : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root (right.map fun child => child.constitutional)
        observations := rootObservations ++
          input.mergeLocalizedRerootRule3ObservationChildren right
        rule3 := rootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren right }
    input.localizedRerootRule3SpatialKeyObservable parentLeft =
        input.localizedRerootRule3SpatialKeyObservable parentRight ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        unit ∈ input.localizedRule3PhysicalUnitIds parentLeft ↔
          unit ∈ input.localizedRule3PhysicalUnitIds parentRight) ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        (∃ entry, entry ∈
            (input.mergeLocalizedRerootRule3ObservationChildren left).flatten ∧
            entry.2.physicalUnitId = unit) ↔
          ∃ entry, entry ∈
            (input.mergeLocalizedRerootRule3ObservationChildren right).flatten ∧
            entry.2.physicalUnitId = unit) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact assembledParent_observable_eq_of_map_eq input root rootObservations rootPriorities
      left right (map_observable_eq_of_forall₂ input related)
  · intro unit
    exact assembledParent_physicalUnitIds_mem_iff_of_merged input root rootObservations
      rootPriorities left right
      (mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂
        input left right related) unit
  · intro unit
    exact mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂
      input left right related unit

/-- Permuted-descending child lists assemble to parents with the same comparison-visible
projection and the same physical-unit identities, for fixed node-level root data.  This is the
missing assembled-parent step on top of
`parentAssembly_congruence_of_perm_of_descending`; the child `observations` payloads may still
differ. -/
theorem assembledParent_congruence_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPriorities : List (List (OfficialSparseEntry Nat)))
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : left.Perm right)
    (leftDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending left)
    (rightDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending right) :
    let parentLeft : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root (left.map fun child => child.constitutional)
        observations := rootObservations ++
          input.mergeLocalizedRerootRule3ObservationChildren left
        rule3 := rootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren left }
    let parentRight : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root (right.map fun child => child.constitutional)
        observations := rootObservations ++
          input.mergeLocalizedRerootRule3ObservationChildren right
        rule3 := rootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren right }
    input.localizedRerootRule3SpatialKeyObservable parentLeft =
        input.localizedRerootRule3SpatialKeyObservable parentRight ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        unit ∈ input.localizedRule3PhysicalUnitIds parentLeft ↔
          unit ∈ input.localizedRule3PhysicalUnitIds parentRight) ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        (∃ entry, entry ∈
            (input.mergeLocalizedRerootRule3ObservationChildren left).flatten ∧
            entry.2.physicalUnitId = unit) ↔
          ∃ entry, entry ∈
            (input.mergeLocalizedRerootRule3ObservationChildren right).flatten ∧
            entry.2.physicalUnitId = unit) := by
  have assembly := input.parentAssembly_congruence_of_perm_of_descending
    left right permutation leftDescending rightDescending
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact assembledParent_observable_eq_of_map_eq input root rootObservations rootPriorities
      left right assembly.1
  · intro unit
    exact assembledParent_physicalUnitIds_mem_iff_of_merged input root rootObservations
      rootPriorities left right assembly.2.2 unit
  · exact assembly.2.2

/-- The permuted-descending congruence with the concrete root key and root observation projections
that `buildLocalizedRerootRecursiveRule3SpatialKey?` uses at a branch node. -/
theorem assembledParent_congruence_of_perm_of_descending_node
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : left.Perm right)
    (leftDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending left)
    (rightDescending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending right) :
    let parentLeft : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey node false)
            (left.map fun child => child.constitutional)
        observations := input.localizedRule3SpatialRootObservations observation ++
          input.mergeLocalizedRerootRule3ObservationChildren left
        rule3 := input.localizedRule3SpatialRootPriorities observation ++
          input.mergeLocalizedRerootRule3PriorityChildren left }
    let parentRight : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey node false)
            (right.map fun child => child.constitutional)
        observations := input.localizedRule3SpatialRootObservations observation ++
          input.mergeLocalizedRerootRule3ObservationChildren right
        rule3 := input.localizedRule3SpatialRootPriorities observation ++
          input.mergeLocalizedRerootRule3PriorityChildren right }
    input.localizedRerootRule3SpatialKeyObservable parentLeft =
        input.localizedRerootRule3SpatialKeyObservable parentRight ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        unit ∈ input.localizedRule3PhysicalUnitIds parentLeft ↔
          unit ∈ input.localizedRule3PhysicalUnitIds parentRight) ∧
      (∀ unit : input.LocalizedRule3PhysicalUnitId,
        (∃ entry, entry ∈
            (input.mergeLocalizedRerootRule3ObservationChildren left).flatten ∧
            entry.2.physicalUnitId = unit) ↔
          ∃ entry, entry ∈
            (input.mergeLocalizedRerootRule3ObservationChildren right).flatten ∧
            entry.2.physicalUnitId = unit) :=
  assembledParent_congruence_of_perm_of_descending input
    (input.moleculeGraph.officialRuleMajorRootKey node false)
    (input.localizedRule3SpatialRootObservations observation)
    (input.localizedRule3SpatialRootPriorities observation)
    left right permutation leftDescending rightDescending

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
