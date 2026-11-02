import TetraStereo.OneCenter.LocalizedRule3ParentObservableCongruence

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Sorted-parent transport for localized recursive Rule-3 spatial keys

The executable recursive builder compiles every reroot child, sorts the compiled keys by the
cumulative Rules-1a--3 comparator, and only then assembles the parent from that sorted list.  An
independent declarative derivation may produce its own descending permutation of the *source*
child keys.  The two child lists therefore need not be equal, and after sorting even
`LocalizedRule3SpatialKeyTopologyEquivalent` child lists may order constitutionally tied keys
differently, so the sorted `observations` payloads -- and hence pointwise physical-unit
incidence -- can genuinely differ.

This module proves the precise transport needed in that situation.  Given

* `related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) children compiledChildren`,
* `sorted.Perm children`, and
* `input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted`,

the parent assembled from `sorted` and the parent assembled from
`input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren` are
`LocalizedRule3SpatialKeyTopologyEquivalent`, with the same root key, root observations and root
priorities.  The proof has exactly two components:

1. the comparison-visible numeric projection of the *assembled parent* agrees, because both sorted
   lists are descending permutations of the same projected child observables and the observable
   comparator decides equality exactly on equal projections
   (`map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂_of_perm_of_descending`);
2. physical-unit membership of the *assembled parent* agrees, because it reduces to the union of
   the child units, which a permutation and a pointwise topology equivalence both preserve
   (`mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_of_perm`).

No pointwise physical-unit incidence equality after sorting is asserted or required; only the
parent union is transported.  No whole-frame completeness statement is introduced, and the root
data is held fixed throughout.
-/

/-! ## Transport of the projected observable sequence -/

/-- Pointwise topology-equivalent child lists have equal comparison-visible projections. -/
theorem map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    left.map input.localizedRerootRule3SpatialKeyObservable =
      right.map input.localizedRerootRule3SpatialKeyObservable := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp [head.1, ih]

/-- A descending permutation of one list and the compiled descending sort of a pointwise
topology-equivalent list project to the same observable sequence.  The lists themselves need not
be permutations of one another: pointwise equivalence plus descending order is enough, because the
observable comparator decides equality exactly on equal projections. -/
theorem map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (children compiledChildren sorted : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) children compiledChildren)
    (permutation : sorted.Perm children)
    (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted) :
    sorted.map input.localizedRerootRule3SpatialKeyObservable =
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren).map
        input.localizedRerootRule3SpatialKeyObservable := by
  haveI : Std.TransCmp compareLocalizedRerootRule3SpatialKeyObservable :=
    compareLocalizedRerootRule3SpatialKeyObservable_transCmp
  have projected :
      children.map input.localizedRerootRule3SpatialKeyObservable =
        compiledChildren.map input.localizedRerootRule3SpatialKeyObservable :=
    input.map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂
      children compiledChildren related
  have projectedPermutation :
      (sorted.map input.localizedRerootRule3SpatialKeyObservable).Perm
        ((input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren).map
          input.localizedRerootRule3SpatialKeyObservable) := by
    refine (permutation.map input.localizedRerootRule3SpatialKeyObservable).trans ?_
    rw [projected]
    exact ((input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm compiledChildren).map
      input.localizedRerootRule3SpatialKeyObservable).symm
  exact List.Perm.eq_of_pairwise
    (le := fun left right =>
      compareLocalizedRerootRule3SpatialKeyObservable left right ≠ Ordering.lt)
    (fun a b _ _ lower upper =>
      (compareLocalizedRerootRule3SpatialKeyObservable_eq_iff a b).mp (by
        refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp lower)
        rw [← Std.OrientedCmp.isGE_eq_isLE]
        exact Ordering.ne_lt_iff_isGE.mp upper))
    (input.rule3SpatialKey_observable_pairwise_of_descending sorted descending)
    (input.rule3SpatialKey_observable_pairwise_of_descending
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending compiledChildren))
    projectedPermutation

/-! ## Transport of the physical-unit union -/

/-- The flat union of child physical-unit identities is invariant under pointwise topology
equivalence. -/
theorem exists_mem_localizedRule3PhysicalUnitIds_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ child, child ∈ left ∧ unit ∈ input.localizedRule3PhysicalUnitIds child) ↔
      ∃ child, child ∈ right ∧ unit ∈ input.localizedRule3PhysicalUnitIds child := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      simp only [List.mem_cons]
      constructor
      · rintro ⟨child, rfl | tailMem, unitMem⟩
        · exact ⟨_, Or.inl rfl, (head.2 unit).mp unitMem⟩
        · obtain ⟨target, targetMem, targetUnit⟩ := ih.mp ⟨child, tailMem, unitMem⟩
          exact ⟨target, Or.inr targetMem, targetUnit⟩
      · rintro ⟨child, rfl | tailMem, unitMem⟩
        · exact ⟨_, Or.inl rfl, (head.2 unit).mpr unitMem⟩
        · obtain ⟨source, sourceMem, sourceUnit⟩ := ih.mpr ⟨child, tailMem, unitMem⟩
          exact ⟨source, Or.inr sourceMem, sourceUnit⟩

/-- The physical units carried by the merged observations of a descending permutation of a child
list agree with those of the compiled descending sort of a pointwise topology-equivalent child
list.  Only the union is preserved; the sorted lists may order tied keys differently, so pointwise
incidence need not agree. -/
theorem mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_of_perm
    (input : CertifiedLocalizedCIPInput)
    (children compiledChildren sorted : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) children compiledChildren)
    (permutation : sorted.Perm children)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry, entry ∈
        (input.mergeLocalizedRerootRule3ObservationChildren sorted).flatten ∧
        entry.2.physicalUnitId = unit) ↔
      ∃ entry, entry ∈
        (input.mergeLocalizedRerootRule3ObservationChildren
          (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)).flatten ∧
        entry.2.physicalUnitId = unit := by
  rw [input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff sorted unit,
    input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren) unit]
  constructor
  · rintro ⟨child, childMem, unitMem⟩
    have childInChildren : child ∈ children := permutation.mem_iff.mp childMem
    obtain ⟨target, targetMem, targetUnit⟩ :=
      (input.exists_mem_localizedRule3PhysicalUnitIds_iff_of_forall₂
        children compiledChildren related unit).mp
        ⟨child, childInChildren, unitMem⟩
    exact ⟨target,
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm compiledChildren).mem_iff.mpr
        targetMem,
      targetUnit⟩
  · rintro ⟨child, childMem, unitMem⟩
    have childInCompiled : child ∈ compiledChildren :=
      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm compiledChildren).mem_iff.mp
        childMem
    obtain ⟨source, sourceMem, sourceUnit⟩ :=
      (input.exists_mem_localizedRule3PhysicalUnitIds_iff_of_forall₂
        children compiledChildren related unit).mpr
        ⟨child, childInCompiled, unitMem⟩
    exact ⟨source, permutation.mem_iff.mpr sourceMem, sourceUnit⟩

/-! ## The assembled-parent bridge -/

/-- The numeric, comparison-visible projection of the parent assembled from the declared
descending permutation `sorted` equals that of the parent assembled from the compiled sort
`sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren`, for fixed node-level root data. -/
theorem assembledParent_observable_eq_of_forall₂_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPriorities : List (List (OfficialSparseEntry Nat)))
    (children compiledChildren sorted : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) children compiledChildren)
    (permutation : sorted.Perm children)
    (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted) :
    input.localizedRerootRule3SpatialKeyObservable
        { constitutional :=
            OfficialRuleMajorKey.assemble root (sorted.map fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren sorted
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren sorted } =
      input.localizedRerootRule3SpatialKeyObservable
        { constitutional :=
            OfficialRuleMajorKey.assemble root
              ((input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren).map
                fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren
              (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren
              (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren) } :=
  assembledParent_observable_eq_of_map_eq input root rootObservations rootPriorities
    sorted (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)
    (input.map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂_of_perm_of_descending
      children compiledChildren sorted related permutation descending)

/-- The assembled parent's physical-unit membership is the union of the root and child units.
The union of the declared sorted list equals that of the compiled sort of a pointwise
topology-equivalent list; no pointwise incidence after sorting is asserted. -/
theorem assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPriorities : List (List (OfficialSparseEntry Nat)))
    (children compiledChildren sorted : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) children compiledChildren)
    (permutation : sorted.Perm children)
    (_descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional :=
            OfficialRuleMajorKey.assemble root (sorted.map fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren sorted
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren sorted } ↔
      unit ∈ input.localizedRule3PhysicalUnitIds
        { constitutional :=
            OfficialRuleMajorKey.assemble root
              ((input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren).map
                fun child => child.constitutional)
          observations := rootObservations ++
            input.mergeLocalizedRerootRule3ObservationChildren
              (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)
          rule3 := rootPriorities ++
            input.mergeLocalizedRerootRule3PriorityChildren
              (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren) } :=
  assembledParent_physicalUnitIds_mem_iff_of_merged input root rootObservations rootPriorities
    sorted (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)
    (fun value =>
      input.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_of_perm
        children compiledChildren sorted related permutation value)
    unit

/-- **Sorted-parent transport.**  The actual parent assembled from the declared descending
permutation `sorted` is topology-equivalent to the actual parent assembled from the compiled sort
of a pointwise topology-equivalent child list, with identical root key, root observations and root
priorities.  Both the comparison-visible numeric projection of the parent and its physical-unit
membership are transported; the sorted child `observations` payloads may differ. -/
theorem assembledParent_topologyEquivalent_of_forall₂_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootObservations :
      List (List (OfficialSparseEntry input.LocalizedRule3SpatialNodeResult)))
    (rootPriorities : List (List (OfficialSparseEntry Nat)))
    (children compiledChildren sorted : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) children compiledChildren)
    (permutation : sorted.Perm children)
    (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted) :
    let parentSorted : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root (sorted.map fun child => child.constitutional)
        observations := rootObservations ++
          input.mergeLocalizedRerootRule3ObservationChildren sorted
        rule3 := rootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren sorted }
    let parentCompiled : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root
            ((input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren).map
              fun child => child.constitutional)
        observations := rootObservations ++
          input.mergeLocalizedRerootRule3ObservationChildren
            (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)
        rule3 := rootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren
            (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren) }
    LocalizedRule3SpatialKeyTopologyEquivalent input parentSorted parentCompiled := by
  dsimp only
  refine ⟨?_, ?_⟩
  · exact assembledParent_observable_eq_of_forall₂_of_perm_of_descending
      input root rootObservations rootPriorities children compiledChildren sorted
      related permutation descending
  · intro unit
    exact assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_descending
      input root rootObservations rootPriorities children compiledChildren sorted
      related permutation descending unit

/-- The sorted-parent bridge with the concrete node-derived root key, root observations and root
priorities used by `buildLocalizedRerootRecursiveRule3SpatialKey?` at a branch node.  This is the
form needed when comparing an executable branch parent against an independently derived descending
permutation in the mutual key derivation. -/
theorem assembledParent_topologyEquivalent_of_forall₂_of_perm_of_descending_node
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (children compiledChildren sorted : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) children compiledChildren)
    (permutation : sorted.Perm children)
    (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted) :
    let parentSorted : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey node false)
            (sorted.map fun child => child.constitutional)
        observations := input.localizedRule3SpatialRootObservations observation ++
          input.mergeLocalizedRerootRule3ObservationChildren sorted
        rule3 := input.localizedRule3SpatialRootPriorities observation ++
          input.mergeLocalizedRerootRule3PriorityChildren sorted }
    let parentCompiled : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey node false)
            ((input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren).map
              fun child => child.constitutional)
        observations := input.localizedRule3SpatialRootObservations observation ++
          input.mergeLocalizedRerootRule3ObservationChildren
            (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren)
        rule3 := input.localizedRule3SpatialRootPriorities observation ++
          input.mergeLocalizedRerootRule3PriorityChildren
            (input.sortLocalizedRerootRecursiveRule3SpatialKeys compiledChildren) }
    LocalizedRule3SpatialKeyTopologyEquivalent input parentSorted parentCompiled :=
  assembledParent_topologyEquivalent_of_forall₂_of_perm_of_descending input
    (input.moleculeGraph.officialRuleMajorRootKey node false)
    (input.localizedRule3SpatialRootObservations observation)
    (input.localizedRule3SpatialRootPriorities observation)
    children compiledChildren sorted related permutation descending

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
