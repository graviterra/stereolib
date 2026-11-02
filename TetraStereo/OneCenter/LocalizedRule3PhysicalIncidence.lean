import TetraStereo.OneCenter.LocalizedExtendedFrameCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Physical-unit incidence congruence for localized Rule-3 spatial keys

`LocalizedRule3SpatialKeyTopologyEquivalent` is the relation used by the existing topology
congruence API.  It bundles two pieces of information:

* equality of the comparison-visible observable projection
  (`localizedRerootRule3SpatialKeyObservable`), and
* equality of physical-unit incidence (`localizedRule3PhysicalUnitIds`).

The parent-side reader-definedness route pursued here cannot assume the first component: two
independently compiled keys may have the same physical-unit incidence while their constitutional
and Rule-3 priority projections differ.  This module isolates the second component as a relation of
its own and reproves the transport facts that only need incidence.

Main results:

* `List.Forall₂` of the relation preserves the per-unit ligand-key count
  (`localizedRule3PhysicalUnitKeyCount`), the frame physical-unit universe
  (`localizedRule3FramePhysicalUnits`) and the ordinary shared-unit cancellation domain
  (`localizedRule3SharedPhysicalUnits`);
* the assembled parent's physical-unit membership is congruent when the pre-sort children are
  pointwise related, each side is replaced by an arbitrary permutation (an arbitrary sort), and
  the two root observations carry the same physical-unit identity;
* for an ordinary (non-coupled) topology resolution the excluded set is exactly the shared-unit
  domain, so exclusion membership is congruent as well.

The sorted child lists may order constitutionally tied keys differently, so pointwise incidence
*after* sorting is deliberately **not** asserted.  Only the union over children is transported.
This is a structural core for the mutual `isSome`/physical-identity induction; it is not by itself
an arbitrary-reader invariance statement for the full resolver.
-/

namespace CertifiedLocalizedCIPInput

/-! ## The physical-incidence relation -/

/-- Two recursively ranked Rule-3 spatial keys have the same physical-unit incidence when every
physical-unit identity occurs in one key exactly when it occurs in the other.  Unlike
`LocalizedRule3SpatialKeyTopologyEquivalent`, the comparison-visible observable projection is
deliberately not constrained: constitutional components and Rule-3 priority projections may
differ. -/
def LocalizedRule3PhysicalIncidenceEquivalent
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  ∀ unit : input.LocalizedRule3PhysicalUnitId,
    unit ∈ input.localizedRule3PhysicalUnitIds left ↔
      unit ∈ input.localizedRule3PhysicalUnitIds right

namespace LocalizedRule3PhysicalIncidenceEquivalent

/-- The relation is symmetric. -/
theorem symm
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3PhysicalIncidenceEquivalent input left right) :
    LocalizedRule3PhysicalIncidenceEquivalent input right left :=
  fun unit => (related unit).symm

/-- The relation is reflexive. -/
theorem refl
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    LocalizedRule3PhysicalIncidenceEquivalent input key key :=
  fun _ => Iff.rfl

/-- Physical-unit identities have the same incidence in both keys. -/
theorem mem_physicalUnitIds_iff
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3PhysicalIncidenceEquivalent input left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds left ↔
      unit ∈ input.localizedRule3PhysicalUnitIds right :=
  related unit

end LocalizedRule3PhysicalIncidenceEquivalent

/-! ## Generic list transport helpers -/

/-- Membership in a flattened pointwise-related list is invariant. -/
private theorem exists_mem_flatMap_iff_of_forall₂
    {α β γ : Type*} {r : α → β → Prop}
    (f : α → List γ) (g : β → List γ)
    (pointwise : ∀ a b, r a b → ∀ c, c ∈ f a ↔ c ∈ g b)
    (c : γ) :
    ∀ {left : List α} {right : List β}, List.Forall₂ r left right →
      (c ∈ left.flatMap f ↔ c ∈ right.flatMap g)
  | [], [], .nil => by simp
  | a :: l₁, b :: l₂, .cons hab htail => by
      simp only [List.flatMap_cons, List.mem_append]
      rw [pointwise a b hab c,
        exists_mem_flatMap_iff_of_forall₂ f g pointwise c htail]

/-- Filter lengths agree along a pointwise relation with equivalent predicates. -/
private theorem length_filter_eq_of_forall₂
    {α β : Type*} {r : α → β → Prop}
    (p : α → Bool) (q : β → Bool)
    (pointwise : ∀ a b, r a b → (p a = true ↔ q b = true)) :
    ∀ {left : List α} {right : List β}, List.Forall₂ r left right →
      (left.filter p).length = (right.filter q).length
  | [], [], .nil => rfl
  | a :: l₁, b :: l₂, .cons hab htail => by
      by_cases head : p a = true
      · have other : q b = true := (pointwise a b hab).mp head
        simp [head, other,
          length_filter_eq_of_forall₂ p q pointwise htail]
      · have other : q b = false := by
          cases value : q b with
          | false => rfl
          | true => exact absurd ((pointwise a b hab).mpr value) head
        simp [head, other,
          length_filter_eq_of_forall₂ p q pointwise htail]

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

/-! ## Frame universe, per-unit key count and the ordinary shared domain -/

/-- The number of ligand keys containing one physical unit is invariant under pointwise physical
incidence. -/
theorem localizedRule3PhysicalUnitKeyCount_eq_of_forall₂_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3PhysicalUnitKeyCount left unit =
      input.localizedRule3PhysicalUnitKeyCount right unit := by
  unfold localizedRule3PhysicalUnitKeyCount
  exact length_filter_eq_of_forall₂
    (r := LocalizedRule3PhysicalIncidenceEquivalent input)
    (fun key => (input.localizedRule3PhysicalUnitIds key).contains unit)
    (fun key => (input.localizedRule3PhysicalUnitIds key).contains unit)
    (fun _ _ keyRelated => by simp [List.contains_eq_mem, keyRelated unit])
    related

/-- The frame physical-unit universe has the same membership under pointwise physical
incidence. -/
theorem mem_localizedRule3FramePhysicalUnits_iff_of_forall₂_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3FramePhysicalUnits left ↔
      unit ∈ input.localizedRule3FramePhysicalUnits right := by
  unfold localizedRule3FramePhysicalUnits
  rw [input.mem_eraseDups_localizedRule3PhysicalUnitId_iff,
    input.mem_eraseDups_localizedRule3PhysicalUnitId_iff]
  exact exists_mem_flatMap_iff_of_forall₂
    (r := LocalizedRule3PhysicalIncidenceEquivalent input)
    (fun key => input.localizedRule3PhysicalUnitIds key)
    (fun key => input.localizedRule3PhysicalUnitIds key)
    (fun _ _ keyRelated c => keyRelated c) unit related

/-- The ordinary shared-unit cancellation domain has the same membership under pointwise physical
incidence. -/
theorem mem_localizedRule3SharedPhysicalUnits_iff_of_forall₂_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3SharedPhysicalUnits left ↔
      unit ∈ input.localizedRule3SharedPhysicalUnits right := by
  have frame :=
    input.mem_localizedRule3FramePhysicalUnits_iff_of_forall₂_physicalIncidence
      left right related unit
  unfold localizedRule3FramePhysicalUnits at frame
  have count :=
    input.localizedRule3PhysicalUnitKeyCount_eq_of_forall₂_physicalIncidence
      left right related unit
  rw [input.mem_localizedRule3SharedPhysicalUnits_iff,
    input.mem_localizedRule3SharedPhysicalUnits_iff]
  constructor
  · rintro ⟨member, many⟩
    exact ⟨frame.mp member, by rw [← count]; exact many⟩
  · rintro ⟨member, many⟩
    exact ⟨frame.mpr member, by rw [count]; exact many⟩

/-- For an ordinary (non-coupled) resolution the excluded set is exactly the ordinary shared-unit
domain, so exclusion membership is congruent under pointwise physical incidence.  The excluded
list is not assumed empty. -/
theorem mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff_of_forall₂_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left .ordinary ↔
      unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right .ordinary := by
  simpa using
    input.mem_localizedRule3SharedPhysicalUnits_iff_of_forall₂_physicalIncidence
      left right related unit

/-! ## The root observation -/

/-- Physical-incidence relation on the optional root observation of a node.  Structural absence is
related only to structural absence; two retained geometrical readings are related when they carry
the same physical-unit identity.  The remaining fields of the node result may differ. -/
def LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent
    (input : CertifiedLocalizedCIPInput)
    (left right : Option input.LocalizedRule3SpatialNodeResult) : Prop :=
  match left, right with
  | none, none => True
  | some leftResult, some rightResult =>
      leftResult.physicalUnitId = rightResult.physicalUnitId
  | _, _ => False

/-- The root observation contributes a physical identity exactly when its optional reading retains
that identity. -/
private theorem mem_localizedRule3SpatialRootObservations_flatten_iff
    (input : CertifiedLocalizedCIPInput)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry, entry ∈
        (input.localizedRule3SpatialRootObservations observation).flatten ∧
        entry.2.physicalUnitId = unit) ↔
      ∃ result, observation = some result ∧ result.physicalUnitId = unit := by
  cases observation with
  | none => simp [localizedRule3SpatialRootObservations]
  | some result =>
      simp [localizedRule3SpatialRootObservations]

/-- Root observations with the same physical identity contribute the same physical units. -/
theorem mem_localizedRule3SpatialRootObservations_physicalUnitId_iff_of_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    {left right : Option input.LocalizedRule3SpatialNodeResult}
    (related :
      LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent input left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry, entry ∈ (input.localizedRule3SpatialRootObservations left).flatten ∧
        entry.2.physicalUnitId = unit) ↔
      ∃ entry, entry ∈ (input.localizedRule3SpatialRootObservations right).flatten ∧
        entry.2.physicalUnitId = unit := by
  rw [mem_localizedRule3SpatialRootObservations_flatten_iff,
    mem_localizedRule3SpatialRootObservations_flatten_iff]
  cases left with
  | none =>
      cases right with
      | none => simp
      | some rightResult => exact (related : False).elim
  | some leftResult =>
      cases right with
      | none => exact (related : False).elim
      | some rightResult =>
          have same :
              leftResult.physicalUnitId = rightResult.physicalUnitId := related
          simp [same]

/-! ## Child union transport -/

/-- The flat union of child physical-unit identities is invariant under pointwise physical
incidence. -/
theorem exists_mem_localizedRule3PhysicalUnitIds_iff_of_forall₂_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ child, child ∈ left ∧ unit ∈ input.localizedRule3PhysicalUnitIds child) ↔
      ∃ child, child ∈ right ∧ unit ∈ input.localizedRule3PhysicalUnitIds child := by
  induction related with
  | nil => simp
  | cons head tail ih =>
      simp only [List.mem_cons]
      constructor
      · rintro ⟨child, rfl | tailMem, unitMem⟩
        · exact ⟨_, Or.inl rfl, (head unit).mp unitMem⟩
        · obtain ⟨target, targetMem, targetUnit⟩ := ih.mp ⟨child, tailMem, unitMem⟩
          exact ⟨target, Or.inr targetMem, targetUnit⟩
      · rintro ⟨child, rfl | tailMem, unitMem⟩
        · exact ⟨_, Or.inl rfl, (head unit).mpr unitMem⟩
        · obtain ⟨source, sourceMem, sourceUnit⟩ := ih.mpr ⟨child, tailMem, unitMem⟩
          exact ⟨source, Or.inr sourceMem, sourceUnit⟩

/-- A physical-unit identity is carried by the merged child observations exactly when some child
key carries it.  Pointwise physical incidence transports that union; slot re-addressing after an
arbitrary permutation does not change it. -/
theorem mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (∃ entry, entry ∈
        (input.mergeLocalizedRerootRule3ObservationChildren left).flatten ∧
        entry.2.physicalUnitId = unit) ↔
      ∃ entry, entry ∈
        (input.mergeLocalizedRerootRule3ObservationChildren right).flatten ∧
        entry.2.physicalUnitId = unit := by
  rw [input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff left unit,
    input.mem_mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_iff right unit]
  exact input.exists_mem_localizedRule3PhysicalUnitIds_iff_of_forall₂_physicalIncidence
    left right related unit

/-! ## Assembled-parent physical-unit membership -/

/-- Membership of a physical unit in an assembled parent is the disjunction of the root
observation's contribution and the merged-child contribution. -/
private theorem mem_localizedRule3PhysicalUnitIds_append_physicalIncidence_iff
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

/-- **Assembled-parent physical incidence.**  Suppose two pre-sort child lists are pointwise
physically incident, `sortedLeft` is an arbitrary permutation of the left children and
`sortedRight` an arbitrary permutation of the right children, and the two optional root
observations carry the same physical identity.  Then the parent assembled on the left from
`sortedLeft` and the parent assembled on the right from `sortedRight` have the same physical-unit
membership.  The root constitutional component is shared, while the two root priority streams may
differ; the sorted child lists may genuinely reorder constitutionally tied children. -/
theorem assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_perm
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (leftRootObservation rightRootObservation :
      Option input.LocalizedRule3SpatialNodeResult)
    (rootRelated :
      LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent input
        leftRootObservation rightRootObservation)
    (leftRootPriorities rightRootPriorities :
      List (List (OfficialSparseEntry Nat)))
    (children compiledChildren sortedLeft sortedRight :
      List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related :
      List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input)
        children compiledChildren)
    (leftPermutation : sortedLeft.Perm children)
    (rightPermutation : sortedRight.Perm compiledChildren)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    let parentLeft : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root
            (sortedLeft.map fun child => child.constitutional)
        observations :=
          input.localizedRule3SpatialRootObservations leftRootObservation ++
            input.mergeLocalizedRerootRule3ObservationChildren sortedLeft
        rule3 := leftRootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren sortedLeft }
    let parentRight : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble root
            (sortedRight.map fun child => child.constitutional)
        observations :=
          input.localizedRule3SpatialRootObservations rightRootObservation ++
            input.mergeLocalizedRerootRule3ObservationChildren sortedRight
        rule3 := rightRootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren sortedRight }
    unit ∈ input.localizedRule3PhysicalUnitIds parentLeft ↔
      unit ∈ input.localizedRule3PhysicalUnitIds parentRight := by
  dsimp only
  rw [input.mem_localizedRule3PhysicalUnitIds_append_physicalIncidence_iff
        (input.localizedRule3SpatialRootObservations leftRootObservation)
        (input.mergeLocalizedRerootRule3ObservationChildren sortedLeft)
        (OfficialRuleMajorKey.assemble root
          (sortedLeft.map fun child => child.constitutional))
        (leftRootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren sortedLeft) unit,
    input.mem_localizedRule3PhysicalUnitIds_append_physicalIncidence_iff
        (input.localizedRule3SpatialRootObservations rightRootObservation)
        (input.mergeLocalizedRerootRule3ObservationChildren sortedRight)
        (OfficialRuleMajorKey.assemble root
          (sortedRight.map fun child => child.constitutional))
        (rightRootPriorities ++
          input.mergeLocalizedRerootRule3PriorityChildren sortedRight) unit]
  refine or_congr ?_ ?_
  · exact
      input.mem_localizedRule3SpatialRootObservations_physicalUnitId_iff_of_physicalIncidence
        rootRelated unit
  · exact
      (input.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_eq_of_perm
        sortedLeft children leftPermutation unit).trans
        ((input.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_physicalIncidence
          children compiledChildren related unit).trans
          (input.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_eq_of_perm
            sortedRight compiledChildren rightPermutation unit).symm)

/-- The assembled-parent physical-incidence theorem specialised to the concrete node-derived root
key and root priority streams used by `buildLocalizedRerootRecursiveRule3SpatialKey?` at a branch
node.  The two sides may use different retained root readings, provided they carry the same
physical-unit identity. -/
theorem assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_perm_node
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom)
    (leftRootObservation rightRootObservation :
      Option input.LocalizedRule3SpatialNodeResult)
    (rootRelated :
      LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent input
        leftRootObservation rightRootObservation)
    (children compiledChildren sortedLeft sortedRight :
      List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related :
      List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input)
        children compiledChildren)
    (leftPermutation : sortedLeft.Perm children)
    (rightPermutation : sortedRight.Perm compiledChildren)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    let parentLeft : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey node false)
            (sortedLeft.map fun child => child.constitutional)
        observations :=
          input.localizedRule3SpatialRootObservations leftRootObservation ++
            input.mergeLocalizedRerootRule3ObservationChildren sortedLeft
        rule3 := input.localizedRule3SpatialRootPriorities leftRootObservation ++
          input.mergeLocalizedRerootRule3PriorityChildren sortedLeft }
    let parentRight : input.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional :=
          OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey node false)
            (sortedRight.map fun child => child.constitutional)
        observations :=
          input.localizedRule3SpatialRootObservations rightRootObservation ++
            input.mergeLocalizedRerootRule3ObservationChildren sortedRight
        rule3 := input.localizedRule3SpatialRootPriorities rightRootObservation ++
          input.mergeLocalizedRerootRule3PriorityChildren sortedRight }
    unit ∈ input.localizedRule3PhysicalUnitIds parentLeft ↔
      unit ∈ input.localizedRule3PhysicalUnitIds parentRight :=
  assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_perm input
    (input.moleculeGraph.officialRuleMajorRootKey node false)
    leftRootObservation rightRootObservation rootRelated
    (input.localizedRule3SpatialRootPriorities leftRootObservation)
    (input.localizedRule3SpatialRootPriorities rightRootObservation)
    children compiledChildren sortedLeft sortedRight related
    leftPermutation rightPermutation unit

/-! ## Excluded-set congruence for the per-node reader

The executable node reader inspects the exclusion list only through `List.contains`, which is
`decide` of membership.  Two exclusion lists with the same membership therefore induce the same
node reading.  This is the small auxiliary fact needed when the excluded set is transported only as
a set. -/

/-- The exclusion-aware node reader is determined by exclusion-list membership alone. -/
theorem localizedRule3SpatialNodeExcept?_eq_of_physicalUnitIds_mem_iff
    (input : CertifiedLocalizedCIPInput)
    (leftExcluded rightExcluded : List input.LocalizedRule3PhysicalUnitId)
    (sameMembership : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ leftExcluded ↔ unit ∈ rightExcluded)
    (node : OfficialCIPNode input.Atom) :
    input.localizedRule3SpatialNodeExcept? leftExcluded node =
      input.localizedRule3SpatialNodeExcept? rightExcluded node := by
  unfold localizedRule3SpatialNodeExcept?
  cases input.localizedRule3SpatialNode? node with
  | none => rfl
  | some observation =>
      cases observation with
      | none => rfl
      | some result =>
          by_cases excludedLeft : result.physicalUnitId ∈ leftExcluded
          · have excludedRight : result.physicalUnitId ∈ rightExcluded :=
              (sameMembership _).mp excludedLeft
            simp [excludedLeft, excludedRight]
          · have excludedRight : result.physicalUnitId ∉ rightExcluded :=
              fun present => excludedLeft ((sameMembership _).mpr present)
            simp [excludedLeft, excludedRight]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalIncidenceEquivalent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3SpatialRootObservationPhysicalIncidenceEquivalent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalIncidenceEquivalent.symm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalIncidenceEquivalent.refl
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalIncidenceEquivalent.mem_physicalUnitIds_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3PhysicalUnitKeyCount_eq_of_forall₂_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRule3FramePhysicalUnits_iff_of_forall₂_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRule3SharedPhysicalUnits_iff_of_forall₂_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff_of_forall₂_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRule3SpatialRootObservations_physicalUnitId_iff_of_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_mem_localizedRule3PhysicalUnitIds_iff_of_forall₂_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootRule3ObservationChildren_physicalUnitId_mem_iff_of_forall₂_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_perm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.assembledParent_physicalUnitIds_mem_iff_of_forall₂_of_perm_of_perm_node
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialNodeExcept?_eq_of_physicalUnitIds_mem_iff
