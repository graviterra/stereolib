import TetraStereo.OneCenter.LocalizedRerootRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Physical-unit-aware localized Rule 3

Ring opening and multiple-bond duplication can place the same physical geometrical unit in more
than one ligand digraph.  Treating that repeated unit as independent evidence can make a branch
order depend on which opponent was chosen.  This module gives each order-two unit an unordered
molecule-level identity, discovers identities shared by distinct ligand keys, and performs a
second recursive compilation with ordinary circular identities excluded *before* tied siblings
are sorted.

The four-ligand/two-unit perfect-matching topology is retained explicitly for later Rule 6 rather
than being erased pairwise.  This is a conservative executable topology boundary.  Proving that
the detector exhausts every IUPAC coupled-unit case remains a later chemical-completeness target;
no final descriptor pipeline depends on this module yet.
-/

namespace CertifiedLocalizedCIPInput

/-- Canonical unordered identity of one physical order-two bond. -/
structure LocalizedRule3PhysicalUnitId
    (input : CertifiedLocalizedCIPInput) where
  first : input.Atom
  second : input.Atom
  deriving DecidableEq, Repr

/-- Sort the two molecule atom identifiers so traversal direction cannot change unit identity. -/
def localizedRule3PhysicalUnitId
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.LocalizedRule3PhysicalUnitId :=
  if left ≤ right then { first := left, second := right }
  else { first := right, second := left }

theorem localizedRule3PhysicalUnitId_swap
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.localizedRule3PhysicalUnitId left right =
      input.localizedRule3PhysicalUnitId right left := by
  unfold localizedRule3PhysicalUnitId
  by_cases forward : left ≤ right
  · rw [if_pos forward]
    by_cases reverse : right ≤ left
    · have same : left = right := le_antisymm forward reverse
      subst right
      simp
    · rw [if_neg reverse]
  · rw [if_neg forward]
    have reverse : right ≤ left := le_of_lt (lt_of_not_ge forward)
    rw [if_pos reverse]

/-- Equality of canonical identities is exactly equality of unordered endpoint pairs. -/
theorem localizedRule3PhysicalUnitId_eq_iff
    (input : CertifiedLocalizedCIPInput)
    (left right otherLeft otherRight : input.Atom) :
    input.localizedRule3PhysicalUnitId left right =
        input.localizedRule3PhysicalUnitId otherLeft otherRight ↔
      (left = otherLeft ∧ right = otherRight) ∨
        (left = otherRight ∧ right = otherLeft) := by
  constructor
  · intro equal
    unfold localizedRule3PhysicalUnitId at equal
    by_cases firstForward : left ≤ right
    · rw [if_pos firstForward] at equal
      by_cases secondForward : otherLeft ≤ otherRight
      · rw [if_pos secondForward] at equal
        exact Or.inl ⟨congrArg LocalizedRule3PhysicalUnitId.first equal,
          congrArg LocalizedRule3PhysicalUnitId.second equal⟩
      · rw [if_neg secondForward] at equal
        exact Or.inr ⟨congrArg LocalizedRule3PhysicalUnitId.first equal,
          congrArg LocalizedRule3PhysicalUnitId.second equal⟩
    · rw [if_neg firstForward] at equal
      by_cases secondForward : otherLeft ≤ otherRight
      · rw [if_pos secondForward] at equal
        exact Or.inr ⟨congrArg LocalizedRule3PhysicalUnitId.second equal,
          congrArg LocalizedRule3PhysicalUnitId.first equal⟩
      · rw [if_neg secondForward] at equal
        exact Or.inl ⟨congrArg LocalizedRule3PhysicalUnitId.second equal,
          congrArg LocalizedRule3PhysicalUnitId.first equal⟩
  · rintro (⟨rfl, rfl⟩ | ⟨leftEq, rightEq⟩)
    · rfl
    · subst otherRight
      subst otherLeft
      exact input.localizedRule3PhysicalUnitId_swap left right

/-- Physical identity retained by one positive node observation. -/
def LocalizedRule3SpatialNodeResult.physicalUnitId
    {input : CertifiedLocalizedCIPInput}
    (result : input.LocalizedRule3SpatialNodeResult) :
    input.LocalizedRule3PhysicalUnitId :=
  input.localizedRule3PhysicalUnitId result.left result.right

/-- Distinct physical identities occurring anywhere in one recursively ranked ligand key. -/
def localizedRule3PhysicalUnitIds
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRule3PhysicalUnitId :=
  (key.observations.flatten.map fun entry => entry.2.physicalUnitId).eraseDups

private theorem mem_eraseDups_iff_for_rule3PhysicalUnits
    {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) (values : List α) : a ∈ values.eraseDups ↔ a ∈ values := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      by_cases same : a = head
      · subst head
        simp
      · have filteredMembership := mem_eraseDups_iff_for_rule3PhysicalUnits a
          (tail.filter fun b => !b == head)
        simpa [same] using filteredMembership
termination_by values.length
decreasing_by
  have filtered := List.length_filter_le (fun b => !b == head) tail
  simpa using Nat.lt_succ_of_le filtered

/-- Removing duplicate physical-unit identities changes multiplicity but not membership. -/
theorem mem_eraseDups_localizedRule3PhysicalUnitId_iff
    (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedRule3PhysicalUnitId)
    (units : List input.LocalizedRule3PhysicalUnitId) :
    unit ∈ units.eraseDups ↔ unit ∈ units :=
  mem_eraseDups_iff_for_rule3PhysicalUnits unit units

theorem eraseDups_localizedRule3PhysicalUnitId_nodup
    (input : CertifiedLocalizedCIPInput) :
    ∀ units : List input.LocalizedRule3PhysicalUnitId, units.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [input.mem_eraseDups_localizedRule3PhysicalUnitId_iff]
        simp
      · exact input.eraseDups_localizedRule3PhysicalUnitId_nodup
          (tail.filter fun unit => !unit == head)
termination_by units => units.length
decreasing_by
  have filtered := List.length_filter_le (fun unit => !unit == head) tail
  simpa using Nat.lt_succ_of_le filtered

/-- The distinct-identity projection of any observation list has no duplicates. -/
theorem localizedRule3PhysicalUnitIds_nodup
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.localizedRule3PhysicalUnitIds key).Nodup := by
  exact input.eraseDups_localizedRule3PhysicalUnitId_nodup _

/-- Exact provenance of a physical identity in a recursive key.  In particular, identities at
arbitrary merged child depths are visible to the later coupled-topology search. -/
theorem mem_localizedRule3PhysicalUnitIds_iff
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds key ↔
      ∃ layer ∈ key.observations, ∃ entry ∈ layer,
        entry.2.physicalUnitId = unit := by
  rw [localizedRule3PhysicalUnitIds,
    mem_eraseDups_iff_for_rule3PhysicalUnits]
  simp

/-- Number of distinct ligand keys containing one physical identity. -/
def localizedRule3PhysicalUnitKeyCount
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) : Nat :=
  (keys.filter fun key => (input.localizedRule3PhysicalUnitIds key).contains unit).length

/-- Reordering ligand keys cannot change how many keys contain a physical identity. -/
theorem localizedRule3PhysicalUnitKeyCount_eq_of_perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId)
    (permutation : left.Perm right) :
    input.localizedRule3PhysicalUnitKeyCount left unit =
      input.localizedRule3PhysicalUnitKeyCount right unit := by
  unfold localizedRule3PhysicalUnitKeyCount
  exact (permutation.filter fun key =>
    (input.localizedRule3PhysicalUnitIds key).contains unit).length_eq

/-- Physical units present in at least two distinct ligand keys. -/
def localizedRule3SharedPhysicalUnits
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRule3PhysicalUnitId :=
  ((keys.flatMap input.localizedRule3PhysicalUnitIds).eraseDups).filter fun unit =>
    decide (1 < input.localizedRule3PhysicalUnitKeyCount keys unit)

theorem mem_localizedRule3SharedPhysicalUnits_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3SharedPhysicalUnits keys ↔
      unit ∈ (keys.flatMap input.localizedRule3PhysicalUnitIds).eraseDups ∧
        1 < input.localizedRule3PhysicalUnitKeyCount keys unit := by
  unfold localizedRule3SharedPhysicalUnits
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

/-- All four ligand keys tie constitutionally before a coupled Rule-3 topology is considered. -/
def localizedRule3ConstitutionallyTied
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  keys.all fun left => keys.all fun right =>
    OfficialRuleMajorKey.compare left.constitutional right.constitutional == Ordering.eq

/-- Four singleton ligand views partitioned by exactly two physical units, each seen twice. -/
def hasLocalizedCoupledRule3PerfectMatching
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  let unitSets := keys.map input.localizedRule3PhysicalUnitIds
  let units := unitSets.flatten.eraseDups
  keys.length == 4 &&
    unitSets.all (fun keyUnits => keyUnits.length == 1) &&
    units.length == 2 &&
    units.all (fun unit => input.localizedRule3PhysicalUnitKeyCount keys unit == 2) &&
    input.localizedRule3ConstitutionallyTied keys

/-- Ordinary shared units are excluded; the explicit coupled perfect matching is retained. -/
def localizedRule3ExcludedPhysicalUnits
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRule3PhysicalUnitId :=
  if input.hasLocalizedCoupledRule3PerfectMatching keys then []
  else input.localizedRule3SharedPhysicalUnits keys

@[simp] theorem localizedRule3ExcludedPhysicalUnits_of_coupled
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (coupled : input.hasLocalizedCoupledRule3PerfectMatching keys = true) :
    input.localizedRule3ExcludedPhysicalUnits keys = [] := by
  simp [localizedRule3ExcludedPhysicalUnits, coupled]

theorem localizedRule3ExcludedPhysicalUnits_of_not_coupled
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (ordinary : input.hasLocalizedCoupledRule3PerfectMatching keys = false) :
    input.localizedRule3ExcludedPhysicalUnits keys =
      input.localizedRule3SharedPhysicalUnits keys := by
  simp [localizedRule3ExcludedPhysicalUnits, ordinary]

/-- Resolve one node while erasing a geometry whose physical identity was globally excluded. -/
noncomputable def localizedRule3SpatialNodeExcept?
    (input : CertifiedLocalizedCIPInput)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (node : OfficialCIPNode input.Atom) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  match input.localizedRule3SpatialNode? node with
  | none => none
  | some none => some none
  | some (some result) =>
      if excluded.contains result.physicalUnitId then some none
      else some (some result)

/-- Independent meaning of structural absence, deliberate cancellation, or retained geometry. -/
inductive DeclarativeLocalizedRule3SpatialNodeExceptOutcome
    (input : CertifiedLocalizedCIPInput)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (node : OfficialCIPNode input.Atom) :
    Option input.LocalizedRule3SpatialNodeResult → Prop
  | structuralNonunit
      (notUnit : ¬ input.LocalizedRule3NodeHasDoubleBondEdge node) :
      input.DeclarativeLocalizedRule3SpatialNodeExceptOutcome excluded node none
  | excludedUnit {result : input.LocalizedRule3SpatialNodeResult}
      (observed : input.DeclarativeLocalizedRule3SpatialNode node result)
      (excludedIdentity : result.physicalUnitId ∈ excluded) :
      input.DeclarativeLocalizedRule3SpatialNodeExceptOutcome excluded node none
  | retainedGeometry {result : input.LocalizedRule3SpatialNodeResult}
      (observed : input.DeclarativeLocalizedRule3SpatialNode node result)
      (freshIdentity : result.physicalUnitId ∉ excluded) :
      input.DeclarativeLocalizedRule3SpatialNodeExceptOutcome excluded node (some result)

theorem localizedRule3SpatialNodeExcept?_sound
    (input : CertifiedLocalizedCIPInput)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (node : OfficialCIPNode input.Atom)
    (outcome : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3SpatialNodeExcept? excluded node = some outcome) :
    input.DeclarativeLocalizedRule3SpatialNodeExceptOutcome excluded node outcome := by
  unfold localizedRule3SpatialNodeExcept? at computed
  cases originalComputed : input.localizedRule3SpatialNode? node with
  | none => simp [originalComputed] at computed
  | some original =>
      cases original with
      | none =>
          simp [originalComputed] at computed
          subst outcome
          exact DeclarativeLocalizedRule3SpatialNodeExceptOutcome.structuralNonunit
            (input.localizedRule3SpatialNode?_eq_some_none_implies_not_edge
              node originalComputed)
      | some result =>
          by_cases isExcluded : result.physicalUnitId ∈ excluded
          · simp [originalComputed, isExcluded] at computed
            subst outcome
            exact DeclarativeLocalizedRule3SpatialNodeExceptOutcome.excludedUnit
              (input.localizedRule3SpatialNode?_sound node result originalComputed)
              isExcluded
          · simp [originalComputed, isExcluded] at computed
            subst outcome
            exact DeclarativeLocalizedRule3SpatialNodeExceptOutcome.retainedGeometry
              (input.localizedRule3SpatialNode?_sound node result originalComputed)
              isExcluded

/-- Recompile a reroot tree with a fixed opponent-independent physical-unit exclusion set. -/
noncomputable def buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootRecursiveRule3SpatialKey
  | 0, cursor => do
      let children ← input.localizedRerootChildren? cursor
      let observation ← input.localizedRule3SpatialNodeExcept?
        excluded cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }
      else none
  | fuel + 1, cursor => do
      let children ← input.localizedRerootChildren? cursor
      let observation ← input.localizedRule3SpatialNodeExcept?
        excluded cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }
      else
        let childKeys ← children.mapM
          (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept? excluded fuel)
        let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations observation ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities observation ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }

mutual
  /-- Independent recursively re-ranked key derivation under a fixed exclusion set. -/
  inductive DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (excluded : List input.LocalizedRule3PhysicalUnitId) :
      Nat → input.LocalizedRerootCursor carrierFuel →
        input.LocalizedRerootRecursiveRule3SpatialKey → Prop
    | terminal {fuel cursor children observation}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (empty : children = [])
        (observed : input.DeclarativeLocalizedRule3SpatialNodeExceptOutcome
          excluded cursor.occurrence.1.node observation) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept excluded fuel cursor
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations observation
            rule3 := input.localizedRule3SpatialRootPriorities observation }
    | branch {fuel cursor children observation childKeys sorted}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (nonempty : children ≠ [])
        (observed : input.DeclarativeLocalizedRule3SpatialNodeExceptOutcome
          excluded cursor.occurrence.1.node observation)
        (childDerivations :
          input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList
            excluded fuel children childKeys)
        (ranking : sorted.Perm childKeys)
        (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending sorted) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept excluded
          (fuel + 1) cursor
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations observation ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities observation ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }

  /-- Pointwise exclusion-aware derivations for an exact reroot child list. -/
  inductive DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (excluded : List input.LocalizedRule3PhysicalUnitId) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        List input.LocalizedRerootRecursiveRule3SpatialKey → Prop
    | nil (fuel : Nat) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList
          excluded fuel [] []
    | cons {fuel cursor cursors key keys}
        (head : input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept
          excluded fuel cursor key)
        (tail : input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList
          excluded fuel cursors keys) :
        input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList
          excluded fuel (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (sound : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
        excluded fuel cursor = some key →
      input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept
        excluded fuel cursor key) :
    ∀ cursors keys,
      (cursors : List (input.LocalizedRerootCursor carrierFuel)).mapM
          (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept? excluded fuel) =
        some (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) →
      input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList
        excluded fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
          excluded fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept? excluded fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList.cons
                (sound cursor head headComputed)
                (input.mapM_buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_sound
                  excluded sound cursors tail tailComputed)

/-- Successful exclusion-aware recompilation has the complete independent recursive meaning. -/
theorem buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootRecursiveRule3SpatialKey),
      input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
        excluded fuel cursor = some key →
      input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept
        excluded fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKeyExcept? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed : input.localizedRule3SpatialNodeExcept?
              excluded cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept.terminal
                  (input.localizedRerootChildren?_sound cursor children childrenComputed)
                  terminal
                  (input.localizedRule3SpatialNodeExcept?_sound
                    excluded cursor.occurrence.1.node observation observationComputed)
              · simp [childrenComputed, observationComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKeyExcept? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          cases observationComputed : input.localizedRule3SpatialNodeExcept?
              excluded cursor.occurrence.1.node with
          | none => simp [childrenComputed, observationComputed] at computed
          | some observation =>
              by_cases terminal : children = []
              · simp [childrenComputed, observationComputed, terminal] at computed
                subst key
                exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept.terminal
                  (input.localizedRerootChildren?_sound cursor children childrenComputed)
                  terminal
                  (input.localizedRule3SpatialNodeExcept?_sound
                    excluded cursor.occurrence.1.node observation observationComputed)
              · cases childKeysComputed : children.mapM
                    (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                      excluded fuel) with
                | none =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                | some childKeys =>
                    simp [childrenComputed, observationComputed, terminal,
                      childKeysComputed] at computed
                    subst key
                    exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExcept.branch
                      (input.localizedRerootChildren?_sound cursor children childrenComputed)
                      terminal
                      (input.localizedRule3SpatialNodeExcept?_sound
                        excluded cursor.occurrence.1.node observation observationComputed)
                      (input.mapM_buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_sound
                        excluded
                        (fun child childKey childComputed =>
                          input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_sound
                            excluded fuel child childKey childComputed)
                        children childKeys childKeysComputed)
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_perm childKeys)
                      (input.sortLocalizedRerootRecursiveRule3SpatialKeys_descending childKeys)

/-- Two-pass physical-unit-aware keys for one fixed ligand frame. -/
structure LocalizedRule3CanonicalKeyFrame
    (input : CertifiedLocalizedCIPInput) where
  rawKeys : List input.LocalizedRerootRecursiveRule3SpatialKey
  coupled : Bool
  excluded : List input.LocalizedRule3PhysicalUnitId
  keys : List input.LocalizedRerootRecursiveRule3SpatialKey

/-- First discover shared identities; then rebuild every ligand under one common exclusion set. -/
noncomputable def buildLocalizedRule3CanonicalKeyFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel)) :
    Option input.LocalizedRule3CanonicalKeyFrame := do
  let rawKeys ← cursors.mapM
    (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel)
  let coupled := input.hasLocalizedCoupledRule3PerfectMatching rawKeys
  let excluded := input.localizedRule3ExcludedPhysicalUnits rawKeys
  let keys ← cursors.mapM
    (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept? excluded fuel)
  some { rawKeys := rawKeys, coupled := coupled, excluded := excluded, keys := keys }

private theorem mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_sound_for_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (computed : cursors.mapM
      (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) = some keys) :
    input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList fuel cursors keys := by
  induction cursors generalizing keys with
  | nil =>
      simp at computed
      subst keys
      exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList.nil fuel
  | cons cursor cursors ih =>
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootRecursiveRule3SpatialKey?
          fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList.cons
                (input.buildLocalizedRerootRecursiveRule3SpatialKey?_sound
                  fuel cursor head headComputed)
                (ih tail tailComputed)

/-- Independent meaning of the discovery pass, topology choice, and exclusion-aware rebuild. -/
def DeclarativeLocalizedRule3CanonicalKeyFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyList
      fuel cursors frame.rawKeys ∧
    frame.coupled = input.hasLocalizedCoupledRule3PerfectMatching frame.rawKeys ∧
    frame.excluded = input.localizedRule3ExcludedPhysicalUnits frame.rawKeys ∧
    input.DeclarativeLocalizedRerootRecursiveRule3SpatialKeyExceptList
      frame.excluded fuel cursors frame.keys

/-- Successful two-pass construction is fully accounted for by the independent relations. -/
theorem buildLocalizedRule3CanonicalKeyFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedRule3CanonicalKeyFrame? fuel cursors = some frame) :
    input.DeclarativeLocalizedRule3CanonicalKeyFrame fuel cursors frame := by
  unfold buildLocalizedRule3CanonicalKeyFrame? at computed
  cases rawComputed : cursors.mapM
      (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
  | none => simp [rawComputed] at computed
  | some rawKeys =>
      let coupled := input.hasLocalizedCoupledRule3PerfectMatching rawKeys
      let excluded := input.localizedRule3ExcludedPhysicalUnits rawKeys
      cases keysComputed : cursors.mapM
          (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept? excluded fuel) with
      | none => simp [rawComputed, excluded, keysComputed] at computed
      | some keys =>
          simp [rawComputed, excluded, keysComputed] at computed
          subst frame
          exact ⟨
            input.mapM_buildLocalizedRerootRecursiveRule3SpatialKey?_sound_for_frame
              cursors rawKeys rawComputed,
            rfl,
            rfl,
            input.mapM_buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_sound
              excluded
              (fun cursor key keyComputed =>
                input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_sound
                  excluded fuel cursor key keyComputed)
              cursors keys keysComputed⟩

/-- Indexed access to the fixed unary key family produced by the two-pass construction. -/
def LocalizedRule3CanonicalKeyFrame.keyAt
    {input : CertifiedLocalizedCIPInput}
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (index : Fin frame.keys.length) :
    input.LocalizedRerootRecursiveRule3SpatialKey :=
  frame.keys.get index

/-- Opponent-independent comparison: every pair pulls back one common canonical key family. -/
def compareLocalizedRule3CanonicalKeyFrameAt
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3CanonicalKeyFrame) :
    Fin frame.keys.length → Fin frame.keys.length → Ordering :=
  Ordering.byKey frame.keyAt input.compareLocalizedRerootRecursiveRule3SpatialKeys

/-- Center-aware physical-unit handling preserves a lawful oriented transitive comparator. -/
theorem compareLocalizedRule3CanonicalKeyFrameAt_transCmp
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3CanonicalKeyFrame) :
    Std.TransCmp (input.compareLocalizedRule3CanonicalKeyFrameAt frame) := by
  letI : Std.TransCmp input.compareLocalizedRerootRecursiveRule3SpatialKeys :=
    input.compareLocalizedRerootRecursiveRule3SpatialKeys_transCmp
  unfold compareLocalizedRule3CanonicalKeyFrameAt
  infer_instance

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
