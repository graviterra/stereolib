import TetraStereo.OneCenter.CIPRule3RecursiveBuilderAffineInvariance

/-!
# Affine invariance of the canonical localized Rule-3 builder

This module closes the second, physical-unit-aware pass of the localized Rule-3
compiler. It proves that injective coordinate transport preserves physical-unit
deduplication, coupled perfect matching, the induced exclusion set, exclusion-aware
recursive recompilation, and the assembled canonical key frame. In particular,
the complete canonical Rules 1a--3 key builder commutes with every invertible
rational affine transformation of the spatial realization.
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

private theorem eraseDupsByLoop_map_injective
    {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (mapValue : α → β) (injective : Function.Injective mapValue)
    (values kept : List α) :
    List.eraseDupsBy.loop (fun left right : β => left == right)
        (values.map mapValue) (kept.map mapValue) =
      (List.eraseDupsBy.loop (fun left right : α => left == right)
        values kept).map mapValue := by
  induction values generalizing kept with
  | nil => simp [List.eraseDupsBy.loop]
  | cons value values ih =>
      simp only [List.map_cons, List.eraseDupsBy.loop]
      have anyNatural :
          (kept.map mapValue).any (fun other => mapValue value == other) =
            kept.any (fun other => value == other) := by
        induction kept with
        | nil => rfl
        | cons other kept ih =>
            simp only [List.map_cons, List.any_cons]
            rw [show (mapValue value == mapValue other) = (value == other) by
              simp [injective.eq_iff]]
            rw [ih]
      rw [anyNatural]
      split
      · exact ih kept
      · exact ih (value :: kept)

theorem eraseDups_map_injective
    {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (mapValue : α → β) (injective : Function.Injective mapValue)
    (values : List α) :
    (values.map mapValue).eraseDups = values.eraseDups.map mapValue := by
  unfold List.eraseDups List.eraseDupsBy
  exact eraseDupsByLoop_map_injective mapValue injective values []

def LocalizedRule3PhysicalUnitId.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (unit : input.LocalizedRule3PhysicalUnitId)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3PhysicalUnitId :=
  { first := unit.first, second := unit.second }

theorem LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    Function.Injective (fun unit : input.LocalizedRule3PhysicalUnitId =>
      unit.mapSpatialPoints mapPoint) := by
  intro left right equal
  cases left
  cases right
  simp only [LocalizedRule3PhysicalUnitId.mapSpatialPoints] at equal
  simp_all

@[simp] theorem localizedRule3PhysicalUnitId_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitId left right =
      (input.localizedRule3PhysicalUnitId left right).mapSpatialPoints mapPoint := by
  unfold localizedRule3PhysicalUnitId
  by_cases forward : left ≤ right <;> simp [forward,
    LocalizedRule3PhysicalUnitId.mapSpatialPoints]

@[simp] theorem physicalUnitId_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (result : input.LocalizedRule3SpatialNodeResult) :
    (result.mapSpatialPoints mapPoint).physicalUnitId =
      result.physicalUnitId.mapSpatialPoints mapPoint := by
  unfold LocalizedRule3SpatialNodeResult.physicalUnitId
  exact localizedRule3PhysicalUnitId_mapSpatialPoints input mapPoint _ _

@[simp] theorem localizedRule3PhysicalUnitIds_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitIds
        (key.mapSpatialPoints mapPoint) =
      (input.localizedRule3PhysicalUnitIds key).map
        (fun unit => unit.mapSpatialPoints mapPoint) := by
  have rawEq :
      (key.mapSpatialPoints mapPoint).observations.flatten.map
          (fun entry => entry.2.physicalUnitId) =
        (key.observations.flatten.map
          (fun entry => entry.2.physicalUnitId)).map
            (fun unit => unit.mapSpatialPoints mapPoint) := by
    simp only [LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
    rw [← List.map_flatten, List.map_map, List.map_map]
    apply List.map_congr_left
    intro entry entryPresent
    exact physicalUnitId_mapSpatialPoints input mapPoint entry.2
  unfold localizedRule3PhysicalUnitIds
  rw [rawEq]
  rw [eraseDups_map_injective]
  exact LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint

theorem listContains_map_injective
    {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (mapValue : α → β) (injective : Function.Injective mapValue)
    (target : α) : ∀ values : List α,
    (values.map mapValue).contains (mapValue target) = values.contains target
  | [] => rfl
  | value :: values => by
      simp only [List.map_cons, List.contains_cons]
      rw [show (mapValue target == mapValue value) = (target == value) by
        simp [injective.eq_iff]]
      rw [listContains_map_injective mapValue injective target values]

@[simp] theorem localizedRule3PhysicalUnitKeyCount_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitKeyCount
        (keys.map fun key => key.mapSpatialPoints mapPoint)
        (unit.mapSpatialPoints mapPoint) =
      input.localizedRule3PhysicalUnitKeyCount keys unit := by
  unfold localizedRule3PhysicalUnitKeyCount
  rw [List.filter_map]
  have predicateEq :
      ((fun key : (input.mapSpatialPoints mapPoint).LocalizedRerootRecursiveRule3SpatialKey =>
          ((input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitIds key).contains
            (unit.mapSpatialPoints mapPoint)) ∘
        (fun key : input.LocalizedRerootRecursiveRule3SpatialKey =>
          key.mapSpatialPoints mapPoint)) =
        (fun key : input.LocalizedRerootRecursiveRule3SpatialKey =>
          (input.localizedRule3PhysicalUnitIds key).contains unit) := by
    funext key
    simp only [Function.comp_apply]
    rw [localizedRule3PhysicalUnitIds_mapSpatialPoints]
    exact listContains_map_injective
      (fun value => value.mapSpatialPoints mapPoint)
      (LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint)
      unit _
  rw [predicateEq, List.length_map]

@[simp] theorem localizedRule3ConstitutionallyTied_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3ConstitutionallyTied
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      input.localizedRule3ConstitutionallyTied keys := by
  unfold localizedRule3ConstitutionallyTied
  simp only [List.all_map,
    LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
  rfl

@[simp] theorem localizedRule3SharedPhysicalUnits_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3SharedPhysicalUnits
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      (input.localizedRule3SharedPhysicalUnits keys).map
        (fun unit => unit.mapSpatialPoints mapPoint) := by
  unfold localizedRule3SharedPhysicalUnits
  rw [List.flatMap_map]
  have unitSetsEq :
      (keys.flatMap fun key =>
          (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitIds
            (key.mapSpatialPoints mapPoint)) =
        (keys.flatMap input.localizedRule3PhysicalUnitIds).map
          (fun unit => unit.mapSpatialPoints mapPoint) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro key keyPresent
    exact localizedRule3PhysicalUnitIds_mapSpatialPoints input mapPoint key
  rw [unitSetsEq, eraseDups_map_injective]
  · rw [List.filter_map]
    have predicateEq :
        ((fun mappedUnit => decide
            (1 < (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitKeyCount
              (keys.map fun key => key.mapSpatialPoints mapPoint) mappedUnit)) ∘
          (fun unit : input.LocalizedRule3PhysicalUnitId =>
            unit.mapSpatialPoints mapPoint)) =
          (fun unit => decide (1 < input.localizedRule3PhysicalUnitKeyCount keys unit)) := by
      funext unit
      simp only [Function.comp_apply]
      rw [localizedRule3PhysicalUnitKeyCount_mapSpatialPoints]
    rw [predicateEq]
  · exact LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint

@[simp] theorem hasLocalizedCoupledRule3PerfectMatching_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).hasLocalizedCoupledRule3PerfectMatching
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      input.hasLocalizedCoupledRule3PerfectMatching keys := by
  unfold hasLocalizedCoupledRule3PerfectMatching
  simp only [List.length_map]
  have unitSetsEq :
      (keys.map fun key =>
          (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitIds
            (key.mapSpatialPoints mapPoint)) =
        (keys.map input.localizedRule3PhysicalUnitIds).map
          (List.map fun unit => unit.mapSpatialPoints mapPoint) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro key keyPresent
    exact localizedRule3PhysicalUnitIds_mapSpatialPoints input mapPoint key
  have unitSetsEqNested :
      (keys.map fun key => key.mapSpatialPoints mapPoint).map
          (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitIds =
        (keys.map input.localizedRule3PhysicalUnitIds).map
          (List.map fun unit => unit.mapSpatialPoints mapPoint) := by
    rw [List.map_map]
    exact unitSetsEq
  rw [unitSetsEqNested]
  rw [← List.map_flatten]
  rw [eraseDups_map_injective]
  · rw [localizedRule3ConstitutionallyTied_mapSpatialPoints]
    have singletonEq :
        keys.all (((fun keyUnits => keyUnits.length == 1) ∘
            (List.map fun unit => unit.mapSpatialPoints mapPoint)) ∘
              input.localizedRule3PhysicalUnitIds) =
          keys.all ((fun keyUnits => keyUnits.length == 1) ∘
            input.localizedRule3PhysicalUnitIds) := by
      apply List.all_congr rfl
      intro key
      change
        (((input.localizedRule3PhysicalUnitIds key).map
            (fun unit => unit.mapSpatialPoints mapPoint)).length == 1) =
          ((input.localizedRule3PhysicalUnitIds key).length == 1)
      rw [List.length_map]
    rw [List.all_map, List.all_map]
    rw [singletonEq]
    rw [List.length_map]
    have countsEq :
        ((keys.map input.localizedRule3PhysicalUnitIds).flatten.eraseDups).all
            ((fun mappedUnit =>
              (input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitKeyCount
                (keys.map fun key => key.mapSpatialPoints mapPoint) mappedUnit == 2) ∘
              (fun unit => unit.mapSpatialPoints mapPoint)) =
          ((keys.map input.localizedRule3PhysicalUnitIds).flatten.eraseDups).all
            (fun unit => input.localizedRule3PhysicalUnitKeyCount keys unit == 2) := by
      apply List.all_congr rfl
      intro unit
      change
        ((input.mapSpatialPoints mapPoint).localizedRule3PhysicalUnitKeyCount
            (keys.map fun key => key.mapSpatialPoints mapPoint)
            (unit.mapSpatialPoints mapPoint) == 2) =
          (input.localizedRule3PhysicalUnitKeyCount keys unit == 2)
      rw [localizedRule3PhysicalUnitKeyCount_mapSpatialPoints]
    rw [List.all_map]
    rw [countsEq]
    rw [List.all_map]
  · exact LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint

@[simp] theorem localizedRule3ExcludedPhysicalUnits_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3ExcludedPhysicalUnits
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      (input.localizedRule3ExcludedPhysicalUnits keys).map
        (fun unit => unit.mapSpatialPoints mapPoint) := by
  unfold localizedRule3ExcludedPhysicalUnits
  rw [hasLocalizedCoupledRule3PerfectMatching_mapSpatialPoints]
  cases input.hasLocalizedCoupledRule3PerfectMatching keys <;>
    simp [localizedRule3SharedPhysicalUnits_mapSpatialPoints]

@[simp] theorem localizedRule3SpatialNodeExcept?_affine
    (input : CertifiedLocalizedCIPInput)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (node : OfficialCIPNode input.Atom)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3SpatialNodeExcept?
        (excluded.map fun unit => unit.mapSpatialPoints transform.applyPoint) node =
      (input.localizedRule3SpatialNodeExcept? excluded node).map
        (Option.map fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3SpatialNodeExcept?
  rw [localizedRule3SpatialNode?_affine input node transform determinantNonzero]
  cases originalEq : input.localizedRule3SpatialNode? node with
  | none => rfl
  | some original =>
      cases original with
      | none => rfl
      | some result =>
          simp only [Option.map_some]
          rw [physicalUnitId_mapSpatialPoints]
          rw [listContains_map_injective
            (fun unit : input.LocalizedRule3PhysicalUnitId =>
              unit.mapSpatialPoints transform.applyPoint)
            (LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective
              input transform.applyPoint)
            result.physicalUnitId excluded]
          cases excluded.contains result.physicalUnitId <;> rfl

theorem buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
    buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
        (input.mapSpatialPoints transform.applyPoint)
          (excluded.map fun unit => unit.mapSpatialPoints transform.applyPoint)
          fuel (cursor.mapSpatialPoints transform.applyPoint) =
      (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
        excluded fuel cursor).map
          (fun key => key.mapSpatialPoints transform.applyPoint)
  | 0, cursor => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
      rw [localizedRerootChildren?_mapSpatialPoints]
      have nodeEq :
          (cursor.mapSpatialPoints transform.applyPoint).occurrence.1.node =
            cursor.occurrence.1.node := rfl
      rw [nodeEq, localizedRule3SpatialNodeExcept?_affine
        input excluded cursor.occurrence.1.node transform determinantNonzero]
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          cases observationEq : input.localizedRule3SpatialNodeExcept?
              excluded cursor.occurrence.1.node with
          | none => rfl
          | some observation =>
              by_cases terminal : children = []
              · simp [terminal, moleculeGraph_mapSpatialPoints,
                  localizedRule3SpatialRootObservations_mapSpatialPoints,
                  localizedRule3SpatialRootPriorities_mapSpatialPoints,
                  LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
              · simp [terminal]
  | fuel + 1, cursor => by
      unfold buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
      rw [localizedRerootChildren?_mapSpatialPoints]
      have nodeEq :
          (cursor.mapSpatialPoints transform.applyPoint).occurrence.1.node =
            cursor.occurrence.1.node := rfl
      rw [nodeEq, localizedRule3SpatialNodeExcept?_affine
        input excluded cursor.occurrence.1.node transform determinantNonzero]
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          cases observationEq : input.localizedRule3SpatialNodeExcept?
              excluded cursor.occurrence.1.node with
          | none => rfl
          | some observation =>
              by_cases terminal : children = []
              · simp [terminal, moleculeGraph_mapSpatialPoints,
                  localizedRule3SpatialRootObservations_mapSpatialPoints,
                  localizedRule3SpatialRootPriorities_mapSpatialPoints,
                  LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints]
              · simp [terminal]
                have mapMNatural :
                    children.mapM
                        (buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                          (input.mapSpatialPoints transform.applyPoint)
                          (excluded.map fun unit =>
                            unit.mapSpatialPoints transform.applyPoint) fuel ∘
                            fun child =>
                              child.mapSpatialPoints transform.applyPoint) =
                      (children.mapM
                        (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                          excluded fuel)).map
                        (fun keys => keys.map fun key =>
                          key.mapSpatialPoints transform.applyPoint) :=
                  listMapM_map_of_natural
                    (fun child => child.mapSpatialPoints transform.applyPoint)
                    (fun key => key.mapSpatialPoints transform.applyPoint)
                    (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                      excluded fuel)
                    (buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                      (input.mapSpatialPoints transform.applyPoint)
                      (excluded.map fun unit =>
                        unit.mapSpatialPoints transform.applyPoint) fuel)
                    (fun child =>
                      buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_affine
                        input excluded transform determinantNonzero fuel child)
                    children
                rw [mapMNatural]
                cases childKeysEq : children.mapM
                    (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                      excluded fuel) with
                | none => rfl
                | some childKeys =>
                    simp only [Option.map_some, Option.bind_some]
                    rw [sortLocalizedRerootRecursiveRule3SpatialKeys_mapSpatialPoints]
                    rw [mergeLocalizedRerootRule3ObservationChildren_mapSpatialPoints,
                      mergeLocalizedRerootRule3PriorityChildren_mapSpatialPoints]
                    simp only [LocalizedRerootRecursiveRule3SpatialKey.mapSpatialPoints,
                      List.map_append, List.map_map]
                    rfl

def LocalizedRule3CanonicalKeyFrame.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3CanonicalKeyFrame :=
  { rawKeys := frame.rawKeys.map fun key => key.mapSpatialPoints mapPoint
    coupled := frame.coupled
    excluded := frame.excluded.map fun unit => unit.mapSpatialPoints mapPoint
    keys := frame.keys.map fun key => key.mapSpatialPoints mapPoint }

theorem buildLocalizedRule3CanonicalKeyFrame?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (transform : RationalAffineFrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).buildLocalizedRule3CanonicalKeyFrame?
        fuel (cursors.map fun cursor =>
          cursor.mapSpatialPoints transform.applyPoint) =
      (input.buildLocalizedRule3CanonicalKeyFrame? fuel cursors).map
        (fun frame => frame.mapSpatialPoints transform.applyPoint) := by
  unfold buildLocalizedRule3CanonicalKeyFrame?
  rw [List.mapM_map]
  conv_lhs =>
    enter [2, rawKeys, coupled, excluded]
    rw [List.mapM_map]
  have rawNatural :
      cursors.mapM
          (buildLocalizedRerootRecursiveRule3SpatialKey?
            (input.mapSpatialPoints transform.applyPoint) fuel ∘
              fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
        (cursors.mapM
          (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel)).map
            (fun keys => keys.map fun key =>
              key.mapSpatialPoints transform.applyPoint) :=
    listMapM_map_of_natural
      (fun cursor => cursor.mapSpatialPoints transform.applyPoint)
      (fun key => key.mapSpatialPoints transform.applyPoint)
      (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel)
      (buildLocalizedRerootRecursiveRule3SpatialKey?
        (input.mapSpatialPoints transform.applyPoint) fuel)
      (fun cursor => input.buildLocalizedRerootRecursiveRule3SpatialKey?_affine
        transform determinantNonzero fuel cursor)
      cursors
  change
    (do
      let rawKeys ← cursors.mapM
        (buildLocalizedRerootRecursiveRule3SpatialKey?
          (input.mapSpatialPoints transform.applyPoint) fuel ∘
            fun cursor : input.LocalizedRerootCursor carrierFuel =>
              cursor.mapSpatialPoints transform.applyPoint)
      let coupled := hasLocalizedCoupledRule3PerfectMatching
        (input.mapSpatialPoints transform.applyPoint) rawKeys
      let excluded := localizedRule3ExcludedPhysicalUnits
        (input.mapSpatialPoints transform.applyPoint) rawKeys
      let keys ← cursors.mapM
        (buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
          (input.mapSpatialPoints transform.applyPoint) excluded fuel ∘
            fun cursor : input.LocalizedRerootCursor carrierFuel =>
              cursor.mapSpatialPoints transform.applyPoint)
      some
        ({ rawKeys := rawKeys
           coupled := coupled
           excluded := excluded
           keys := keys } :
          (input.mapSpatialPoints transform.applyPoint).LocalizedRule3CanonicalKeyFrame)) = _
  rw [rawNatural]
  cases rawKeysEq : cursors.mapM
      (input.buildLocalizedRerootRecursiveRule3SpatialKey? fuel) with
  | none => rfl
  | some rawKeys =>
      simp only [Option.map_some]
      let mappedRawKeys :
          List (LocalizedRerootRecursiveRule3SpatialKey
            (input.mapSpatialPoints transform.applyPoint)) :=
        rawKeys.map fun key => key.mapSpatialPoints transform.applyPoint
      let mappedCoupled := hasLocalizedCoupledRule3PerfectMatching
        (input.mapSpatialPoints transform.applyPoint) mappedRawKeys
      let mappedExcluded := localizedRule3ExcludedPhysicalUnits
        (input.mapSpatialPoints transform.applyPoint) mappedRawKeys
      change
        (cursors.mapM
            (buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                (input.mapSpatialPoints transform.applyPoint)
                mappedExcluded fuel ∘
              fun cursor : input.LocalizedRerootCursor carrierFuel =>
                cursor.mapSpatialPoints transform.applyPoint)).bind
            (fun keys => some
              ({ rawKeys := mappedRawKeys
                , coupled := mappedCoupled
                , excluded := mappedExcluded
                , keys := keys } :
                LocalizedRule3CanonicalKeyFrame
                  (input.mapSpatialPoints transform.applyPoint))) = _
      dsimp only [mappedRawKeys, mappedCoupled, mappedExcluded]
      rw [hasLocalizedCoupledRule3PerfectMatching_mapSpatialPoints,
        localizedRule3ExcludedPhysicalUnits_mapSpatialPoints]
      let excluded := input.localizedRule3ExcludedPhysicalUnits rawKeys
      have keysNatural :
          cursors.mapM
              (buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                (input.mapSpatialPoints transform.applyPoint)
                  (excluded.map fun unit =>
                    unit.mapSpatialPoints transform.applyPoint) fuel ∘
                fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
            (cursors.mapM
              (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                excluded fuel)).map
              (fun keys => keys.map fun key =>
                key.mapSpatialPoints transform.applyPoint) :=
        listMapM_map_of_natural
          (fun cursor => cursor.mapSpatialPoints transform.applyPoint)
          (fun key => key.mapSpatialPoints transform.applyPoint)
          (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
            excluded fuel)
          (buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
            (input.mapSpatialPoints transform.applyPoint)
              (excluded.map fun unit =>
                unit.mapSpatialPoints transform.applyPoint) fuel)
          (fun cursor =>
            buildLocalizedRerootRecursiveRule3SpatialKeyExcept?_affine
              input excluded transform determinantNonzero fuel cursor)
          cursors
      dsimp only [excluded] at keysNatural ⊢
      change
        (cursors.mapM
            (buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
              (input.mapSpatialPoints transform.applyPoint)
                (excluded.map fun unit =>
                  unit.mapSpatialPoints transform.applyPoint) fuel ∘
              fun cursor : input.LocalizedRerootCursor carrierFuel =>
                cursor.mapSpatialPoints transform.applyPoint)).bind
            (fun keys => some
              ({ rawKeys := rawKeys.map (fun key =>
                    key.mapSpatialPoints transform.applyPoint),
                 coupled := input.hasLocalizedCoupledRule3PerfectMatching rawKeys,
                 excluded := (input.localizedRule3ExcludedPhysicalUnits rawKeys).map
                   (fun unit => unit.mapSpatialPoints transform.applyPoint),
                 keys := keys } :
                LocalizedRule3CanonicalKeyFrame
                  (input.mapSpatialPoints transform.applyPoint))) = _
      have sourceTail :
          (do
            let rawKeys ← some rawKeys
            let keys ← cursors.mapM
              (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                (input.localizedRule3ExcludedPhysicalUnits rawKeys) fuel)
            some
              ({ rawKeys := rawKeys,
                 coupled := input.hasLocalizedCoupledRule3PerfectMatching rawKeys,
                 excluded := input.localizedRule3ExcludedPhysicalUnits rawKeys,
                 keys := keys } : input.LocalizedRule3CanonicalKeyFrame)) =
            (cursors.mapM
              (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
                (input.localizedRule3ExcludedPhysicalUnits rawKeys) fuel)).bind
              (fun keys => some
                ({ rawKeys := rawKeys,
                   coupled := input.hasLocalizedCoupledRule3PerfectMatching rawKeys,
                   excluded := input.localizedRule3ExcludedPhysicalUnits rawKeys,
                   keys := keys } : input.LocalizedRule3CanonicalKeyFrame)) := rfl
      rw [sourceTail]
      rw [keysNatural]
      cases keysEq : cursors.mapM
          (input.buildLocalizedRerootRecursiveRule3SpatialKeyExcept?
            excluded fuel) with
      | none =>
          rfl
      | some keys =>
          rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
