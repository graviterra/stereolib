import TetraStereo.OneCenter.CIPRule3CanonicalBuilderAffineInvariance
import TetraStereo.OneCenter.LocalizedRule3CoupledTopology

/-!
# Coordinate naturality of exhaustive coupled Rule-3 topology

The exhaustive search over the three four-ligand pairings depends on physical-unit incidence and
constitutional keys, not on the coordinate representation. This module proves that candidate
enumeration, validity filtering, ambiguity/uniqueness resolution, and the resulting cancellation
set commute with arbitrary coordinate transport.
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedRule3CoupledMatching.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (matching : input.LocalizedRule3CoupledMatching)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3CoupledMatching :=
  { pairing := matching.pairing
    firstUnit := matching.firstUnit.mapSpatialPoints mapPoint
    secondUnit := matching.secondUnit.mapSpatialPoints mapPoint }

def LocalizedRule3CoupledTopologyResolution.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (resolution : input.LocalizedRule3CoupledTopologyResolution)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3CoupledTopologyResolution :=
  match resolution with
  | .ordinary => .ordinary
  | .coupled matching => .coupled (matching.mapSpatialPoints mapPoint)

private theorem listProduct_map {α β γ δ : Type*}
    (mapLeft : α → γ) (mapRight : β → δ) :
    ∀ (left : List α) (right : List β),
      (left.map mapLeft).product (right.map mapRight) =
        (left.product right).map fun pair => (mapLeft pair.1, mapRight pair.2)
  | [], right => rfl
  | value :: values, right => by
      simp only [List.map_cons]
      change
        ((mapLeft value :: List.map mapLeft values) ×ˢ (List.map mapRight right)) =
          List.map (fun pair => (mapLeft pair.1, mapRight pair.2))
            ((value :: values) ×ˢ right)
      rw [List.product_cons, List.product_cons, List.map_append]
      congr 1
      · simp only [List.map_map]
        apply List.map_congr_left
        intro b present
        rfl
      · exact listProduct_map mapLeft mapRight values right

private theorem listProduct_map_left {α β γ : Type*}
    (mapLeft : α → γ) (left : List α) (right : List β) :
    (left.map mapLeft).product right =
      (left.product right).map fun pair => (mapLeft pair.1, pair.2) := by
  simpa using listProduct_map mapLeft (fun value : β => value) left right

@[simp] theorem localizedRule3FramePhysicalUnits_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3FramePhysicalUnits
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      (input.localizedRule3FramePhysicalUnits keys).map
        (fun unit => unit.mapSpatialPoints mapPoint) := by
  unfold localizedRule3FramePhysicalUnits
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
  exact LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint

@[simp] theorem localizedRule3PhysicalUnitIdLexLt_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.LocalizedRule3PhysicalUnitId) :
    (left.mapSpatialPoints mapPoint).LexLt (right.mapSpatialPoints mapPoint) ↔
      left.LexLt right := by
  rfl

@[simp] theorem declarativeLocalizedRule3ExactPairIncidence_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (unit : input.LocalizedRule3PhysicalUnitId)
    (first second outsideFirst outsideSecond :
      input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedRule3ExactPairIncidence
        (unit.mapSpatialPoints mapPoint)
        (first.mapSpatialPoints mapPoint) (second.mapSpatialPoints mapPoint)
        (outsideFirst.mapSpatialPoints mapPoint) (outsideSecond.mapSpatialPoints mapPoint) ↔
      input.DeclarativeLocalizedRule3ExactPairIncidence
        unit first second outsideFirst outsideSecond := by
  unfold DeclarativeLocalizedRule3ExactPairIncidence
  simp only [localizedRule3PhysicalUnitIds_mapSpatialPoints]
  constructor
  · rintro ⟨firstMem, secondMem, outsideFirstNot, outsideSecondNot⟩
    have injective := LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint
    exact ⟨List.mem_map_of_injective injective |>.mp firstMem,
      List.mem_map_of_injective injective |>.mp secondMem,
      fun present => outsideFirstNot (List.mem_map.mpr ⟨unit, present, rfl⟩),
      fun present => outsideSecondNot (List.mem_map.mpr ⟨unit, present, rfl⟩)⟩
  · rintro ⟨firstMem, secondMem, outsideFirstNot, outsideSecondNot⟩
    exact ⟨List.mem_map.mpr ⟨unit, firstMem, rfl⟩,
      List.mem_map.mpr ⟨unit, secondMem, rfl⟩,
      fun mappedMem => outsideFirstNot
        ((List.mem_map_of_injective
          (LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint)).mp
            mappedMem),
      fun mappedMem => outsideSecondNot
        ((List.mem_map_of_injective
          (LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint)).mp
            mappedMem)⟩

@[simp] theorem declarativeLocalizedRule3ComplementaryPairIncidence_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (firstUnit secondUnit : input.LocalizedRule3PhysicalUnitId)
    (pairFirst pairSecond complementFirst complementSecond :
      input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedRule3ComplementaryPairIncidence
        (firstUnit.mapSpatialPoints mapPoint) (secondUnit.mapSpatialPoints mapPoint)
        (pairFirst.mapSpatialPoints mapPoint) (pairSecond.mapSpatialPoints mapPoint)
        (complementFirst.mapSpatialPoints mapPoint)
        (complementSecond.mapSpatialPoints mapPoint) ↔
      input.DeclarativeLocalizedRule3ComplementaryPairIncidence
        firstUnit secondUnit pairFirst pairSecond complementFirst complementSecond := by
  unfold DeclarativeLocalizedRule3ComplementaryPairIncidence
  simp only [declarativeLocalizedRule3ExactPairIncidence_mapSpatialPoints]

@[simp] theorem declarativeLocalizedRule3FourWayConstitutionalTie_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (k0 k1 k2 k3 : input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedRule3FourWayConstitutionalTie
        (k0.mapSpatialPoints mapPoint) (k1.mapSpatialPoints mapPoint)
        (k2.mapSpatialPoints mapPoint) (k3.mapSpatialPoints mapPoint) ↔
      input.DeclarativeLocalizedRule3FourWayConstitutionalTie k0 k1 k2 k3 := by
  rfl

@[simp] theorem declarativeLocalizedRule3CoupledMatching_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedRule3CoupledMatching
        (keys.map fun key => key.mapSpatialPoints mapPoint)
        (matching.mapSpatialPoints mapPoint) ↔
      input.DeclarativeLocalizedRule3CoupledMatching keys matching := by
  have firstMem :
      matching.firstUnit.mapSpatialPoints mapPoint ∈
          (input.mapSpatialPoints mapPoint).localizedRule3FramePhysicalUnits
            (keys.map fun key => key.mapSpatialPoints mapPoint) ↔
        matching.firstUnit ∈ input.localizedRule3FramePhysicalUnits keys := by
    rw [localizedRule3FramePhysicalUnits_mapSpatialPoints]
    exact List.mem_map_of_injective
      (LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint)
  have secondMem :
      matching.secondUnit.mapSpatialPoints mapPoint ∈
          (input.mapSpatialPoints mapPoint).localizedRule3FramePhysicalUnits
            (keys.map fun key => key.mapSpatialPoints mapPoint) ↔
        matching.secondUnit ∈ input.localizedRule3FramePhysicalUnits keys := by
    rw [localizedRule3FramePhysicalUnits_mapSpatialPoints]
    exact List.mem_map_of_injective
      (LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint)
  cases keys with
  | nil => simp [DeclarativeLocalizedRule3CoupledMatching,
      LocalizedRule3CoupledMatching.mapSpatialPoints]
  | cons k0 rest =>
      cases rest with
      | nil => simp [DeclarativeLocalizedRule3CoupledMatching,
          LocalizedRule3CoupledMatching.mapSpatialPoints]
      | cons k1 rest =>
          cases rest with
          | nil => simp [DeclarativeLocalizedRule3CoupledMatching,
              LocalizedRule3CoupledMatching.mapSpatialPoints]
          | cons k2 rest =>
              cases rest with
              | nil => simp [DeclarativeLocalizedRule3CoupledMatching,
                  LocalizedRule3CoupledMatching.mapSpatialPoints]
              | cons k3 rest =>
                  cases rest with
                  | nil =>
                      have firstMem4 :
                          matching.firstUnit.mapSpatialPoints mapPoint ∈
                              (input.mapSpatialPoints mapPoint).localizedRule3FramePhysicalUnits
                                  [k0.mapSpatialPoints mapPoint,
                                    k1.mapSpatialPoints mapPoint,
                                    k2.mapSpatialPoints mapPoint,
                                    k3.mapSpatialPoints mapPoint] ↔
                            matching.firstUnit ∈
                              input.localizedRule3FramePhysicalUnits [k0, k1, k2, k3] := by
                        simpa only [List.map_cons, List.map_nil] using firstMem
                      have secondMem4 :
                          matching.secondUnit.mapSpatialPoints mapPoint ∈
                              (input.mapSpatialPoints mapPoint).localizedRule3FramePhysicalUnits
                                  [k0.mapSpatialPoints mapPoint,
                                    k1.mapSpatialPoints mapPoint,
                                    k2.mapSpatialPoints mapPoint,
                                    k3.mapSpatialPoints mapPoint] ↔
                            matching.secondUnit ∈
                              input.localizedRule3FramePhysicalUnits [k0, k1, k2, k3] := by
                        simpa only [List.map_cons, List.map_nil] using secondMem
                      cases matching.pairing <;>
                        simp [DeclarativeLocalizedRule3CoupledMatching, firstMem4, secondMem4,
                          LocalizedRule3CoupledMatching.mapSpatialPoints]
                  | cons k4 rest =>
                      simp [DeclarativeLocalizedRule3CoupledMatching,
                        LocalizedRule3CoupledMatching.mapSpatialPoints]

@[simp] theorem localizedRule3CoupledMatchingCandidates_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3CoupledMatchingCandidates
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      (input.localizedRule3CoupledMatchingCandidates keys).map
        (fun matching => matching.mapSpatialPoints mapPoint) := by
  unfold localizedRule3CoupledMatchingCandidates
  rw [localizedRule3FramePhysicalUnits_mapSpatialPoints]
  dsimp only
  let units := input.localizedRule3FramePhysicalUnits keys
  let mapUnit := fun unit : input.LocalizedRule3PhysicalUnitId =>
    unit.mapSpatialPoints mapPoint
  let mapInner := fun candidate : input.LocalizedRule3PhysicalUnitId ×
      LocalizedRule3FourLigandPairing => (mapUnit candidate.1, candidate.2)
  let makeMapped := fun candidate :
      (input.mapSpatialPoints mapPoint).LocalizedRule3PhysicalUnitId ×
        ((input.mapSpatialPoints mapPoint).LocalizedRule3PhysicalUnitId ×
          LocalizedRule3FourLigandPairing) =>
    ({ pairing := candidate.2.2
       firstUnit := candidate.1
       secondUnit := candidate.2.1 } :
      (input.mapSpatialPoints mapPoint).LocalizedRule3CoupledMatching)
  let makeSource := fun candidate : input.LocalizedRule3PhysicalUnitId ×
      (input.LocalizedRule3PhysicalUnitId × LocalizedRule3FourLigandPairing) =>
    ({ pairing := candidate.2.2
       firstUnit := candidate.1
       secondUnit := candidate.2.1 } : input.LocalizedRule3CoupledMatching)
  have innerEq :
      (units.map mapUnit).product localizedRule3FourLigandPairings =
        (units.product localizedRule3FourLigandPairings).map mapInner := by
    exact listProduct_map_left mapUnit units localizedRule3FourLigandPairings
  have outerEq :
      (units.map mapUnit).product
          ((units.product localizedRule3FourLigandPairings).map mapInner) =
        (units.product (units.product localizedRule3FourLigandPairings)).map
          (fun candidate => (mapUnit candidate.1, mapInner candidate.2)) := by
    exact listProduct_map mapUnit mapInner units
      (units.product localizedRule3FourLigandPairings)
  change
    List.map makeMapped
        ((units.map mapUnit).product
          ((units.map mapUnit).product localizedRule3FourLigandPairings)) =
      (List.map makeSource
        (units.product (units.product localizedRule3FourLigandPairings))).map
          (fun matching => matching.mapSpatialPoints mapPoint)
  calc
    _ = List.map makeMapped
          ((units.map mapUnit).product
            ((units.product localizedRule3FourLigandPairings).map mapInner)) := by
        rw [innerEq]
    _ = List.map makeMapped
          ((units.product (units.product localizedRule3FourLigandPairings)).map
            (fun candidate => (mapUnit candidate.1, mapInner candidate.2))) := by
        rw [outerEq]
    _ = _ := by
      simp only [List.map_map]
      rfl

@[simp] theorem localizedRule3CoupledPerfectMatchings_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3CoupledPerfectMatchings
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      (input.localizedRule3CoupledPerfectMatchings keys).map
        (fun matching => matching.mapSpatialPoints mapPoint) := by
  classical
  unfold localizedRule3CoupledPerfectMatchings
  rw [localizedRule3CoupledMatchingCandidates_mapSpatialPoints, List.filter_map]
  apply congrArg (fun predicate =>
    (input.localizedRule3CoupledMatchingCandidates keys).filter predicate |>
      List.map fun matching => matching.mapSpatialPoints mapPoint)
  funext matching
  simp only [Function.comp_apply]
  simp only [declarativeLocalizedRule3CoupledMatching_mapSpatialPoints]

@[simp] theorem localizedRule3CoupledTopologyResolution?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.mapSpatialPoints mapPoint).localizedRule3CoupledTopologyResolution?
        (keys.map fun key => key.mapSpatialPoints mapPoint) =
      (input.localizedRule3CoupledTopologyResolution? keys).map
        (fun resolution => resolution.mapSpatialPoints mapPoint) := by
  unfold localizedRule3CoupledTopologyResolution?
  rw [localizedRule3CoupledPerfectMatchings_mapSpatialPoints]
  cases matchingsEq : input.localizedRule3CoupledPerfectMatchings keys with
  | nil => rfl
  | cons matching rest =>
      cases rest <;> rfl

@[simp] theorem localizedRule3CoupledTopologyResolution_isCoupled_mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (resolution : input.LocalizedRule3CoupledTopologyResolution)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (resolution.mapSpatialPoints mapPoint).isCoupled = resolution.isCoupled := by
  cases resolution <;> rfl

@[simp] theorem localizedRule3CoupledExcludedPhysicalUnits_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (resolution : input.LocalizedRule3CoupledTopologyResolution) :
    (input.mapSpatialPoints mapPoint).localizedRule3CoupledExcludedPhysicalUnits
        (keys.map fun key => key.mapSpatialPoints mapPoint)
        (resolution.mapSpatialPoints mapPoint) =
      (input.localizedRule3CoupledExcludedPhysicalUnits keys resolution).map
        (fun unit => unit.mapSpatialPoints mapPoint) := by
  cases resolution with
  | ordinary =>
      exact localizedRule3SharedPhysicalUnits_mapSpatialPoints input mapPoint keys
  | coupled matching =>
      unfold localizedRule3CoupledExcludedPhysicalUnits
      simp only [LocalizedRule3CoupledTopologyResolution.mapSpatialPoints,
        LocalizedRule3CoupledMatching.mapSpatialPoints]
      rw [localizedRule3SharedPhysicalUnits_mapSpatialPoints, List.filter_map]
      apply congrArg (fun predicate =>
        (input.localizedRule3SharedPhysicalUnits keys).filter predicate |>
          List.map fun unit => unit.mapSpatialPoints mapPoint)
      funext unit
      simp only [Function.comp_apply]
      have injective :=
        LocalizedRule3PhysicalUnitId.mapSpatialPoints_injective input mapPoint
      simp [injective.eq_iff]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
