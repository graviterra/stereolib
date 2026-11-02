import TetraStereo.OneCenter.LocalizedRerootRule3PhysicalUnit

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exhaustive finite topology for coupled Rule-3 units

The earlier active path recognized only one hard-coded shape: four singleton ligand views and two
physical units occurring twice.  This module states the topology independently.  For four
constitutionally tied ligand keys, every physical-unit pair and all three perfect pairings of the
four ligand positions are enumerated.  A unit assigned to one pair must occur in exactly those two
ligand keys.  Other, nonmatching observations may coexist and can be handled separately by the
ordinary circular-unit exclusion policy.

The resolver distinguishes no matching, one canonical matching, and ambiguity.  Ambiguity is a
real refusal state; an implementation must not select one pairing by list order.
-/

namespace CertifiedLocalizedCIPInput

/-- The three perfect pairings of four ligand positions. -/
inductive LocalizedRule3FourLigandPairing where
  | pair01_23
  | pair02_13
  | pair03_12
  deriving DecidableEq, Repr

def localizedRule3FourLigandPairings : List LocalizedRule3FourLigandPairing :=
  [.pair01_23, .pair02_13, .pair03_12]

/-- One proposed pair of physical geometrical units and its four-ligand partition. -/
structure LocalizedRule3CoupledMatching
    (input : CertifiedLocalizedCIPInput) where
  pairing : LocalizedRule3FourLigandPairing
  firstUnit : input.LocalizedRule3PhysicalUnitId
  secondUnit : input.LocalizedRule3PhysicalUnitId
  deriving DecidableEq, Repr

/-- Canonical strict order on unordered physical-unit identities. -/
def LocalizedRule3PhysicalUnitId.LexLt
    {input : CertifiedLocalizedCIPInput}
    (left right : input.LocalizedRule3PhysicalUnitId) : Prop :=
  left.first.val < right.first.val ∨
    (left.first = right.first ∧ left.second.val < right.second.val)

/-- All physical Rule-3 identities observed in the four raw ligand keys. -/
def localizedRule3FramePhysicalUnits
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRule3PhysicalUnitId :=
  (keys.flatMap input.localizedRule3PhysicalUnitIds).eraseDups

/-- Exact branching-tree provenance of every unit considered by the exhaustive matching search. -/
theorem mem_localizedRule3FramePhysicalUnits_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3FramePhysicalUnits keys ↔
      ∃ key ∈ keys, ∃ layer ∈ key.observations, ∃ entry ∈ layer,
        entry.2.physicalUnitId = unit := by
  rw [localizedRule3FramePhysicalUnits,
    input.mem_eraseDups_localizedRule3PhysicalUnitId_iff]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨key, keyPresent, unitPresent⟩
    rcases (input.mem_localizedRule3PhysicalUnitIds_iff key unit).mp unitPresent with
      ⟨layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, keyPresent, layer, layerPresent, entry, entryPresent, identity⟩
  · rintro ⟨key, keyPresent, layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, keyPresent,
      (input.mem_localizedRule3PhysicalUnitIds_iff key unit).mpr
        ⟨layer, layerPresent, entry, entryPresent, identity⟩⟩

/-- The physical-unit universe searched by coupled topology is invariant under ligand order. -/
theorem mem_localizedRule3FramePhysicalUnits_iff_of_perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId)
    (permutation : left.Perm right) :
    unit ∈ input.localizedRule3FramePhysicalUnits left ↔
      unit ∈ input.localizedRule3FramePhysicalUnits right := by
  rw [input.mem_localizedRule3FramePhysicalUnits_iff,
    input.mem_localizedRule3FramePhysicalUnits_iff]
  constructor
  · rintro ⟨key, present, layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, permutation.mem_iff.mp present, layer, layerPresent,
      entry, entryPresent, identity⟩
  · rintro ⟨key, present, layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, permutation.mem_iff.mpr present, layer, layerPresent,
      entry, entryPresent, identity⟩

/-- The ordinary shared-unit cancellation domain is invariant under ligand order. -/
theorem mem_localizedRule3SharedPhysicalUnits_iff_of_perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId)
    (permutation : left.Perm right) :
    unit ∈ input.localizedRule3SharedPhysicalUnits left ↔
      unit ∈ input.localizedRule3SharedPhysicalUnits right := by
  rw [input.mem_localizedRule3SharedPhysicalUnits_iff,
    input.mem_localizedRule3SharedPhysicalUnits_iff]
  change
    (unit ∈ input.localizedRule3FramePhysicalUnits left ∧
        1 < input.localizedRule3PhysicalUnitKeyCount left unit) ↔
      unit ∈ input.localizedRule3FramePhysicalUnits right ∧
        1 < input.localizedRule3PhysicalUnitKeyCount right unit
  rw [input.mem_localizedRule3FramePhysicalUnits_iff_of_perm
        (left := left) (right := right) (unit := unit) permutation,
    input.localizedRule3PhysicalUnitKeyCount_eq_of_perm
        (left := left) (right := right) (unit := unit) permutation]

/-- Exact pairwise constitutional tie for four ligand keys.  Both directions are retained
explicitly, so the specification does not assume comparator symmetry. -/
def DeclarativeLocalizedRule3FourWayConstitutionalTie
    (input : CertifiedLocalizedCIPInput)
    (k0 k1 k2 k3 : input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  OfficialRuleMajorKey.compare k0.constitutional k0.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k0.constitutional k1.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k0.constitutional k2.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k0.constitutional k3.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k1.constitutional k0.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k1.constitutional k1.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k1.constitutional k2.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k1.constitutional k3.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k2.constitutional k0.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k2.constitutional k1.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k2.constitutional k2.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k2.constitutional k3.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k3.constitutional k0.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k3.constitutional k1.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k3.constitutional k2.constitutional = Ordering.eq ∧
  OfficialRuleMajorKey.compare k3.constitutional k3.constitutional = Ordering.eq

/-- One unit occurs in exactly the selected two ligand keys of a four-key frame. -/
def DeclarativeLocalizedRule3ExactPairIncidence
    (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedRule3PhysicalUnitId)
    (first second outsideFirst outsideSecond :
      input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  unit ∈ input.localizedRule3PhysicalUnitIds first ∧
    unit ∈ input.localizedRule3PhysicalUnitIds second ∧
    unit ∉ input.localizedRule3PhysicalUnitIds outsideFirst ∧
    unit ∉ input.localizedRule3PhysicalUnitIds outsideSecond

/-- Two physical units occupy complementary pairs.  Either unit may occupy the pair containing
ligand position zero; the canonical lexicographic ordering of unit identities must not constrain
their chemical incidence. -/
def DeclarativeLocalizedRule3ComplementaryPairIncidence
    (input : CertifiedLocalizedCIPInput)
    (firstUnit secondUnit : input.LocalizedRule3PhysicalUnitId)
    (pairFirst pairSecond complementFirst complementSecond :
      input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  (input.DeclarativeLocalizedRule3ExactPairIncidence
      firstUnit pairFirst pairSecond complementFirst complementSecond ∧
    input.DeclarativeLocalizedRule3ExactPairIncidence
      secondUnit complementFirst complementSecond pairFirst pairSecond) ∨
  (input.DeclarativeLocalizedRule3ExactPairIncidence
      secondUnit pairFirst pairSecond complementFirst complementSecond ∧
    input.DeclarativeLocalizedRule3ExactPairIncidence
      firstUnit complementFirst complementSecond pairFirst pairSecond)

/-- Independent meaning of a coupled perfect matching.  Extra observations are not discarded by
this relation; it specifies exactly the incidence of the two matched physical units. -/
def DeclarativeLocalizedRule3CoupledMatching
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching) : Prop :=
  matching.firstUnit ∈ input.localizedRule3FramePhysicalUnits keys ∧
    matching.secondUnit ∈ input.localizedRule3FramePhysicalUnits keys ∧
    matching.firstUnit.LexLt matching.secondUnit ∧
    match keys with
    | [k0, k1, k2, k3] =>
        input.DeclarativeLocalizedRule3FourWayConstitutionalTie k0 k1 k2 k3 ∧
        match matching.pairing with
        | .pair01_23 =>
            input.DeclarativeLocalizedRule3ComplementaryPairIncidence
              matching.firstUnit matching.secondUnit k0 k1 k2 k3
        | .pair02_13 =>
            input.DeclarativeLocalizedRule3ComplementaryPairIncidence
              matching.firstUnit matching.secondUnit k0 k2 k1 k3
        | .pair03_12 =>
            input.DeclarativeLocalizedRule3ComplementaryPairIncidence
              matching.firstUnit matching.secondUnit k0 k3 k1 k2
    | _ => False

/-- Position-free meaning of a complementary pair of coupled physical units.  It does not name a
ligand-number pairing: four constitutionally tied keys are partitioned by two distinct units,
each occurring in exactly two keys and exactly one of them occurring in every key. -/
def DeclarativeLocalizedRule3CoupledUnitPair
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstUnit secondUnit : input.LocalizedRule3PhysicalUnitId) : Prop :=
  firstUnit ∈ input.localizedRule3FramePhysicalUnits keys ∧
    secondUnit ∈ input.localizedRule3FramePhysicalUnits keys ∧
    firstUnit.LexLt secondUnit ∧
    keys.length = 4 ∧
    (∀ left ∈ keys, ∀ right ∈ keys,
      OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq) ∧
    input.localizedRule3PhysicalUnitKeyCount keys firstUnit = 2 ∧
    input.localizedRule3PhysicalUnitKeyCount keys secondUnit = 2 ∧
    ∀ key ∈ keys,
      (firstUnit ∈ input.localizedRule3PhysicalUnitIds key ↔
        secondUnit ∉ input.localizedRule3PhysicalUnitIds key)

namespace DeclarativeLocalizedRule3CoupledMatching

/-- Every position-indexed exact matching yields the position-free complementary-unit relation. -/
theorem implies_unit_pair
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching)
    (derived : input.DeclarativeLocalizedRule3CoupledMatching keys matching) :
    input.DeclarativeLocalizedRule3CoupledUnitPair keys
      matching.firstUnit matching.secondUnit := by
  rcases derived with ⟨firstPresent, secondPresent, ordered, shape⟩
  cases keys with
  | nil => simp at shape
  | cons k0 tail0 =>
      cases tail0 with
      | nil => simp at shape
      | cons k1 tail1 =>
          cases tail1 with
          | nil => simp at shape
          | cons k2 tail2 =>
              cases tail2 with
              | nil => simp at shape
              | cons k3 tail3 =>
                  cases tail3 with
                  | cons k4 rest => simp at shape
                  | nil =>
                      rcases shape with ⟨tied, incidence⟩
                      refine ⟨firstPresent, secondPresent, ordered, rfl, ?_, ?_⟩
                      · rcases tied with
                          ⟨h00, h01, h02, h03, h10, h11, h12, h13,
                            h20, h21, h22, h23, h30, h31, h32, h33⟩
                        intro left leftPresent right rightPresent
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at leftPresent rightPresent
                        rcases leftPresent with rfl | rfl | rfl | rfl <;>
                          rcases rightPresent with rfl | rfl | rfl | rfl <;>
                          assumption
                      · cases matching with
                        | mk pairing firstUnit secondUnit =>
                            cases pairing <;>
                              simp only [DeclarativeLocalizedRule3ComplementaryPairIncidence]
                                at incidence <;>
                              rcases incidence with orientation | orientation <;>
                              rcases orientation with ⟨firstIncidence, secondIncidence⟩ <;>
                              simp only [DeclarativeLocalizedRule3ExactPairIncidence]
                                at firstIncidence secondIncidence <;>
                              simp [localizedRule3PhysicalUnitKeyCount,
                                firstIncidence, secondIncidence]

/-- For fixed canonically ordered unit identities, exact complementary incidence determines the
position pairing uniquely. -/
theorem eq_of_unit_fields_eq
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (left right : input.LocalizedRule3CoupledMatching)
    (leftDerived : input.DeclarativeLocalizedRule3CoupledMatching keys left)
    (rightDerived : input.DeclarativeLocalizedRule3CoupledMatching keys right)
    (firstEq : left.firstUnit = right.firstUnit)
    (secondEq : left.secondUnit = right.secondUnit) :
    left = right := by
  cases left with
  | mk leftPairing firstUnit secondUnit =>
      cases right with
      | mk rightPairing otherFirst otherSecond =>
          simp only at firstEq secondEq
          subst otherFirst
          subst otherSecond
          cases keys with
          | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at leftDerived
          | cons k0 tail0 =>
              cases tail0 with
              | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at leftDerived
              | cons k1 tail1 =>
                  cases tail1 with
                  | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at leftDerived
                  | cons k2 tail2 =>
                      cases tail2 with
                      | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at leftDerived
                      | cons k3 tail3 =>
                          cases tail3 with
                          | cons k4 rest =>
                              simp [DeclarativeLocalizedRule3CoupledMatching] at leftDerived
                          | nil =>
                              cases leftPairing <;> cases rightPairing <;>
                                simp [DeclarativeLocalizedRule3CoupledMatching,
                                  DeclarativeLocalizedRule3ComplementaryPairIncidence,
                                  DeclarativeLocalizedRule3ExactPairIncidence] at leftDerived rightDerived ⊢ <;>
                                aesop

end DeclarativeLocalizedRule3CoupledMatching

namespace DeclarativeLocalizedRule3CoupledUnitPair

/-- Every position-free complementary unit pair induces one of the three position-indexed
pairings.  Both unit-to-pair orientations are already included in the matching relation. -/
theorem exists_matching
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstUnit secondUnit : input.LocalizedRule3PhysicalUnitId)
    (derived : input.DeclarativeLocalizedRule3CoupledUnitPair
      keys firstUnit secondUnit) :
    ∃ pairing,
      input.DeclarativeLocalizedRule3CoupledMatching keys
        { pairing, firstUnit, secondUnit } := by
  rcases derived with ⟨firstPresent, secondPresent, ordered, length,
    tied, firstCount, secondCount, complementary⟩
  cases keys with
  | nil => simp at length
  | cons k0 tail0 =>
      cases tail0 with
      | nil => simp at length
      | cons k1 tail1 =>
          cases tail1 with
          | nil => simp at length
          | cons k2 tail2 =>
              cases tail2 with
              | nil => simp at length
              | cons k3 tail3 =>
                  cases tail3 with
                  | cons k4 rest => simp at length
                  | nil =>
                      have tied4 :
                          input.DeclarativeLocalizedRule3FourWayConstitutionalTie
                            k0 k1 k2 k3 := by
                        unfold DeclarativeLocalizedRule3FourWayConstitutionalTie
                        exact ⟨
                          tied k0 (by simp) k0 (by simp),
                          tied k0 (by simp) k1 (by simp),
                          tied k0 (by simp) k2 (by simp),
                          tied k0 (by simp) k3 (by simp),
                          tied k1 (by simp) k0 (by simp),
                          tied k1 (by simp) k1 (by simp),
                          tied k1 (by simp) k2 (by simp),
                          tied k1 (by simp) k3 (by simp),
                          tied k2 (by simp) k0 (by simp),
                          tied k2 (by simp) k1 (by simp),
                          tied k2 (by simp) k2 (by simp),
                          tied k2 (by simp) k3 (by simp),
                          tied k3 (by simp) k0 (by simp),
                          tied k3 (by simp) k1 (by simp),
                          tied k3 (by simp) k2 (by simp),
                          tied k3 (by simp) k3 (by simp)⟩
                      have complement0 := complementary k0 (by simp)
                      have complement1 := complementary k1 (by simp)
                      have complement2 := complementary k2 (by simp)
                      have complement3 := complementary k3 (by simp)
                      by_cases first0 : firstUnit ∈ input.localizedRule3PhysicalUnitIds k0 <;>
                        by_cases first1 : firstUnit ∈ input.localizedRule3PhysicalUnitIds k1 <;>
                        by_cases first2 : firstUnit ∈ input.localizedRule3PhysicalUnitIds k2 <;>
                        by_cases first3 : firstUnit ∈ input.localizedRule3PhysicalUnitIds k3 <;>
                        simp [localizedRule3PhysicalUnitKeyCount, first0, first1,
                          first2, first3] at firstCount <;>
                        try omega
                      all_goals
                        let pairing : LocalizedRule3FourLigandPairing :=
                          if firstUnit ∈ input.localizedRule3PhysicalUnitIds k0 then
                            if firstUnit ∈ input.localizedRule3PhysicalUnitIds k1 then
                              .pair01_23
                            else if firstUnit ∈ input.localizedRule3PhysicalUnitIds k2 then
                              .pair02_13 else .pair03_12
                          else if firstUnit ∈ input.localizedRule3PhysicalUnitIds k1 then
                            if firstUnit ∈ input.localizedRule3PhysicalUnitIds k2 then
                              .pair03_12 else .pair02_13
                          else .pair01_23
                        exact ⟨pairing, by
                          simp_all [pairing, DeclarativeLocalizedRule3CoupledMatching,
                            DeclarativeLocalizedRule3ComplementaryPairIncidence,
                            DeclarativeLocalizedRule3ExactPairIncidence]⟩

/-- The position-free coupled-unit relation is invariant under any ligand-key permutation. -/
theorem perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (firstUnit secondUnit : input.LocalizedRule3PhysicalUnitId)
    (permutation : left.Perm right)
    (derived : input.DeclarativeLocalizedRule3CoupledUnitPair
      left firstUnit secondUnit) :
    input.DeclarativeLocalizedRule3CoupledUnitPair
      right firstUnit secondUnit := by
  rcases derived with ⟨firstPresent, secondPresent, ordered, length,
    tied, firstCount, secondCount, complementary⟩
  refine ⟨
    (input.mem_localizedRule3FramePhysicalUnits_iff_of_perm
      left right firstUnit permutation).mp firstPresent,
    (input.mem_localizedRule3FramePhysicalUnits_iff_of_perm
      left right secondUnit permutation).mp secondPresent,
    ordered, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← permutation.length_eq]
    exact length
  · intro leftKey leftPresent rightKey rightPresent
    exact tied leftKey (permutation.mem_iff.mpr leftPresent)
      rightKey (permutation.mem_iff.mpr rightPresent)
  · rw [← input.localizedRule3PhysicalUnitKeyCount_eq_of_perm
      left right firstUnit permutation]
    exact firstCount
  · rw [← input.localizedRule3PhysicalUnitKeyCount_eq_of_perm
      left right secondUnit permutation]
    exact secondCount
  · intro key present
    exact complementary key (permutation.mem_iff.mpr present)

end DeclarativeLocalizedRule3CoupledUnitPair

/-- A position-indexed matching exists exactly when a position-free coupled unit pair exists. -/
theorem exists_declarativeLocalizedRule3CoupledMatching_iff_unit_pair
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (∃ matching, input.DeclarativeLocalizedRule3CoupledMatching keys matching) ↔
      ∃ firstUnit secondUnit,
        input.DeclarativeLocalizedRule3CoupledUnitPair
          keys firstUnit secondUnit := by
  constructor
  · rintro ⟨matching, derived⟩
    exact ⟨matching.firstUnit, matching.secondUnit,
      DeclarativeLocalizedRule3CoupledMatching.implies_unit_pair
        input keys matching derived⟩
  · rintro ⟨firstUnit, secondUnit, derived⟩
    obtain ⟨pairing, matching⟩ :=
      DeclarativeLocalizedRule3CoupledUnitPair.exists_matching
        input keys firstUnit secondUnit derived
    exact ⟨{ pairing, firstUnit, secondUnit }, matching⟩

/-- Existence of coupled topology is invariant under ligand enumeration order. -/
theorem exists_declarativeLocalizedRule3CoupledMatching_iff_of_perm
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : left.Perm right) :
    (∃ matching, input.DeclarativeLocalizedRule3CoupledMatching left matching) ↔
      ∃ matching, input.DeclarativeLocalizedRule3CoupledMatching right matching := by
  rw [input.exists_declarativeLocalizedRule3CoupledMatching_iff_unit_pair,
    input.exists_declarativeLocalizedRule3CoupledMatching_iff_unit_pair]
  constructor
  · rintro ⟨firstUnit, secondUnit, derived⟩
    exact ⟨firstUnit, secondUnit,
      DeclarativeLocalizedRule3CoupledUnitPair.perm
        input left right firstUnit secondUnit permutation derived⟩
  · rintro ⟨firstUnit, secondUnit, derived⟩
    exact ⟨firstUnit, secondUnit,
      DeclarativeLocalizedRule3CoupledUnitPair.perm
        input right left firstUnit secondUnit permutation.symm derived⟩

/-- Finite Cartesian enumeration of every observed unit pair and every four-ligand pairing. -/
def localizedRule3CoupledMatchingCandidates
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRule3CoupledMatching :=
  let units := input.localizedRule3FramePhysicalUnits keys
  (units.product (units.product localizedRule3FourLigandPairings)).map fun candidate =>
    { pairing := candidate.2.2
      firstUnit := candidate.1
      secondUnit := candidate.2.1 }

/-- Cartesian candidate enumeration contains each pairing/unit record exactly once. -/
theorem localizedRule3CoupledMatchingCandidates_nodup
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.localizedRule3CoupledMatchingCandidates keys).Nodup := by
  unfold localizedRule3CoupledMatchingCandidates localizedRule3FramePhysicalUnits
  let units := (keys.flatMap input.localizedRule3PhysicalUnitIds).eraseDups
  have unitsNodup : units.Nodup :=
    input.eraseDups_localizedRule3PhysicalUnitId_nodup _
  have pairingsNodup : localizedRule3FourLigandPairings.Nodup := by
    simp [localizedRule3FourLigandPairings]
  apply (unitsNodup.product (unitsNodup.product pairingsNodup)).map
  rintro ⟨firstUnit, secondUnit, pairing⟩ ⟨otherFirst, otherSecond, otherPairing⟩
    equal
  simp only [LocalizedRule3CoupledMatching.mk.injEq] at equal
  simp_all

/-- Candidate enumeration contains precisely the records whose two unit fields occur in the raw
frame; the pairing field is exhaustive by cases. -/
theorem mem_localizedRule3CoupledMatchingCandidates_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching) :
    matching ∈ input.localizedRule3CoupledMatchingCandidates keys ↔
      matching.firstUnit ∈ input.localizedRule3FramePhysicalUnits keys ∧
        matching.secondUnit ∈ input.localizedRule3FramePhysicalUnits keys := by
  cases matching with
  | mk pairing firstUnit secondUnit =>
      cases pairing <;>
        simp [localizedRule3CoupledMatchingCandidates,
          localizedRule3FourLigandPairings]

/-- Every independently valid matching is present in the finite candidate enumeration. -/
theorem mem_localizedRule3CoupledMatchingCandidates_of_declarative
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching)
    (derived : input.DeclarativeLocalizedRule3CoupledMatching keys matching) :
    matching ∈ input.localizedRule3CoupledMatchingCandidates keys :=
  (input.mem_localizedRule3CoupledMatchingCandidates_iff keys matching).mpr
    ⟨derived.1, derived.2.1⟩

/-- Exhaustive executable list of independently valid coupled matchings. -/
noncomputable def localizedRule3CoupledPerfectMatchings
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRule3CoupledMatching := by
  classical
  exact (input.localizedRule3CoupledMatchingCandidates keys).filter fun matching =>
    decide (input.DeclarativeLocalizedRule3CoupledMatching keys matching)

/-- Filtering the duplicate-free candidate product preserves duplicate freedom. -/
theorem localizedRule3CoupledPerfectMatchings_nodup
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.localizedRule3CoupledPerfectMatchings keys).Nodup := by
  classical
  unfold localizedRule3CoupledPerfectMatchings
  exact (input.localizedRule3CoupledMatchingCandidates_nodup keys).filter _

/-- Executable membership is exactly the independent coupled-matching relation. -/
theorem mem_localizedRule3CoupledPerfectMatchings_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching) :
    matching ∈ input.localizedRule3CoupledPerfectMatchings keys ↔
      input.DeclarativeLocalizedRule3CoupledMatching keys matching := by
  classical
  unfold localizedRule3CoupledPerfectMatchings
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · exact fun derived => derived.2
  · intro derived
    exact ⟨input.mem_localizedRule3CoupledMatchingCandidates_of_declarative
      keys matching derived, derived⟩

/-- A coupled matching is intrinsically a four-ligand phenomenon.  Frames of every other
cardinality have no valid matching candidates, independently of the observations stored in their
keys. -/
theorem localizedRule3CoupledPerfectMatchings_eq_nil_of_length_ne_four
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (length : keys.length ≠ 4) :
    input.localizedRule3CoupledPerfectMatchings keys = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro matching present
  have derived :=
    (input.mem_localizedRule3CoupledPerfectMatchings_iff keys matching).mp present
  have unitPair :=
    DeclarativeLocalizedRule3CoupledMatching.implies_unit_pair
      input keys matching derived
  exact length unitPair.2.2.2.1

/-- Resolved topology distinguishes ordinary cancellation from one unique coupled matching. -/
inductive LocalizedRule3CoupledTopologyResolution
    (input : CertifiedLocalizedCIPInput) where
  | ordinary
  | coupled (matching : input.LocalizedRule3CoupledMatching)
  deriving DecidableEq, Repr

/-- Whether a resolved topology carries a unique coupled matching. -/
def LocalizedRule3CoupledTopologyResolution.isCoupled
    {input : CertifiedLocalizedCIPInput} :
    input.LocalizedRule3CoupledTopologyResolution → Bool
  | .ordinary => false
  | .coupled _ => true

/-- Circular-unit cancellation induced by a resolved exhaustive topology.  In the ordinary case
every shared unit is cancelled.  In the uniquely coupled case exactly the two matched units are
retained and every other shared unit is cancelled. -/
def localizedRule3CoupledExcludedPhysicalUnits
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.LocalizedRule3CoupledTopologyResolution →
      List input.LocalizedRule3PhysicalUnitId
  | .ordinary => input.localizedRule3SharedPhysicalUnits keys
  | .coupled matching =>
      (input.localizedRule3SharedPhysicalUnits keys).filter fun unit =>
        decide (unit ≠ matching.firstUnit ∧ unit ≠ matching.secondUnit)

@[simp] theorem mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits keys .ordinary ↔
      unit ∈ input.localizedRule3SharedPhysicalUnits keys := by
  rfl

@[simp] theorem mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits keys (.coupled matching) ↔
      unit ∈ input.localizedRule3SharedPhysicalUnits keys ∧
        unit ≠ matching.firstUnit ∧ unit ≠ matching.secondUnit := by
  simp [localizedRule3CoupledExcludedPhysicalUnits]

/-- The first unit of a uniquely selected coupled matching is retained by the rebuild. -/
theorem localizedRule3CoupledExcludedPhysicalUnits_retains_first
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching) :
    matching.firstUnit ∉
      input.localizedRule3CoupledExcludedPhysicalUnits keys (.coupled matching) := by
  simp

/-- The second unit of a uniquely selected coupled matching is retained by the rebuild. -/
theorem localizedRule3CoupledExcludedPhysicalUnits_retains_second
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching) :
    matching.secondUnit ∉
      input.localizedRule3CoupledExcludedPhysicalUnits keys (.coupled matching) := by
  simp

/-- Once the same canonical unit pair is transported to a permuted ligand frame, its cancellation
set has exactly the same physical-unit membership. -/
theorem mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff_of_perm
    (input : CertifiedLocalizedCIPInput)
    (leftKeys rightKeys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (leftMatching rightMatching : input.LocalizedRule3CoupledMatching)
    (unit : input.LocalizedRule3PhysicalUnitId)
    (permutation : leftKeys.Perm rightKeys)
    (firstEq : leftMatching.firstUnit = rightMatching.firstUnit)
    (secondEq : leftMatching.secondUnit = rightMatching.secondUnit) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits
        leftKeys (.coupled leftMatching) ↔
      unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits
        rightKeys (.coupled rightMatching) := by
  rw [input.mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff,
    input.mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff,
    input.mem_localizedRule3SharedPhysicalUnits_iff_of_perm
      leftKeys rightKeys unit permutation,
    firstEq, secondEq]

/-- Independent frame policy associated with a resolved topology.  It exposes the retained pair
instead of reducing coupled topology to a Boolean before cancellation is chosen. -/
inductive DeclarativeLocalizedRule3CoupledFramePolicy
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.LocalizedRule3CoupledTopologyResolution → Bool →
      List input.LocalizedRule3PhysicalUnitId → Prop
  | ordinary :
      input.DeclarativeLocalizedRule3CoupledFramePolicy keys .ordinary false
        (input.localizedRule3SharedPhysicalUnits keys)
  | coupled (matching : input.LocalizedRule3CoupledMatching) :
      input.DeclarativeLocalizedRule3CoupledFramePolicy keys (.coupled matching) true
        ((input.localizedRule3SharedPhysicalUnits keys).filter fun unit =>
          decide (unit ≠ matching.firstUnit ∧ unit ≠ matching.secondUnit))

/-- The executable projection from a resolved topology satisfies the explicit frame policy. -/
theorem localizedRule3CoupledFramePolicy_sound
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (resolution : input.LocalizedRule3CoupledTopologyResolution) :
    input.DeclarativeLocalizedRule3CoupledFramePolicy keys resolution
      resolution.isCoupled
      (input.localizedRule3CoupledExcludedPhysicalUnits keys resolution) := by
  cases resolution with
  | ordinary => exact DeclarativeLocalizedRule3CoupledFramePolicy.ordinary
  | coupled matching =>
      exact DeclarativeLocalizedRule3CoupledFramePolicy.coupled matching

/-- Refuse when more than one coupled matching is independently valid. -/
noncomputable def localizedRule3CoupledTopologyResolution?
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    Option input.LocalizedRule3CoupledTopologyResolution :=
  match input.localizedRule3CoupledPerfectMatchings keys with
  | [] => some .ordinary
  | [matching] => some (.coupled matching)
  | _ => none

/-- Every non-four-key frame resolves automatically to ordinary shared-unit cancellation; it can
never enter the coupled ambiguity state. -/
theorem localizedRule3CoupledTopologyResolution?_eq_ordinary_of_length_ne_four
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (length : keys.length ≠ 4) :
    input.localizedRule3CoupledTopologyResolution? keys = some .ordinary := by
  simp [localizedRule3CoupledTopologyResolution?,
    input.localizedRule3CoupledPerfectMatchings_eq_nil_of_length_ne_four keys length]

/-- Independent exact positive meaning of the topology resolver. -/
inductive DeclarativeLocalizedRule3CoupledTopologyResolution
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.LocalizedRule3CoupledTopologyResolution → Prop
  | ordinary
      (none : input.localizedRule3CoupledPerfectMatchings keys = []) :
      input.DeclarativeLocalizedRule3CoupledTopologyResolution keys .ordinary
  | coupled {matching}
      (unique : input.localizedRule3CoupledPerfectMatchings keys = [matching]) :
      input.DeclarativeLocalizedRule3CoupledTopologyResolution keys (.coupled matching)

/-- Successful resolution is exactly absence or uniqueness of the exhaustive matching list. -/
theorem localizedRule3CoupledTopologyResolution?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (resolution : input.LocalizedRule3CoupledTopologyResolution) :
    input.localizedRule3CoupledTopologyResolution? keys = some resolution ↔
      input.DeclarativeLocalizedRule3CoupledTopologyResolution keys resolution := by
  constructor
  · intro computed
    unfold localizedRule3CoupledTopologyResolution? at computed
    cases matchingsIdentity : input.localizedRule3CoupledPerfectMatchings keys with
    | nil =>
        simp [matchingsIdentity] at computed
        subst resolution
        exact DeclarativeLocalizedRule3CoupledTopologyResolution.ordinary
          matchingsIdentity
    | cons matching rest =>
        cases rest with
        | nil =>
            simp [matchingsIdentity] at computed
            subst resolution
            exact DeclarativeLocalizedRule3CoupledTopologyResolution.coupled
              matchingsIdentity
        | cons second more => simp [matchingsIdentity] at computed
  · intro derived
    cases derived with
    | ordinary none => simp [localizedRule3CoupledTopologyResolution?, none]
    | coupled unique => simp [localizedRule3CoupledTopologyResolution?, unique]

/-- Refusal means exactly that at least two distinct candidate records survived the independent
matching relation. -/
theorem localizedRule3CoupledTopologyResolution?_eq_none_iff_ambiguous
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.localizedRule3CoupledTopologyResolution? keys = none ↔
      ∃ first second rest,
        input.localizedRule3CoupledPerfectMatchings keys = first :: second :: rest := by
  unfold localizedRule3CoupledTopologyResolution?
  cases matchingsIdentity : input.localizedRule3CoupledPerfectMatchings keys with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second more =>
          constructor
          · intro _
            exact ⟨first, second, more, rfl⟩
          · intro _
            rfl

/-- Refusal is exactly the presence of two valid matchings with different physical-unit pairs;
duplicate candidate enumeration cannot manufacture ambiguity. -/
theorem localizedRule3CoupledTopologyResolution?_eq_none_iff_distinct_unit_pairs
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.localizedRule3CoupledTopologyResolution? keys = none ↔
      ∃ left right,
        left ∈ input.localizedRule3CoupledPerfectMatchings keys ∧
        right ∈ input.localizedRule3CoupledPerfectMatchings keys ∧
        (left.firstUnit ≠ right.firstUnit ∨
          left.secondUnit ≠ right.secondUnit) := by
  constructor
  · intro refused
    obtain ⟨left, right, rest, matchings⟩ :=
      (input.localizedRule3CoupledTopologyResolution?_eq_none_iff_ambiguous
        keys).mp refused
    have nodup := input.localizedRule3CoupledPerfectMatchings_nodup keys
    rw [matchings] at nodup
    have different : left ≠ right := by
      intro equal
      exact (List.nodup_cons.mp nodup).1 (by simp [equal])
    have leftPresent : left ∈ input.localizedRule3CoupledPerfectMatchings keys := by
      rw [matchings]
      simp
    have rightPresent : right ∈ input.localizedRule3CoupledPerfectMatchings keys := by
      rw [matchings]
      simp
    refine ⟨left, right, leftPresent, rightPresent, ?_⟩
    by_contra sameFields
    push_neg at sameFields
    exact different
      (DeclarativeLocalizedRule3CoupledMatching.eq_of_unit_fields_eq
        input keys left right
        ((input.mem_localizedRule3CoupledPerfectMatchings_iff keys left).mp
          leftPresent)
        ((input.mem_localizedRule3CoupledPerfectMatchings_iff keys right).mp
          rightPresent)
        sameFields.1 sameFields.2)
  · rintro ⟨left, right, leftPresent, rightPresent, differentFields⟩
    apply (input.localizedRule3CoupledTopologyResolution?_eq_none_iff_ambiguous
      keys).mpr
    cases matchingsIdentity : input.localizedRule3CoupledPerfectMatchings keys with
    | nil => simp [matchingsIdentity] at leftPresent
    | cons first rest =>
        cases rest with
        | nil =>
            simp [matchingsIdentity] at leftPresent rightPresent
            subst left
            subst right
            exact (differentFields.elim (fun false => false rfl)
              (fun false => false rfl)).elim
        | cons second more => exact ⟨first, second, more, rfl⟩

/-- Whether exhaustive coupled topology is ambiguous is invariant under ligand-key order. -/
theorem localizedRule3CoupledTopologyResolution?_eq_none_iff_of_perm
    (input : CertifiedLocalizedCIPInput)
    (leftKeys rightKeys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (permutation : leftKeys.Perm rightKeys) :
    input.localizedRule3CoupledTopologyResolution? leftKeys = none ↔
      input.localizedRule3CoupledTopologyResolution? rightKeys = none := by
  rw [input.localizedRule3CoupledTopologyResolution?_eq_none_iff_distinct_unit_pairs,
    input.localizedRule3CoupledTopologyResolution?_eq_none_iff_distinct_unit_pairs]
  have transport : ∀
      (source target : List input.LocalizedRerootRecursiveRule3SpatialKey),
      source.Perm target →
      (∃ left right,
        left ∈ input.localizedRule3CoupledPerfectMatchings source ∧
        right ∈ input.localizedRule3CoupledPerfectMatchings source ∧
        (left.firstUnit ≠ right.firstUnit ∨
          left.secondUnit ≠ right.secondUnit)) →
      ∃ left right,
        left ∈ input.localizedRule3CoupledPerfectMatchings target ∧
        right ∈ input.localizedRule3CoupledPerfectMatchings target ∧
        (left.firstUnit ≠ right.firstUnit ∨
          left.secondUnit ≠ right.secondUnit) := by
    intro source target perm
    rintro ⟨left, right, leftPresent, rightPresent, different⟩
    have leftPair :=
      DeclarativeLocalizedRule3CoupledMatching.implies_unit_pair input source left
        ((input.mem_localizedRule3CoupledPerfectMatchings_iff source left).mp
          leftPresent)
    have rightPair :=
      DeclarativeLocalizedRule3CoupledMatching.implies_unit_pair input source right
        ((input.mem_localizedRule3CoupledPerfectMatchings_iff source right).mp
          rightPresent)
    obtain ⟨leftPairing, leftDerived⟩ :=
      DeclarativeLocalizedRule3CoupledUnitPair.exists_matching input target
        left.firstUnit left.secondUnit
        (DeclarativeLocalizedRule3CoupledUnitPair.perm input source target
          left.firstUnit left.secondUnit perm leftPair)
    obtain ⟨rightPairing, rightDerived⟩ :=
      DeclarativeLocalizedRule3CoupledUnitPair.exists_matching input target
        right.firstUnit right.secondUnit
        (DeclarativeLocalizedRule3CoupledUnitPair.perm input source target
          right.firstUnit right.secondUnit perm rightPair)
    let left' : input.LocalizedRule3CoupledMatching :=
      { pairing := leftPairing, firstUnit := left.firstUnit,
        secondUnit := left.secondUnit }
    let right' : input.LocalizedRule3CoupledMatching :=
      { pairing := rightPairing, firstUnit := right.firstUnit,
        secondUnit := right.secondUnit }
    exact ⟨left', right',
      (input.mem_localizedRule3CoupledPerfectMatchings_iff target left').mpr
        leftDerived,
      (input.mem_localizedRule3CoupledPerfectMatchings_iff target right').mpr
        rightDerived,
      by simpa [left', right'] using different⟩
  exact ⟨transport leftKeys rightKeys permutation,
    transport rightKeys leftKeys permutation.symm⟩

namespace DeclarativeLocalizedRule3CoupledTopologyResolution

/-- A uniquely resolved coupled topology carries an independently valid exhaustive matching. -/
theorem coupled_matching
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching)
    (derived : input.DeclarativeLocalizedRule3CoupledTopologyResolution
      keys (.coupled matching)) :
    input.DeclarativeLocalizedRule3CoupledMatching keys matching := by
  cases derived with
  | coupled unique =>
      apply (input.mem_localizedRule3CoupledPerfectMatchings_iff keys matching).mp
      rw [unique]
      simp

end DeclarativeLocalizedRule3CoupledTopologyResolution

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
