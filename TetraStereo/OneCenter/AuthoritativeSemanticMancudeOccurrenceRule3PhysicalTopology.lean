import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3SpatialKey

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exhaustive source-canonical physical topology for Rule 3

The same physical geometrical unit can occur in multiple ring-opened ligand trees.  This module
gives units traversal-independent identities and replaces a shape heuristic by a finite exhaustive
search over every ordered pair of observed units.  The independent coupled relation says exactly:
four constitutional ligands tie, each of two distinct units occurs in exactly two ligand keys, and
each key contains exactly one of the units.  This position-free condition covers all three perfect
pairings of four ligand positions without privileging an input order.

No match means ordinary circular cancellation.  Exactly one match retains its two coupled units
and cancels all other shared units.  More than one match is an explicit ambiguity/refusal.
-/

/-- Traversal-independent unordered identity of one physical ordinary double bond. -/
structure AromaticCanonicalRule3PhysicalUnitId
    (source : AuthoritativeChemicalInput) where
  first : source.AromaticCanonicalAtom
  second : source.AromaticCanonicalAtom
  deriving DecidableEq, Repr

def aromaticCanonicalRule3PhysicalUnitId
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalRule3PhysicalUnitId :=
  if left ≤ right then { first := left, second := right }
  else { first := right, second := left }

theorem aromaticCanonicalRule3PhysicalUnitId_swap
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3PhysicalUnitId left right =
      source.aromaticCanonicalRule3PhysicalUnitId right left := by
  unfold aromaticCanonicalRule3PhysicalUnitId
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

theorem aromaticCanonicalRule3PhysicalUnitId_eq_iff
    (source : AuthoritativeChemicalInput)
    (left right otherLeft otherRight : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3PhysicalUnitId left right =
        source.aromaticCanonicalRule3PhysicalUnitId otherLeft otherRight ↔
      (left = otherLeft ∧ right = otherRight) ∨
        (left = otherRight ∧ right = otherLeft) := by
  constructor
  · intro equal
    unfold aromaticCanonicalRule3PhysicalUnitId at equal
    by_cases firstForward : left ≤ right
    · rw [if_pos firstForward] at equal
      by_cases secondForward : otherLeft ≤ otherRight
      · rw [if_pos secondForward] at equal
        exact Or.inl
          ⟨congrArg AromaticCanonicalRule3PhysicalUnitId.first equal,
            congrArg AromaticCanonicalRule3PhysicalUnitId.second equal⟩
      · rw [if_neg secondForward] at equal
        exact Or.inr
          ⟨congrArg AromaticCanonicalRule3PhysicalUnitId.first equal,
            congrArg AromaticCanonicalRule3PhysicalUnitId.second equal⟩
    · rw [if_neg firstForward] at equal
      by_cases secondForward : otherLeft ≤ otherRight
      · rw [if_pos secondForward] at equal
        exact Or.inr
          ⟨congrArg AromaticCanonicalRule3PhysicalUnitId.second equal,
            congrArg AromaticCanonicalRule3PhysicalUnitId.first equal⟩
      · rw [if_neg secondForward] at equal
        exact Or.inl
          ⟨congrArg AromaticCanonicalRule3PhysicalUnitId.second equal,
            congrArg AromaticCanonicalRule3PhysicalUnitId.first equal⟩
  · rintro (⟨rfl, rfl⟩ | ⟨leftEq, rightEq⟩)
    · rfl
    · subst otherRight
      subst otherLeft
      exact source.aromaticCanonicalRule3PhysicalUnitId_swap left right

def AromaticCanonicalRule3SpatialNodeResult.physicalUnitId
    {source : AuthoritativeChemicalInput}
    (result : source.AromaticCanonicalRule3SpatialNodeResult) :
    source.AromaticCanonicalRule3PhysicalUnitId :=
  source.aromaticCanonicalRule3PhysicalUnitId result.left result.right

/-- Distinct physical identities visible at every observation depth of one ligand key. -/
def aromaticCanonicalRule3PhysicalUnitIds
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalRule3PhysicalUnitId :=
  (key.observations.flatten.map fun entry => entry.2.physicalUnitId).eraseDups

private theorem mem_eraseDups_iff_for_aromaticCanonicalRule3PhysicalUnits
    {α : Type*} [BEq α] [LawfulBEq α]
    (a : α) (values : List α) : a ∈ values.eraseDups ↔ a ∈ values := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      by_cases same : a = head
      · subst head
        simp
      · have filtered := mem_eraseDups_iff_for_aromaticCanonicalRule3PhysicalUnits
          a (tail.filter fun b => !b == head)
        simpa [same] using filtered
termination_by values.length
decreasing_by
  have filtered := List.length_filter_le (fun b => !b == head) tail
  simpa using Nat.lt_succ_of_le filtered

private theorem eraseDups_nodup_for_aromaticCanonicalRule3PhysicalUnits
    {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ values : List α, values.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [mem_eraseDups_iff_for_aromaticCanonicalRule3PhysicalUnits]
        simp
      · exact eraseDups_nodup_for_aromaticCanonicalRule3PhysicalUnits
          (tail.filter fun value => !value == head)
termination_by values => values.length
decreasing_by
  have filtered := List.length_filter_le (fun value => !value == head) tail
  simpa using Nat.lt_succ_of_le filtered

theorem mem_aromaticCanonicalRule3PhysicalUnitIds_iff
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId) :
    unit ∈ source.aromaticCanonicalRule3PhysicalUnitIds key ↔
      ∃ layer ∈ key.observations, ∃ entry ∈ layer,
        entry.2.physicalUnitId = unit := by
  rw [aromaticCanonicalRule3PhysicalUnitIds,
    mem_eraseDups_iff_for_aromaticCanonicalRule3PhysicalUnits]
  simp

theorem aromaticCanonicalRule3PhysicalUnitIds_nodup
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    (source.aromaticCanonicalRule3PhysicalUnitIds key).Nodup := by
  exact eraseDups_nodup_for_aromaticCanonicalRule3PhysicalUnits _

/-- Number of distinct ligand keys containing one physical unit. -/
def aromaticCanonicalRule3PhysicalUnitKeyCount
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId) : Nat :=
  (keys.filter fun key =>
    (source.aromaticCanonicalRule3PhysicalUnitIds key).contains unit).length

theorem aromaticCanonicalRule3PhysicalUnitKeyCount_eq_of_perm
    (source : AuthoritativeChemicalInput)
    (left right : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId)
    (permutation : left.Perm right) :
    source.aromaticCanonicalRule3PhysicalUnitKeyCount left unit =
      source.aromaticCanonicalRule3PhysicalUnitKeyCount right unit := by
  unfold aromaticCanonicalRule3PhysicalUnitKeyCount
  exact (permutation.filter fun key =>
    (source.aromaticCanonicalRule3PhysicalUnitIds key).contains unit).length_eq

/-- Complete finite unit universe of the supplied ligand-key frame. -/
def aromaticCanonicalRule3FramePhysicalUnits
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalRule3PhysicalUnitId :=
  (keys.flatMap source.aromaticCanonicalRule3PhysicalUnitIds).eraseDups

theorem mem_aromaticCanonicalRule3FramePhysicalUnits_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId) :
    unit ∈ source.aromaticCanonicalRule3FramePhysicalUnits keys ↔
      ∃ key ∈ keys, ∃ layer ∈ key.observations, ∃ entry ∈ layer,
        entry.2.physicalUnitId = unit := by
  rw [aromaticCanonicalRule3FramePhysicalUnits,
    mem_eraseDups_iff_for_aromaticCanonicalRule3PhysicalUnits]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨key, keyPresent, unitPresent⟩
    rcases (source.mem_aromaticCanonicalRule3PhysicalUnitIds_iff key unit).mp
      unitPresent with ⟨layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, keyPresent, layer, layerPresent, entry, entryPresent, identity⟩
  · rintro ⟨key, keyPresent, layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, keyPresent,
      (source.mem_aromaticCanonicalRule3PhysicalUnitIds_iff key unit).mpr
        ⟨layer, layerPresent, entry, entryPresent, identity⟩⟩

theorem mem_aromaticCanonicalRule3FramePhysicalUnits_iff_of_perm
    (source : AuthoritativeChemicalInput)
    (left right : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId)
    (permutation : left.Perm right) :
    unit ∈ source.aromaticCanonicalRule3FramePhysicalUnits left ↔
      unit ∈ source.aromaticCanonicalRule3FramePhysicalUnits right := by
  rw [source.mem_aromaticCanonicalRule3FramePhysicalUnits_iff,
    source.mem_aromaticCanonicalRule3FramePhysicalUnits_iff]
  constructor
  · rintro ⟨key, keyPresent, layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, permutation.mem_iff.mp keyPresent,
      layer, layerPresent, entry, entryPresent, identity⟩
  · rintro ⟨key, keyPresent, layer, layerPresent, entry, entryPresent, identity⟩
    exact ⟨key, permutation.mem_iff.mpr keyPresent,
      layer, layerPresent, entry, entryPresent, identity⟩

/-- Units occurring in at least two distinct ligand keys are the ordinary circular-cancellation
domain. -/
def aromaticCanonicalRule3SharedPhysicalUnits
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalRule3PhysicalUnitId :=
  (source.aromaticCanonicalRule3FramePhysicalUnits keys).filter fun unit =>
    decide (1 < source.aromaticCanonicalRule3PhysicalUnitKeyCount keys unit)

theorem mem_aromaticCanonicalRule3SharedPhysicalUnits_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId) :
    unit ∈ source.aromaticCanonicalRule3SharedPhysicalUnits keys ↔
      unit ∈ source.aromaticCanonicalRule3FramePhysicalUnits keys ∧
        1 < source.aromaticCanonicalRule3PhysicalUnitKeyCount keys unit := by
  simp [aromaticCanonicalRule3SharedPhysicalUnits]

theorem mem_aromaticCanonicalRule3SharedPhysicalUnits_iff_of_perm
    (source : AuthoritativeChemicalInput)
    (left right : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId)
    (permutation : left.Perm right) :
    unit ∈ source.aromaticCanonicalRule3SharedPhysicalUnits left ↔
      unit ∈ source.aromaticCanonicalRule3SharedPhysicalUnits right := by
  rw [source.mem_aromaticCanonicalRule3SharedPhysicalUnits_iff,
    source.mem_aromaticCanonicalRule3SharedPhysicalUnits_iff,
    source.mem_aromaticCanonicalRule3FramePhysicalUnits_iff_of_perm
      left right unit permutation,
    source.aromaticCanonicalRule3PhysicalUnitKeyCount_eq_of_perm
      left right unit permutation]

/-- Canonical strict order used only to remove the swapped duplicate of a unit pair. -/
def AromaticCanonicalRule3PhysicalUnitId.LexLt
    {source : AuthoritativeChemicalInput}
    (left right : source.AromaticCanonicalRule3PhysicalUnitId) : Prop :=
  left.first.val < right.first.val ∨
    (left.first = right.first ∧ left.second.val < right.second.val)

/-- A canonically ordered proposed coupled-unit pair. -/
structure AromaticCanonicalRule3CoupledUnitPair
    (source : AuthoritativeChemicalInput) where
  firstUnit : source.AromaticCanonicalRule3PhysicalUnitId
  secondUnit : source.AromaticCanonicalRule3PhysicalUnitId
  deriving DecidableEq, Repr

/-- Independent, position-free coupled topology. -/
def DeclarativeAromaticCanonicalRule3CoupledUnitPair
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair) : Prop :=
  pair.firstUnit ∈ source.aromaticCanonicalRule3FramePhysicalUnits keys ∧
    pair.secondUnit ∈ source.aromaticCanonicalRule3FramePhysicalUnits keys ∧
    pair.firstUnit.LexLt pair.secondUnit ∧
    keys.length = 4 ∧
    (∀ left ∈ keys, ∀ right ∈ keys,
      ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph
        left.constitutional right.constitutional = Ordering.eq) ∧
    source.aromaticCanonicalRule3PhysicalUnitKeyCount keys pair.firstUnit = 2 ∧
    source.aromaticCanonicalRule3PhysicalUnitKeyCount keys pair.secondUnit = 2 ∧
    ∀ key ∈ keys,
      (pair.firstUnit ∈ source.aromaticCanonicalRule3PhysicalUnitIds key ↔
        pair.secondUnit ∉ source.aromaticCanonicalRule3PhysicalUnitIds key)

private theorem DeclarativeAromaticCanonicalRule3CoupledUnitPair.of_perm
    (source : AuthoritativeChemicalInput)
    (left right : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair)
    (permutation : left.Perm right)
    (derived : source.DeclarativeAromaticCanonicalRule3CoupledUnitPair left pair) :
    source.DeclarativeAromaticCanonicalRule3CoupledUnitPair right pair := by
  rcases derived with
    ⟨firstPresent, secondPresent, ordered, length, tied,
      firstCount, secondCount, complementary⟩
  refine ⟨
    (source.mem_aromaticCanonicalRule3FramePhysicalUnits_iff_of_perm
      left right pair.firstUnit permutation).mp firstPresent,
    (source.mem_aromaticCanonicalRule3FramePhysicalUnits_iff_of_perm
      left right pair.secondUnit permutation).mp secondPresent,
    ordered, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← permutation.length_eq]
    exact length
  · intro first firstInRight second secondInRight
    exact tied first (permutation.mem_iff.mpr firstInRight)
      second (permutation.mem_iff.mpr secondInRight)
  · rw [← source.aromaticCanonicalRule3PhysicalUnitKeyCount_eq_of_perm
      left right pair.firstUnit permutation]
    exact firstCount
  · rw [← source.aromaticCanonicalRule3PhysicalUnitKeyCount_eq_of_perm
      left right pair.secondUnit permutation]
    exact secondCount
  · intro key keyInRight
    exact complementary key (permutation.mem_iff.mpr keyInRight)

/-- Coupled incidence is independent of ligand enumeration order. -/
theorem declarativeAromaticCanonicalRule3CoupledUnitPair_iff_of_perm
    (source : AuthoritativeChemicalInput)
    (left right : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair)
    (permutation : left.Perm right) :
    source.DeclarativeAromaticCanonicalRule3CoupledUnitPair left pair ↔
      source.DeclarativeAromaticCanonicalRule3CoupledUnitPair right pair := by
  exact ⟨fun derived =>
    DeclarativeAromaticCanonicalRule3CoupledUnitPair.of_perm
      source left right pair permutation derived,
    fun derived =>
      DeclarativeAromaticCanonicalRule3CoupledUnitPair.of_perm
        source right left pair permutation.symm derived⟩

/-- Every ordered pair from the exhaustive observed-unit universe. -/
def aromaticCanonicalRule3CoupledUnitPairCandidates
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalRule3CoupledUnitPair :=
  (source.aromaticCanonicalRule3FramePhysicalUnits keys).flatMap fun first =>
    (source.aromaticCanonicalRule3FramePhysicalUnits keys).map fun second =>
      { firstUnit := first, secondUnit := second }

theorem mem_aromaticCanonicalRule3CoupledUnitPairCandidates_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair) :
    pair ∈ source.aromaticCanonicalRule3CoupledUnitPairCandidates keys ↔
      pair.firstUnit ∈ source.aromaticCanonicalRule3FramePhysicalUnits keys ∧
        pair.secondUnit ∈ source.aromaticCanonicalRule3FramePhysicalUnits keys := by
  simp [aromaticCanonicalRule3CoupledUnitPairCandidates]
  constructor
  · rintro ⟨first, firstPresent, second, secondPresent, identity⟩
    cases identity
    exact ⟨firstPresent, secondPresent⟩
  · intro present
    exact ⟨pair.firstUnit, present.1, pair.secondUnit, present.2, rfl⟩

/-- Exhaustive finite search for every coupled unit pair satisfying the independent relation. -/
noncomputable def aromaticCanonicalRule3CoupledUnitPairs
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalRule3CoupledUnitPair := by
  classical
  exact (source.aromaticCanonicalRule3CoupledUnitPairCandidates keys).filter fun pair =>
    decide (source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair)

/-- The coupled search has no finite topology gap: membership is exactly the independent
four-ligand complementary-incidence relation. -/
theorem mem_aromaticCanonicalRule3CoupledUnitPairs_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair) :
    pair ∈ source.aromaticCanonicalRule3CoupledUnitPairs keys ↔
      source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair := by
  classical
  rw [aromaticCanonicalRule3CoupledUnitPairs, List.mem_filter,
    decide_eq_true_eq, source.mem_aromaticCanonicalRule3CoupledUnitPairCandidates_iff]
  constructor
  · exact And.right
  · intro derived
    exact ⟨⟨derived.1, derived.2.1⟩, derived⟩

/-- Unambiguous finite topology outcomes.  Ambiguity is represented by `none` below. -/
inductive AromaticCanonicalRule3PhysicalTopologyResolution
    (source : AuthoritativeChemicalInput) where
  | ordinary
  | coupled (pair : source.AromaticCanonicalRule3CoupledUnitPair)
  deriving DecidableEq, Repr

/-- Resolve no match, one match, or ambiguity without choosing by enumeration order. -/
noncomputable def aromaticCanonicalRule3PhysicalTopologyResolution?
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    Option source.AromaticCanonicalRule3PhysicalTopologyResolution :=
  match source.aromaticCanonicalRule3CoupledUnitPairs keys with
  | [] => some .ordinary
  | [pair] => some (.coupled pair)
  | _ :: _ :: _ => none

/-- Independent positive meaning of either unambiguous result. -/
inductive DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.AromaticCanonicalRule3PhysicalTopologyResolution → Prop
  | ordinary
      (absent : ∀ pair,
        ¬ source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair) :
      source.DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution keys .ordinary
  | coupled {pair : source.AromaticCanonicalRule3CoupledUnitPair}
      (derived : source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair)
      (unique : ∀ other,
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys other → other = pair) :
      source.DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution
        keys (.coupled pair)

theorem aromaticCanonicalRule3PhysicalTopologyResolution?_sound
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (resolution : source.AromaticCanonicalRule3PhysicalTopologyResolution)
    (computed : source.aromaticCanonicalRule3PhysicalTopologyResolution? keys =
      some resolution) :
    source.DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution
      keys resolution := by
  unfold aromaticCanonicalRule3PhysicalTopologyResolution? at computed
  generalize foundIdentity :
      source.aromaticCanonicalRule3CoupledUnitPairs keys = found at computed
  cases found with
  | nil =>
      simp at computed
      subst resolution
      exact .ordinary (by
        intro pair derived
        have present := (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff
          keys pair).mpr derived
        rw [foundIdentity] at present
        simp at present)
  | cons pair tail =>
      cases tail with
      | nil =>
          simp at computed
          subst resolution
          exact .coupled
            ((source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys pair).mp
              (by rw [foundIdentity]; simp))
            (by
              intro other derived
              have present :=
                (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff
                  keys other).mpr derived
              rw [foundIdentity] at present
              simpa using present)
      | cons second rest => simp at computed

/-- Common exclusion set induced by one proved-unambiguous topology. -/
def aromaticCanonicalRule3ExcludedPhysicalUnits
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.AromaticCanonicalRule3PhysicalTopologyResolution →
      List source.AromaticCanonicalRule3PhysicalUnitId
  | .ordinary => source.aromaticCanonicalRule3SharedPhysicalUnits keys
  | .coupled pair =>
      (source.aromaticCanonicalRule3SharedPhysicalUnits keys).filter fun unit =>
        unit != pair.firstUnit && unit != pair.secondUnit

@[simp] theorem mem_aromaticCanonicalRule3ExcludedPhysicalUnits_ordinary_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId) :
    unit ∈ source.aromaticCanonicalRule3ExcludedPhysicalUnits keys (.ordinary) ↔
      unit ∈ source.aromaticCanonicalRule3SharedPhysicalUnits keys := by
  rfl

@[simp] theorem mem_aromaticCanonicalRule3ExcludedPhysicalUnits_coupled_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair)
    (unit : source.AromaticCanonicalRule3PhysicalUnitId) :
    unit ∈ source.aromaticCanonicalRule3ExcludedPhysicalUnits keys (.coupled pair) ↔
      unit ∈ source.aromaticCanonicalRule3SharedPhysicalUnits keys ∧
        unit ≠ pair.firstUnit ∧ unit ≠ pair.secondUnit := by
  simp [aromaticCanonicalRule3ExcludedPhysicalUnits]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
