import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception
import TetraStereo.OneCenter.P93SpiroConfigurationCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-!
# Exhaustive finite-graph perception of simple spiro centers

This module recognizes the graph-theoretic core of a spiro fusion: exactly two simple-cycle vertex
sets pass through a center and distinct such cycles intersect only at that center.  Enumeration is
over all finite vertex subsets, inherited from `LocalizedMonocyclicDoubleBondPerception`; no ring
basis, smallest-ring heuristic, or size cutoff is used.

The definition intentionally does not yet classify the four ring branches as `Xabcd`, `Xabab`, or
`Xaabb`.  That classification depends on occurrence-aware CIP comparison, not topology alone.
-/

/-- Every simple cycle in the complete covalent component that contains `center`. -/
noncomputable def localizedSimpleCycleVertexSetsAt
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    Finset (Finset input.Atom) := by
  classical
  exact (input.localizedSimpleCycleVertexSetsInComponent center).filter fun ring =>
    center ∈ ring

@[simp] theorem mem_localizedSimpleCycleVertexSetsAt_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (ring : Finset input.Atom) :
    ring ∈ input.localizedSimpleCycleVertexSetsAt center ↔
      input.DeclarativeLocalizedSimpleCycleVertexSet ring ∧
        ring ⊆ input.localizedCovalentComponentAtoms center ∧
        center ∈ ring := by
  classical
  simp [localizedSimpleCycleVertexSetsAt, and_assoc]

/-- Pair condition once the complete cycle family through the center has been enumerated. -/
def LocalizedSpiroRingPairCondition
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (rings : Finset (Finset input.Atom)) : Prop :=
  rings.card = 2 ∧
    ∀ first, first ∈ rings →
      ∀ second, second ∈ rings →
        first ≠ second → first ∩ second = {center}

/-- Independent graph meaning of the complete two-ring family at a simple spiro center. -/
def DeclarativeLocalizedSpiroRingFamily
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (rings : Finset (Finset input.Atom)) : Prop :=
  rings = input.localizedSimpleCycleVertexSetsAt center ∧
    input.LocalizedSpiroRingPairCondition center rings

/-- Public carrier retaining the complete unordered pair of rings through one spiro center. -/
structure LocalizedSpiroCenter
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) where
  rings : Finset (Finset input.Atom)
  deriving DecidableEq

def DeclarativeLocalizedSpiroCenter
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center) : Prop :=
  input.DeclarativeLocalizedSpiroRingFamily center carrier.rings

/-- Exhaustive perception of the simple two-cycle spiro topology at one atom. -/
noncomputable def localizedSpiroCenterAt?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    Option (input.LocalizedSpiroCenter center) := by
  classical
  let rings := input.localizedSimpleCycleVertexSetsAt center
  if accepted : input.LocalizedSpiroRingPairCondition center rings then
    exact some { rings }
  else
    exact none

/-- Perception succeeds exactly for the independent complete-ring-family predicate. -/
theorem localizedSpiroCenterAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center) :
    input.localizedSpiroCenterAt? center = some carrier ↔
      input.DeclarativeLocalizedSpiroCenter center carrier := by
  classical
  let ringsAt := input.localizedSimpleCycleVertexSetsAt center
  by_cases accepted : input.LocalizedSpiroRingPairCondition center ringsAt
  · constructor
    · intro computed
      have computed' : some ({ rings := ringsAt } : input.LocalizedSpiroCenter center) =
          some carrier := by
        simpa only [localizedSpiroCenterAt?, ringsAt, accepted, ↓reduceIte] using computed
      have carrierEq := Option.some.inj computed'
      rw [← carrierEq]
      exact ⟨rfl, accepted⟩
    · intro judged
      have carrierEq : carrier =
          ({ rings := ringsAt } : input.LocalizedSpiroCenter center) := by
        cases carrier with
        | mk carrierRings =>
            congr
            exact judged.1
      rw [carrierEq]
      unfold localizedSpiroCenterAt?
      dsimp only
      have acceptedAt : input.LocalizedSpiroRingPairCondition center
          (input.localizedSimpleCycleVertexSetsAt center) := by
        simpa only [ringsAt] using accepted
      rw [dif_pos acceptedAt]
  · constructor
    · intro computed
      simp only [localizedSpiroCenterAt?, ringsAt, accepted] at computed
      contradiction
    · intro judged
      apply False.elim
      apply accepted
      have ringsEq : carrier.rings = ringsAt := by
        simpa only [ringsAt] using judged.1
      rw [← ringsEq]
      exact judged.2

/-- `none` has no hidden heuristic meaning: no independently valid two-ring carrier exists. -/
theorem localizedSpiroCenterAt?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    input.localizedSpiroCenterAt? center = none ↔
      ∀ carrier, ¬input.DeclarativeLocalizedSpiroCenter center carrier := by
  constructor
  · intro computed carrier judged
    have someEq :=
      (input.localizedSpiroCenterAt?_eq_some_iff center carrier).mpr judged
    rw [computed] at someEq
    simp at someEq
  · intro absent
    cases computed : input.localizedSpiroCenterAt? center with
    | none => rfl
    | some carrier =>
        exact False.elim (absent carrier
          ((input.localizedSpiroCenterAt?_eq_some_iff center carrier).mp computed))

theorem declarativeLocalizedSpiroCenter_subsingleton
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    {left right : input.LocalizedSpiroCenter center}
    (leftJudged : input.DeclarativeLocalizedSpiroCenter center left)
    (rightJudged : input.DeclarativeLocalizedSpiroCenter center right) :
    left = right := by
  cases left
  cases right
  simp only [DeclarativeLocalizedSpiroCenter,
    DeclarativeLocalizedSpiroRingFamily] at leftJudged rightJudged ⊢
  congr
  exact leftJudged.1.trans rightJudged.1.symm

/-- The two physical rings represented by every valid carrier. -/
theorem DeclarativeLocalizedSpiroCenter.exists_distinct_rings
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier) :
    ∃ first second,
      first ≠ second ∧
      carrier.rings = {first, second} := by
  exact Finset.card_eq_two.mp judged.2.1

/-- Every member of a perceived spiro pair is a genuine simple cycle containing the center. -/
theorem DeclarativeLocalizedSpiroCenter.ring_meaning
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier)
    (ring : Finset input.Atom) (present : ring ∈ carrier.rings) :
    input.DeclarativeLocalizedSimpleCycleVertexSet ring ∧
      ring ⊆ input.localizedCovalentComponentAtoms center ∧
      center ∈ ring := by
  apply (input.mem_localizedSimpleCycleVertexSetsAt_iff center ring).mp
  rw [← judged.1]
  exact present

/-- Each constituent ring contributes exactly two distinct graph neighbours at the spiro atom. -/
theorem DeclarativeLocalizedSpiroCenter.ringNeighbors_card
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier)
    (ring : Finset input.Atom) (present : ring ∈ carrier.rings) :
    (input.localizedCycleNeighbors ring center).card = 2 := by
  have meaning := judged.ring_meaning input center carrier ring present
  exact meaning.1.2.1 center meaning.2.2

/-- Distinct spiro rings contribute disjoint neighbour pairs. -/
theorem DeclarativeLocalizedSpiroCenter.ringNeighbors_disjoint
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier)
    (first second : Finset input.Atom)
    (firstPresent : first ∈ carrier.rings)
    (secondPresent : second ∈ carrier.rings)
    (different : first ≠ second) :
    Disjoint (input.localizedCycleNeighbors first center)
      (input.localizedCycleNeighbors second center) := by
  rw [Finset.disjoint_left]
  intro atom firstNeighbor secondNeighbor
  have firstMeaning :=
    (input.mem_localizedCycleNeighbors_iff first center atom).mp firstNeighbor
  have secondMeaning :=
    (input.mem_localizedCycleNeighbors_iff second center atom).mp secondNeighbor
  have inIntersection : atom ∈ first ∩ second := by
    simp [firstMeaning.1, secondMeaning.1]
  have intersectionEq := judged.2.2 first firstPresent second secondPresent different
  rw [intersectionEq] at inIntersection
  have atomEq : atom = center := by simpa using inIntersection
  subst atom
  simpa [MoleculeGraph.Adj, input.moleculeGraph.bond_self] using firstMeaning.2

/-- The ring topology supplies exactly four distinct branch starts, before any CIP comparison. -/
theorem DeclarativeLocalizedSpiroCenter.four_ring_branch_starts
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedSpiroCenter center carrier) :
    ∃ first second,
      first ≠ second ∧
      carrier.rings = {first, second} ∧
      (input.localizedCycleNeighbors first center ∪
        input.localizedCycleNeighbors second center).card = 4 := by
  obtain ⟨first, second, different, ringsEq⟩ :=
    judged.exists_distinct_rings input center carrier
  have firstPresent : first ∈ carrier.rings := by simp [ringsEq]
  have secondPresent : second ∈ carrier.rings := by simp [ringsEq]
  have disjoint := judged.ringNeighbors_disjoint input center carrier first second
    firstPresent secondPresent different
  refine ⟨first, second, different, ringsEq, ?_⟩
  rw [Finset.card_union_of_disjoint disjoint,
    judged.ringNeighbors_card input center carrier first firstPresent,
    judged.ringNeighbors_card input center carrier second secondPresent]

/-- Whole-molecule finite set of every atom satisfying the exact simple-spiro topology. -/
noncomputable def localizedSpiroCenters
    (input : CertifiedLocalizedCIPInput) : Finset input.Atom := by
  classical
  exact Finset.univ.filter fun center =>
    (input.localizedSpiroCenterAt? center).isSome

@[simp] theorem mem_localizedSpiroCenters_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    center ∈ input.localizedSpiroCenters ↔
      ∃ carrier, input.DeclarativeLocalizedSpiroCenter center carrier := by
  classical
  simp only [localizedSpiroCenters, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Option.isSome_iff_exists]
  exact exists_congr fun carrier =>
    input.localizedSpiroCenterAt?_eq_some_iff center carrier

theorem localizedSpiroCenters_toList_nodup
    (input : CertifiedLocalizedCIPInput) :
    input.localizedSpiroCenters.toList.Nodup :=
  input.localizedSpiroCenters.nodup_toList

theorem localizedSpiroCenter_count_eq_one_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    List.count center input.localizedSpiroCenters.toList = 1 ↔
      ∃ carrier, input.DeclarativeLocalizedSpiroCenter center carrier := by
  rw [← input.mem_localizedSpiroCenters_iff center]
  constructor
  · intro countOne
    by_contra absent
    have countZero : List.count center input.localizedSpiroCenters.toList = 0 :=
      List.count_eq_zero.mpr (by simpa using absent)
    omega
  · intro present
    exact List.count_eq_one_of_mem input.localizedSpiroCenters.nodup_toList (by simpa using present)

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
