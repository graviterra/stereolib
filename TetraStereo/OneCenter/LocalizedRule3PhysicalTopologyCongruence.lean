import TetraStereo.OneCenter.LocalizedRule3PhysicalIncidence
import TetraStereo.OneCenter.LocalizedConstitutionalObservable

set_option autoImplicit false

namespace TetraStereo.OneCenter














































namespace CertifiedLocalizedCIPInput

/-- The exact comparison- and incidence-visible content of one recursively ranked Rule-3 spatial
key that the coupled-topology resolver can read.  The Rule-3 priority projection `rule3`, the
observation order and the sparse-entry payloads are deliberately unconstrained. -/
def LocalizedRule3PhysicalTopologyCongruent
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  constitutionalObservable left.constitutional =
      constitutionalObservable right.constitutional ∧
    LocalizedRule3PhysicalIncidenceEquivalent input left right

namespace LocalizedRule3PhysicalTopologyCongruent

/-- The relation is symmetric. -/
theorem symm
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3PhysicalTopologyCongruent input left right) :
    LocalizedRule3PhysicalTopologyCongruent input right left :=
  ⟨related.1.symm, LocalizedRule3PhysicalIncidenceEquivalent.symm input related.2⟩

/-- The relation is reflexive. -/
theorem refl
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    LocalizedRule3PhysicalTopologyCongruent input key key :=
  ⟨rfl, LocalizedRule3PhysicalIncidenceEquivalent.refl input key⟩

/-- The constitutional observables agree. -/
theorem constitutionalObservable_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3PhysicalTopologyCongruent input left right) :
    constitutionalObservable left.constitutional =
      constitutionalObservable right.constitutional :=
  related.1

/-- Physical-unit incidence agrees. -/
theorem physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3PhysicalTopologyCongruent input left right) :
    LocalizedRule3PhysicalIncidenceEquivalent input left right :=
  related.2

/-- Physical-unit identities have the same incidence in both keys. -/
theorem mem_physicalUnitIds_iff
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3PhysicalTopologyCongruent input left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds left ↔
      unit ∈ input.localizedRule3PhysicalUnitIds right :=
  related.2 unit

end LocalizedRule3PhysicalTopologyCongruent

namespace LocalizedRule3PhysicalTopology



theorem forall₂_physicalIncidence_of_forall₂_congruent
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input) left right := by
  induction related with
  | nil => exact List.Forall₂.nil
  | cons head tail ih => exact List.Forall₂.cons head.2 ih





theorem forall₂_congruent_of_forall₂_observable_and_physicalIncidence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (observableRelated : List.Forall₂
      (fun l r : input.LocalizedRerootRecursiveRule3SpatialKey =>
        constitutionalObservable l.constitutional =
          constitutionalObservable r.constitutional) left right)
    (physicalRelated : List.Forall₂ (LocalizedRule3PhysicalIncidenceEquivalent input)
      left right) :
    List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right := by
  induction observableRelated with
  | nil =>
      cases physicalRelated
      exact List.Forall₂.nil
  | cons head tail ih =>
      cases physicalRelated with
      | cons physicalHead physicalTail =>
          exact List.Forall₂.cons ⟨head, physicalHead⟩ (ih physicalTail)

/-! ## Constitutional comparison

`ruleMajor_compare_eq_observable` identifies `OfficialRuleMajorKey.compare` with the comparison of
constitutional observables (`compareConstitutionalObservable`), and
`compareConstitutionalObservable_eq_iff` says that comparison decides observable equality.  The
four-way tie therefore transports under observable equality alone. -/

/-- Equal constitutional observables compare constitutionally equal. -/
theorem constitutional_compare_eq_of_constitutionalObservable_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (same : constitutionalObservable left.constitutional =
      constitutionalObservable right.constitutional) :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq := by
  rw [ruleMajor_compare_eq_observable, same]
  exact (compareConstitutionalObservable_eq_iff _ _).mpr rfl

/-- A constitutional comparison to equality exposes equality of the two constitutional
observables. -/
theorem constitutionalObservable_eq_of_constitutional_compare_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (compared :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq) :
    constitutionalObservable left.constitutional =
      constitutionalObservable right.constitutional := by
  rw [ruleMajor_compare_eq_observable] at compared
  exact (compareConstitutionalObservable_eq_iff _ _).mp compared

/-- Constitutional comparison-to-equality is invariant when each key is replaced by a key with the
same constitutional observable. -/
theorem constitutional_compare_eq_iff_of_constitutionalObservable_eq
    (input : CertifiedLocalizedCIPInput)
    {left left' right right' : input.LocalizedRerootRecursiveRule3SpatialKey}
    (leftSame : constitutionalObservable left.constitutional =
      constitutionalObservable left'.constitutional)
    (rightSame : constitutionalObservable right.constitutional =
      constitutionalObservable right'.constitutional) :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq ↔
      OfficialRuleMajorKey.compare left'.constitutional right'.constitutional =
        Ordering.eq := by
  constructor
  · intro compared
    exact constitutional_compare_eq_of_constitutionalObservable_eq input
      (leftSame.symm.trans
        ((constitutionalObservable_eq_of_constitutional_compare_eq input compared).trans
          rightSame))
  · intro compared
    exact constitutional_compare_eq_of_constitutionalObservable_eq input
      (leftSame.trans
        ((constitutionalObservable_eq_of_constitutional_compare_eq input compared).trans
          rightSame.symm))

/-- Among keys with equal constitutional observables, the four-way tie is preserved by replacing
each key by any key with the same constitutional observable.  No incidence hypothesis and no
Rule-3 priority hypothesis is used. -/
theorem fourWayConstitutionalTie_iff_of_constitutionalObservable_eq
    (input : CertifiedLocalizedCIPInput)
    {k0 k1 k2 k3 r0 r1 r2 r3 : input.LocalizedRerootRecursiveRule3SpatialKey}
    (h0 : constitutionalObservable k0.constitutional =
      constitutionalObservable r0.constitutional)
    (h1 : constitutionalObservable k1.constitutional =
      constitutionalObservable r1.constitutional)
    (h2 : constitutionalObservable k2.constitutional =
      constitutionalObservable r2.constitutional)
    (h3 : constitutionalObservable k3.constitutional =
      constitutionalObservable r3.constitutional) :
    input.DeclarativeLocalizedRule3FourWayConstitutionalTie k0 k1 k2 k3 ↔
      input.DeclarativeLocalizedRule3FourWayConstitutionalTie r0 r1 r2 r3 := by
  unfold DeclarativeLocalizedRule3FourWayConstitutionalTie
  repeat' apply and_congr
  all_goals
    first
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h0 h0
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h0 h1
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h0 h2
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h0 h3
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h1 h0
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h1 h1
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h1 h2
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h1 h3
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h2 h0
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h2 h1
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h2 h2
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h2 h3
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h3 h0
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h3 h1
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h3 h2
    | exact constitutional_compare_eq_iff_of_constitutionalObservable_eq input h3 h3

/-- The explicit sixteen-comparison constitutional tie is invariant under pointwise physical
topology congruence. -/
theorem fourWayConstitutionalTie_iff_of_physicalTopologyCongruent
    (input : CertifiedLocalizedCIPInput)
    {k0 k1 k2 k3 r0 r1 r2 r3 : input.LocalizedRerootRecursiveRule3SpatialKey}
    (h0 : LocalizedRule3PhysicalTopologyCongruent input k0 r0)
    (h1 : LocalizedRule3PhysicalTopologyCongruent input k1 r1)
    (h2 : LocalizedRule3PhysicalTopologyCongruent input k2 r2)
    (h3 : LocalizedRule3PhysicalTopologyCongruent input k3 r3) :
    input.DeclarativeLocalizedRule3FourWayConstitutionalTie k0 k1 k2 k3 ↔
      input.DeclarativeLocalizedRule3FourWayConstitutionalTie r0 r1 r2 r3 :=
  fourWayConstitutionalTie_iff_of_constitutionalObservable_eq input
    h0.1 h1.1 h2.1 h3.1






/-- Exact two-key incidence is invariant under pointwise physical topology congruence. -/
theorem exactPairIncidence_iff_of_physicalTopologyCongruent
    (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedRule3PhysicalUnitId)
    {first first' second second' outsideFirst outsideFirst' outsideSecond outsideSecond' :
      input.LocalizedRerootRecursiveRule3SpatialKey}
    (firstRelated : LocalizedRule3PhysicalTopologyCongruent input first first')
    (secondRelated : LocalizedRule3PhysicalTopologyCongruent input second second')
    (outsideFirstRelated :
      LocalizedRule3PhysicalTopologyCongruent input outsideFirst outsideFirst')
    (outsideSecondRelated :
      LocalizedRule3PhysicalTopologyCongruent input outsideSecond outsideSecond') :
    input.DeclarativeLocalizedRule3ExactPairIncidence
        unit first second outsideFirst outsideSecond ↔
      input.DeclarativeLocalizedRule3ExactPairIncidence
        unit first' second' outsideFirst' outsideSecond' := by
  unfold DeclarativeLocalizedRule3ExactPairIncidence
  exact and_congr (firstRelated.2 unit)
    (and_congr (secondRelated.2 unit)
      (and_congr (not_congr (outsideFirstRelated.2 unit))
        (not_congr (outsideSecondRelated.2 unit))))

/-- Complementary-pair incidence is invariant under pointwise physical topology congruence. -/
theorem complementaryPairIncidence_iff_of_physicalTopologyCongruent
    (input : CertifiedLocalizedCIPInput)
    (firstUnit secondUnit : input.LocalizedRule3PhysicalUnitId)
    {pairFirst pairFirst' pairSecond pairSecond'
      complementFirst complementFirst' complementSecond complementSecond' :
      input.LocalizedRerootRecursiveRule3SpatialKey}
    (pairFirstRelated :
      LocalizedRule3PhysicalTopologyCongruent input pairFirst pairFirst')
    (pairSecondRelated :
      LocalizedRule3PhysicalTopologyCongruent input pairSecond pairSecond')
    (complementFirstRelated :
      LocalizedRule3PhysicalTopologyCongruent input complementFirst complementFirst')
    (complementSecondRelated :
      LocalizedRule3PhysicalTopologyCongruent input complementSecond complementSecond') :
    input.DeclarativeLocalizedRule3ComplementaryPairIncidence
        firstUnit secondUnit pairFirst pairSecond complementFirst complementSecond ↔
      input.DeclarativeLocalizedRule3ComplementaryPairIncidence
        firstUnit secondUnit pairFirst' pairSecond' complementFirst' complementSecond' := by
  unfold DeclarativeLocalizedRule3ComplementaryPairIncidence
  exact or_congr
    (and_congr
      (exactPairIncidence_iff_of_physicalTopologyCongruent input firstUnit
        pairFirstRelated pairSecondRelated complementFirstRelated complementSecondRelated)
      (exactPairIncidence_iff_of_physicalTopologyCongruent input secondUnit
        complementFirstRelated complementSecondRelated pairFirstRelated pairSecondRelated))
    (and_congr
      (exactPairIncidence_iff_of_physicalTopologyCongruent input secondUnit
        pairFirstRelated pairSecondRelated complementFirstRelated complementSecondRelated)
      (exactPairIncidence_iff_of_physicalTopologyCongruent input firstUnit
        complementFirstRelated complementSecondRelated pairFirstRelated pairSecondRelated))

/-- A frame whose key list has length other than four never satisfies the executable matching
relation, independently of the observations it carries. -/
theorem not_declarativeLocalizedRule3CoupledMatching_of_length_ne_four
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (length : keys.length ≠ 4)
    (matching : input.LocalizedRule3CoupledMatching) :
    ¬ input.DeclarativeLocalizedRule3CoupledMatching keys matching := by
  intro derived
  rcases matching with ⟨pairing, firstUnit, secondUnit⟩
  cases keys with
  | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at derived
  | cons k0 rest0 =>
      cases rest0 with
      | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at derived
      | cons k1 rest1 =>
          cases rest1 with
          | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at derived
          | cons k2 rest2 =>
              cases rest2 with
              | nil => simp [DeclarativeLocalizedRule3CoupledMatching] at derived
              | cons k3 rest3 =>
                  cases rest3 with
                  | nil => exact length rfl
                  | cons k4 rest4 =>
                      simp [DeclarativeLocalizedRule3CoupledMatching] at derived

/-- The complete independent matching relation is invariant under a pointwise congruent key
list.  Only the two matched units' incidence, the constitutional tie and the two-unit incidence
pattern are read, so `rule3` and the observation payload are irrelevant. -/
theorem declarativeLocalizedRule3CoupledMatching_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    input.DeclarativeLocalizedRule3CoupledMatching left matching ↔
      input.DeclarativeLocalizedRule3CoupledMatching right matching := by
  by_cases four : left.length = 4
  · obtain ⟨k0, k1, k2, k3, rfl⟩ := List.length_eq_four.mp four
    have frameIff : ∀ unit : input.LocalizedRule3PhysicalUnitId,
        unit ∈ input.localizedRule3FramePhysicalUnits [k0, k1, k2, k3] ↔
          unit ∈ input.localizedRule3FramePhysicalUnits right :=
      fun unit =>
        input.mem_localizedRule3FramePhysicalUnits_iff_of_forall₂_physicalIncidence
          [k0, k1, k2, k3] right
          (forall₂_physicalIncidence_of_forall₂_congruent input
            [k0, k1, k2, k3] right related)
          unit
    rcases List.forall₂_cons_left_iff.mp related with ⟨r0, u1, h0, rest1, rfl⟩
    rcases List.forall₂_cons_left_iff.mp rest1 with ⟨r1, u2, h1, rest2, rfl⟩
    rcases List.forall₂_cons_left_iff.mp rest2 with ⟨r2, u3, h2, rest3, rfl⟩
    rcases List.forall₂_cons_left_iff.mp rest3 with ⟨r3, u4, h3, rest4, rfl⟩
    have u4nil : u4 = [] := List.forall₂_nil_left_iff.mp rest4
    subst u4
    rcases matching with ⟨pairing, firstUnit, secondUnit⟩
    unfold DeclarativeLocalizedRule3CoupledMatching
    refine and_congr (frameIff firstUnit)
      (and_congr (frameIff secondUnit) (and_congr Iff.rfl ?_))
    refine and_congr
      (fourWayConstitutionalTie_iff_of_physicalTopologyCongruent input h0 h1 h2 h3) ?_
    cases pairing with
    | pair01_23 =>
        exact complementaryPairIncidence_iff_of_physicalTopologyCongruent input
          firstUnit secondUnit h0 h1 h2 h3
    | pair02_13 =>
        exact complementaryPairIncidence_iff_of_physicalTopologyCongruent input
          firstUnit secondUnit h0 h2 h1 h3
    | pair03_12 =>
        exact complementaryPairIncidence_iff_of_physicalTopologyCongruent input
          firstUnit secondUnit h0 h3 h1 h2
  · have rightLength : right.length ≠ 4 := by
      intro rightFour
      exact four (by
        rw [List.Forall₂.length_eq related]
        exact rightFour)
    exact ⟨
      fun derived =>
        (not_declarativeLocalizedRule3CoupledMatching_of_length_ne_four
          input left four matching derived).elim,
      fun derived =>
        (not_declarativeLocalizedRule3CoupledMatching_of_length_ne_four
          input right rightLength matching derived).elim⟩

/-! ## Exhaustive matching search

The executable search enumerates the frame physical-unit universe and filters by the independent
matching relation.  Pointwise congruent frames therefore run the same membership test over the same
unit universe; the resulting duplicate-free lists are permutations of one another.  No alignment
of the two physical-unit lists is assumed. -/

/-- Duplicate-free lists with the same membership are permutations of one another. -/
private theorem perm_of_nodup_of_mem_iff
    {α : Type*} [BEq α] [LawfulBEq α]
    {left right : List α}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (membership : ∀ a, a ∈ left ↔ a ∈ right) :
    List.Perm left right := by
  rw [List.perm_iff_count]
  intro a
  rw [List.Nodup.count leftNodup, List.Nodup.count rightNodup]
  by_cases present : a ∈ left
  · rw [if_pos present, if_pos ((membership a).mp present)]
  · rw [if_neg present, if_neg (fun other => present ((membership a).mpr other))]

/-- The executable perfect-matching list is duplicate-free. -/
theorem localizedRule3CoupledPerfectMatchingsExec_nodup
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    (input.localizedRule3CoupledPerfectMatchingsExec keys).Nodup := by
  unfold localizedRule3CoupledPerfectMatchingsExec
  exact (input.localizedRule3CoupledMatchingCandidates_nodup keys).filter _

/-- Membership in the executable perfect-matching list is invariant. -/
theorem mem_localizedRule3CoupledPerfectMatchingsExec_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    matching ∈ input.localizedRule3CoupledPerfectMatchingsExec left ↔
      matching ∈ input.localizedRule3CoupledPerfectMatchingsExec right := by
  have physicalRelated :=
    forall₂_physicalIncidence_of_forall₂_congruent input left right related
  have frame : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ input.localizedRule3FramePhysicalUnits left ↔
        unit ∈ input.localizedRule3FramePhysicalUnits right :=
    fun unit =>
      input.mem_localizedRule3FramePhysicalUnits_iff_of_forall₂_physicalIncidence
        left right physicalRelated unit
  have derivedIff :=
    declarativeLocalizedRule3CoupledMatching_iff_of_forall₂ input left right matching related
  have candidateIff :
      matching ∈ input.localizedRule3CoupledMatchingCandidates left ↔
        matching ∈ input.localizedRule3CoupledMatchingCandidates right := by
    rw [input.mem_localizedRule3CoupledMatchingCandidates_iff left matching,
      input.mem_localizedRule3CoupledMatchingCandidates_iff right matching]
    exact and_congr (frame matching.firstUnit) (frame matching.secondUnit)
  unfold localizedRule3CoupledPerfectMatchingsExec
  rw [List.mem_filter, List.mem_filter]
  simp only [decide_eq_true_eq]
  rw [candidateIff, derivedIff]

/-- The two executable perfect-matching lists are permutations of one another.  The candidate
order is the raw frame physical-unit order and is deliberately not assumed equal; duplicate
freedom plus equal membership is enough. -/
theorem localizedRule3CoupledPerfectMatchingsExec_perm_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    List.Perm
      (input.localizedRule3CoupledPerfectMatchingsExec left)
      (input.localizedRule3CoupledPerfectMatchingsExec right) :=
  perm_of_nodup_of_mem_iff
    (localizedRule3CoupledPerfectMatchingsExec_nodup input left)
    (localizedRule3CoupledPerfectMatchingsExec_nodup input right)
    (fun matching =>
      mem_localizedRule3CoupledPerfectMatchingsExec_iff_of_forall₂
        input left right matching related)

/-- Topology resolution is invariant as a full `Option`: absence, a unique coupled matching, and
refusal are classified identically on pointwise congruent frames.  A permutation cannot change the
empty/singleton/multiple shape of a list, and a singleton permutation forces the same element. -/
theorem localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    input.localizedRule3CoupledTopologyResolutionExec? left =
      input.localizedRule3CoupledTopologyResolutionExec? right := by
  have permutation :=
    localizedRule3CoupledPerfectMatchingsExec_perm_of_forall₂ input left right related
  unfold localizedRule3CoupledTopologyResolutionExec?
  cases leftMatchings : input.localizedRule3CoupledPerfectMatchingsExec left with
  | nil =>
      have rightMatchings :
          input.localizedRule3CoupledPerfectMatchingsExec right = [] := by
        have computed := permutation
        rw [leftMatchings] at computed
        exact List.nil_perm.mp computed
      rw [rightMatchings]
  | cons matching rest =>
      cases rest with
      | nil =>
          have rightMatchings :
              input.localizedRule3CoupledPerfectMatchingsExec right = [matching] := by
            have computed := permutation
            rw [leftMatchings] at computed
            exact (List.singleton_perm.mp computed).symm
          rw [rightMatchings]
      | cons second more =>
          have lengthEq := permutation.length_eq
          rw [leftMatchings] at lengthEq
          cases rightMatchings : input.localizedRule3CoupledPerfectMatchingsExec right with
          | nil =>
              rw [rightMatchings] at lengthEq
              simp only [List.length_cons, List.length_nil] at lengthEq
              omega
          | cons first tail =>
              cases tail with
              | nil =>
                  rw [rightMatchings] at lengthEq
                  simp only [List.length_cons, List.length_nil] at lengthEq
                  omega
              | cons next moreRight =>
                  rfl

/-- The original (non-executable) topology resolver is invariant under the same relation.  This is
the actual dispatcher used by the declarative endpoint, not a re-statement of its specification. -/
theorem localizedRule3CoupledTopologyResolution?_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    input.localizedRule3CoupledTopologyResolution? left =
      input.localizedRule3CoupledTopologyResolution? right := by
  rw [← input.localizedRule3CoupledTopologyResolutionExec?_eq_original left,
    ← input.localizedRule3CoupledTopologyResolutionExec?_eq_original right]
  exact localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂ input left right related

/-! ## Excluded physical units

For a fixed resolved topology the excluded set is the ordinary shared-unit domain, or that domain
with the two retained coupled units removed.  Both operations preserve membership under pointwise
physical incidence, so the exclusion *set* is determined even when list order is not. -/

/-- For one and the same resolved topology, exclusion membership is invariant. -/
theorem mem_localizedRule3CoupledExcludedPhysicalUnits_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right)
    (resolution : input.LocalizedRule3CoupledTopologyResolution)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left resolution ↔
      unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right resolution := by
  have physicalRelated :=
    forall₂_physicalIncidence_of_forall₂_congruent input left right related
  cases resolution with
  | ordinary =>
      simpa using
        input.mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff_of_forall₂_physicalIncidence
          left right physicalRelated unit
  | coupled matching =>
      rw [input.mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff,
        input.mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff,
        input.mem_localizedRule3SharedPhysicalUnits_iff_of_forall₂_physicalIncidence
          left right physicalRelated unit]

/-- The ordinary excluded set, which is exactly the shared-unit cancellation domain, has the same
membership under pointwise physical topology congruence.  This does not assume that the list is
empty, nonempty, sorted, or aligned. -/
theorem mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left .ordinary ↔
      unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right .ordinary :=
  mem_localizedRule3CoupledExcludedPhysicalUnits_iff_of_forall₂
    input left right related .ordinary unit

/-- Exclusions produced by separately evaluated executable resolutions have the same membership,
including the coupled case where the retained matching is transported through the resolved
`Option` equality. -/
theorem mem_localizedRule3CoupledExcludedPhysicalUnits_congruence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right)
    (leftResolution rightResolution : input.LocalizedRule3CoupledTopologyResolution)
    (leftComputed :
      input.localizedRule3CoupledTopologyResolutionExec? left = some leftResolution)
    (rightComputed :
      input.localizedRule3CoupledTopologyResolutionExec? right = some rightResolution)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left leftResolution ↔
      unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right rightResolution := by
  have computed :=
    localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂ input left right related
  rw [leftComputed, rightComputed] at computed
  have sameResolution : leftResolution = rightResolution := Option.some.inj computed
  rw [← sameResolution]
  exact mem_localizedRule3CoupledExcludedPhysicalUnits_iff_of_forall₂
    input left right related leftResolution unit

/-- The actual executable bridge: the resolver outcome and the exclusion membership agree.  The
two sides are allowed to have independently evaluated resolutions; the equality of the `Option`
results identifies them. -/
theorem localizedRule3CoupledTopologyExec_bridge
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right)
    (leftResolution rightResolution : input.LocalizedRule3CoupledTopologyResolution)
    (leftComputed :
      input.localizedRule3CoupledTopologyResolutionExec? left = some leftResolution)
    (rightComputed :
      input.localizedRule3CoupledTopologyResolutionExec? right = some rightResolution)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    leftResolution = rightResolution ∧
      (unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left leftResolution ↔
        unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right rightResolution) := by
  have computed :=
    localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂ input left right related
  rw [leftComputed, rightComputed] at computed
  have sameResolution : leftResolution = rightResolution := Option.some.inj computed
  refine ⟨sameResolution, ?_⟩
  rw [← sameResolution]
  exact mem_localizedRule3CoupledExcludedPhysicalUnits_iff_of_forall₂
    input left right related leftResolution unit

/-- The `isCoupled` flag of the actual executable resolver agrees on pointwise congruent frames. -/
theorem localizedRule3CoupledTopologyResolutionExec?_isCoupled_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    (input.localizedRule3CoupledTopologyResolutionExec? left).map
        (fun resolution => resolution.isCoupled) =
      (input.localizedRule3CoupledTopologyResolutionExec? right).map
        (fun resolution => resolution.isCoupled) := by
  rw [localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂ input left right related]

/-- Refusal agrees: one side refuses exactly when the other does. -/
theorem localizedRule3CoupledTopologyResolutionExec?_eq_none_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right) :
    input.localizedRule3CoupledTopologyResolutionExec? left = none ↔
      input.localizedRule3CoupledTopologyResolutionExec? right = none := by
  rw [localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂ input left right related]

/-! ## Ordinary frames

Frames whose key count is not four cannot enter the coupled branch.  The actual executable
dispatcher therefore returns the ordinary resolution, and the exclusion set is exactly the
ordinary shared-unit domain. -/

/-- The executable dispatcher resolves every non-four-key frame to ordinary cancellation. -/
theorem localizedRule3CoupledTopologyResolutionExec?_eq_ordinary_of_length_ne_four
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (length : keys.length ≠ 4) :
    input.localizedRule3CoupledTopologyResolutionExec? keys = some .ordinary := by
  rw [input.localizedRule3CoupledTopologyResolutionExec?_eq_original]
  exact input.localizedRule3CoupledTopologyResolution?_eq_ordinary_of_length_ne_four keys length

/-- **Ordinary congruence for every non-four-key frame.**  Both actual executable resolutions are
`some .ordinary` and the excluded sets are the respectively evaluated ordinary shared-unit
domains, with the same membership.  This is the reusable form of the "ordinary pair" corollary: it
applies to every key count other than four, without inspecting any matching. -/
theorem localizedRule3CoupledTopologyResolutionExec?_ordinary_congruence_of_length_ne_four
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3PhysicalTopologyCongruent input) left right)
    (length : left.length ≠ 4)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3CoupledTopologyResolutionExec? left = some .ordinary ∧
      input.localizedRule3CoupledTopologyResolutionExec? right = some .ordinary ∧
      (unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left .ordinary ↔
        unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right .ordinary) := by
  have rightLength : right.length ≠ 4 := by
    intro rightFour
    exact length (by
      rw [List.Forall₂.length_eq related]
      exact rightFour)
  exact ⟨
    localizedRule3CoupledTopologyResolutionExec?_eq_ordinary_of_length_ne_four
      input left length,
    localizedRule3CoupledTopologyResolutionExec?_eq_ordinary_of_length_ne_four
      input right rightLength,
    mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff_of_forall₂
      input left right related unit⟩

end LocalizedRule3PhysicalTopology

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopologyCongruent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopologyCongruent.symm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopologyCongruent.refl
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopologyCongruent.constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopologyCongruent.physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopologyCongruent.mem_physicalUnitIds_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.forall₂_physicalIncidence_of_forall₂_congruent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.forall₂_congruent_of_forall₂_observable_and_physicalIncidence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.constitutional_compare_eq_of_constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.constitutionalObservable_eq_of_constitutional_compare_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.constitutional_compare_eq_iff_of_constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.fourWayConstitutionalTie_iff_of_constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.fourWayConstitutionalTie_iff_of_physicalTopologyCongruent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.exactPairIncidence_iff_of_physicalTopologyCongruent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.complementaryPairIncidence_iff_of_physicalTopologyCongruent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.not_declarativeLocalizedRule3CoupledMatching_of_length_ne_four
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.declarativeLocalizedRule3CoupledMatching_iff_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledPerfectMatchingsExec_nodup
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.mem_localizedRule3CoupledPerfectMatchingsExec_iff_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledPerfectMatchingsExec_perm_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolution?_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.mem_localizedRule3CoupledExcludedPhysicalUnits_iff_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.mem_localizedRule3CoupledExcludedPhysicalUnits_ordinary_iff_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.mem_localizedRule3CoupledExcludedPhysicalUnits_congruence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyExec_bridge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolutionExec?_isCoupled_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolutionExec?_eq_none_iff_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolutionExec?_eq_ordinary_of_length_ne_four
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3PhysicalTopology.localizedRule3CoupledTopologyResolutionExec?_ordinary_congruence_of_length_ne_four
