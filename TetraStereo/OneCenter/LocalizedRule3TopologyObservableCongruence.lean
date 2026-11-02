import TetraStereo.OneCenter.LocalizedExtendedFrameCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Observable congruence of localized coupled Rule-3 topology

The comparison-visible projection of one recursively ranked Rule-3 spatial key is
`LocalizedRerootRule3SpatialKeyObservable`: Rules 1a, 1b, 2 and the Rule-3 priority sequence.  The
coupled-topology resolver, however, inspects more than that projection: it decides the four-way
constitutional tie through `OfficialRuleMajorKey.compare` and it reads physical-unit *incidence*
through `localizedRule3PhysicalUnitIds`, which is derived from the observation payload.  The numeric
Rule-3 projection alone therefore does not commute with topology resolution.

This module isolates the exact observation content the resolver reads.  Two keys are
`LocalizedRule3SpatialKeyTopologyEquivalent` when they have equal comparison-visible observables and
when every physical-unit identity occurs in one key exactly when it occurs in the other.  For lists
of keys related pointwise by that relation we prove:

* the exhaustive matching search has the same membership relation,
* because both search results are duplicate-free, they are permutations of one another,
* a permutation preserves the empty/unique/ambiguous classification, so
  `localizedRule3CoupledTopologyResolutionExec?` agrees on both lists (full `Option` equality),
* the resulting excluded physical-unit sets have the same membership, though not necessarily the
  same list order.

No assumption of literal key equality or of sort determinism is used.  The `observations` fields may
differ; only their comparison projection and their physical-unit membership are required.
-/

/-! ## Generic list transport helpers -/

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

/-- Pointwise observation content of two Rule-3 key lists that the coupled-topology resolver can
read.  Literal equality of `observations` is deliberately not required. -/
def LocalizedRule3SpatialKeyTopologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey) : Prop :=
  input.localizedRerootRule3SpatialKeyObservable left =
      input.localizedRerootRule3SpatialKeyObservable right ∧
    ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ input.localizedRule3PhysicalUnitIds left ↔
        unit ∈ input.localizedRule3PhysicalUnitIds right

namespace LocalizedRule3SpatialKeyTopologyEquivalent

/-- The relation is symmetric. -/
theorem symm
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3SpatialKeyTopologyEquivalent input left right) :
    LocalizedRule3SpatialKeyTopologyEquivalent input right left :=
  ⟨related.1.symm, fun unit => (related.2 unit).symm⟩

/-- The relation is reflexive. -/
theorem refl
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootRecursiveRule3SpatialKey) :
    LocalizedRule3SpatialKeyTopologyEquivalent input key key :=
  ⟨rfl, fun _ => Iff.rfl⟩

/-- The comparison-visible projections agree. -/
theorem observable_eq
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3SpatialKeyTopologyEquivalent input left right) :
    input.localizedRerootRule3SpatialKeyObservable left =
      input.localizedRerootRule3SpatialKeyObservable right :=
  related.1

/-- Physical-unit identities have the same incidence in both keys. -/
theorem mem_physicalUnitIds_iff
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3SpatialKeyTopologyEquivalent input left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3PhysicalUnitIds left ↔
      unit ∈ input.localizedRule3PhysicalUnitIds right :=
  related.2 unit

end LocalizedRule3SpatialKeyTopologyEquivalent

namespace CertifiedLocalizedCIPInput

/-! ## Concrete observation projections

The resolver's frame universe is the duplicate-free list of physical-unit identities observed in
the four ligand keys.  Pointwise membership equivalence transports that universe, the number of keys
containing a unit, and therefore the ordinary shared-unit cancellation domain. -/

/-- The frame physical-unit universe has the same membership for pointwise related key lists. -/
theorem mem_localizedRule3FramePhysicalUnits_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3FramePhysicalUnits left ↔
      unit ∈ input.localizedRule3FramePhysicalUnits right := by
  unfold localizedRule3FramePhysicalUnits
  rw [input.mem_eraseDups_localizedRule3PhysicalUnitId_iff,
    input.mem_eraseDups_localizedRule3PhysicalUnitId_iff]
  exact exists_mem_flatMap_iff_of_forall₂
    (r := LocalizedRule3SpatialKeyTopologyEquivalent input)
    (fun key => input.localizedRule3PhysicalUnitIds key)
    (fun key => input.localizedRule3PhysicalUnitIds key)
    (fun _ _ keyRelated c => keyRelated.2 c) unit related

/-- The number of ligand keys containing one physical unit is invariant. -/
theorem localizedRule3PhysicalUnitKeyCount_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3PhysicalUnitKeyCount left unit =
      input.localizedRule3PhysicalUnitKeyCount right unit := by
  unfold localizedRule3PhysicalUnitKeyCount
  exact length_filter_eq_of_forall₂
    (r := LocalizedRule3SpatialKeyTopologyEquivalent input)
    (fun key => (input.localizedRule3PhysicalUnitIds key).contains unit)
    (fun key => (input.localizedRule3PhysicalUnitIds key).contains unit)
    (fun _ _ keyRelated => by simp [List.contains_eq_mem, keyRelated.2 unit])
    related

/-- The ordinary shared-unit cancellation domain has the same membership. -/
theorem mem_localizedRule3SharedPhysicalUnits_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3SharedPhysicalUnits left ↔
      unit ∈ input.localizedRule3SharedPhysicalUnits right := by
  have frame :=
    input.mem_localizedRule3FramePhysicalUnits_iff_of_forall₂ left right related unit
  unfold localizedRule3FramePhysicalUnits at frame
  have count :=
    input.localizedRule3PhysicalUnitKeyCount_eq_of_forall₂ left right related unit
  rw [input.mem_localizedRule3SharedPhysicalUnits_iff,
    input.mem_localizedRule3SharedPhysicalUnits_iff]
  constructor
  · rintro ⟨member, many⟩
    exact ⟨frame.mp member, by rw [← count]; exact many⟩
  · rintro ⟨member, many⟩
    exact ⟨frame.mpr member, by rw [count]; exact many⟩

/-! ## Constitutional comparison

The constitutional comparator reads only Rules 1a, 1b and 2 (see
`officialRuleMajorKey_compare_eq_iff`), all of which are part of the observable projection. -/

/-- Keys with equal comparison-visible observables compare constitutionally equal. -/
theorem constitutional_compare_eq_of_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedRerootRecursiveRule3SpatialKey}
    (related : LocalizedRule3SpatialKeyTopologyEquivalent input left right) :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq := by
  rw [officialRuleMajorKey_compare_eq_iff]
  refine ⟨?_, ?_, ?_⟩
  · simpa [localizedRerootRule3SpatialKeyObservable] using
      congrArg LocalizedRerootRule3SpatialKeyObservable.rule1a related.1
  · simpa [localizedRerootRule3SpatialKeyObservable] using
      congrArg LocalizedRerootRule3SpatialKeyObservable.rule1b related.1
  · simpa [localizedRerootRule3SpatialKeyObservable] using
      congrArg LocalizedRerootRule3SpatialKeyObservable.rule2 related.1

/-- Constitutional comparison-to-equality is invariant under the pointwise relation. -/
theorem constitutional_compare_eq_iff_of_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    {left left' right right' : input.LocalizedRerootRecursiveRule3SpatialKey}
    (leftRelated : LocalizedRule3SpatialKeyTopologyEquivalent input left left')
    (rightRelated : LocalizedRule3SpatialKeyTopologyEquivalent input right right') :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq ↔
      OfficialRuleMajorKey.compare left'.constitutional right'.constitutional =
        Ordering.eq := by
  constructor
  · intro compared
    rw [officialRuleMajorKey_compare_eq_iff] at compared ⊢
    refine ⟨?_, ?_, ?_⟩
    · simpa [localizedRerootRule3SpatialKeyObservable] using
        (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1a leftRelated.1).symm.trans
          (compared.1.trans
            (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1a rightRelated.1))
    · simpa [localizedRerootRule3SpatialKeyObservable] using
        (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1b leftRelated.1).symm.trans
          (compared.2.1.trans
            (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1b rightRelated.1))
    · simpa [localizedRerootRule3SpatialKeyObservable] using
        (congrArg LocalizedRerootRule3SpatialKeyObservable.rule2 leftRelated.1).symm.trans
          (compared.2.2.trans
            (congrArg LocalizedRerootRule3SpatialKeyObservable.rule2 rightRelated.1))
  · intro compared
    rw [officialRuleMajorKey_compare_eq_iff] at compared ⊢
    refine ⟨?_, ?_, ?_⟩
    · simpa [localizedRerootRule3SpatialKeyObservable] using
        (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1a leftRelated.1).trans
          (compared.1.trans
            (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1a rightRelated.1).symm)
    · simpa [localizedRerootRule3SpatialKeyObservable] using
        (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1b leftRelated.1).trans
          (compared.2.1.trans
            (congrArg LocalizedRerootRule3SpatialKeyObservable.rule1b rightRelated.1).symm)
    · simpa [localizedRerootRule3SpatialKeyObservable] using
        (congrArg LocalizedRerootRule3SpatialKeyObservable.rule2 leftRelated.1).trans
          (compared.2.2.trans
            (congrArg LocalizedRerootRule3SpatialKeyObservable.rule2 rightRelated.1).symm)

/-- The explicit sixteen-comparison constitutional tie is invariant under the pointwise relation. -/
theorem fourWayConstitutionalTie_iff_of_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    {k0 k1 k2 k3 r0 r1 r2 r3 : input.LocalizedRerootRecursiveRule3SpatialKey}
    (h0 : LocalizedRule3SpatialKeyTopologyEquivalent input k0 r0)
    (h1 : LocalizedRule3SpatialKeyTopologyEquivalent input k1 r1)
    (h2 : LocalizedRule3SpatialKeyTopologyEquivalent input k2 r2)
    (h3 : LocalizedRule3SpatialKeyTopologyEquivalent input k3 r3) :
    input.DeclarativeLocalizedRule3FourWayConstitutionalTie k0 k1 k2 k3 ↔
      input.DeclarativeLocalizedRule3FourWayConstitutionalTie r0 r1 r2 r3 := by
  unfold DeclarativeLocalizedRule3FourWayConstitutionalTie
  repeat' apply and_congr
  all_goals
    first
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h0 h0
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h0 h1
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h0 h2
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h0 h3
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h1 h0
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h1 h1
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h1 h2
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h1 h3
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h2 h0
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h2 h1
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h2 h2
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h2 h3
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h3 h0
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h3 h1
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h3 h2
    | exact input.constitutional_compare_eq_iff_of_topologyEquivalent h3 h3

/-! ## Physical-unit incidence

The resolver's remaining observation dependency is membership of a physical-unit identity in one
ligand key.  The pointwise relation transports exact-pair and complementary-pair incidence. -/

/-- Exact two-key incidence is invariant under the pointwise relation. -/
theorem exactPairIncidence_iff_of_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    (unit : input.LocalizedRule3PhysicalUnitId)
    {first first' second second' outsideFirst outsideFirst' outsideSecond outsideSecond' :
      input.LocalizedRerootRecursiveRule3SpatialKey}
    (firstRelated : LocalizedRule3SpatialKeyTopologyEquivalent input first first')
    (secondRelated : LocalizedRule3SpatialKeyTopologyEquivalent input second second')
    (outsideFirstRelated :
      LocalizedRule3SpatialKeyTopologyEquivalent input outsideFirst outsideFirst')
    (outsideSecondRelated :
      LocalizedRule3SpatialKeyTopologyEquivalent input outsideSecond outsideSecond') :
    input.DeclarativeLocalizedRule3ExactPairIncidence
        unit first second outsideFirst outsideSecond ↔
      input.DeclarativeLocalizedRule3ExactPairIncidence
        unit first' second' outsideFirst' outsideSecond' := by
  unfold DeclarativeLocalizedRule3ExactPairIncidence
  exact and_congr (firstRelated.2 unit)
    (and_congr (secondRelated.2 unit)
      (and_congr (not_congr (outsideFirstRelated.2 unit))
        (not_congr (outsideSecondRelated.2 unit))))

/-- Complementary-pair incidence is invariant under the pointwise relation. -/
theorem complementaryPairIncidence_iff_of_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    (firstUnit secondUnit : input.LocalizedRule3PhysicalUnitId)
    {pairFirst pairFirst' pairSecond pairSecond'
      complementFirst complementFirst' complementSecond complementSecond' :
      input.LocalizedRerootRecursiveRule3SpatialKey}
    (pairFirstRelated :
      LocalizedRule3SpatialKeyTopologyEquivalent input pairFirst pairFirst')
    (pairSecondRelated :
      LocalizedRule3SpatialKeyTopologyEquivalent input pairSecond pairSecond')
    (complementFirstRelated :
      LocalizedRule3SpatialKeyTopologyEquivalent input complementFirst complementFirst')
    (complementSecondRelated :
      LocalizedRule3SpatialKeyTopologyEquivalent input complementSecond complementSecond') :
    input.DeclarativeLocalizedRule3ComplementaryPairIncidence
        firstUnit secondUnit pairFirst pairSecond complementFirst complementSecond ↔
      input.DeclarativeLocalizedRule3ComplementaryPairIncidence
        firstUnit secondUnit pairFirst' pairSecond' complementFirst' complementSecond' := by
  unfold DeclarativeLocalizedRule3ComplementaryPairIncidence
  exact or_congr
    (and_congr
      (input.exactPairIncidence_iff_of_topologyEquivalent firstUnit
        pairFirstRelated pairSecondRelated complementFirstRelated complementSecondRelated)
      (input.exactPairIncidence_iff_of_topologyEquivalent secondUnit
        complementFirstRelated complementSecondRelated pairFirstRelated pairSecondRelated))
    (and_congr
      (input.exactPairIncidence_iff_of_topologyEquivalent secondUnit
        pairFirstRelated pairSecondRelated complementFirstRelated complementSecondRelated)
      (input.exactPairIncidence_iff_of_topologyEquivalent firstUnit
        complementFirstRelated complementSecondRelated pairFirstRelated pairSecondRelated))

/-- A frame whose key list has length other than four can never satisfy the executable matching
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

/-- The complete independent matching relation is invariant under a pointwise related key list. -/
theorem declarativeLocalizedRule3CoupledMatching_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    input.DeclarativeLocalizedRule3CoupledMatching left matching ↔
      input.DeclarativeLocalizedRule3CoupledMatching right matching := by
  by_cases four : left.length = 4
  · obtain ⟨k0, k1, k2, k3, rfl⟩ := List.length_eq_four.mp four
    have frameIff : ∀ unit : input.LocalizedRule3PhysicalUnitId,
        unit ∈ input.localizedRule3FramePhysicalUnits [k0, k1, k2, k3] ↔
          unit ∈ input.localizedRule3FramePhysicalUnits right :=
      fun unit =>
        input.mem_localizedRule3FramePhysicalUnits_iff_of_forall₂
          [k0, k1, k2, k3] right related unit
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
      (input.fourWayConstitutionalTie_iff_of_topologyEquivalent h0 h1 h2 h3) ?_
    cases pairing with
    | pair01_23 =>
        exact input.complementaryPairIncidence_iff_of_topologyEquivalent
          firstUnit secondUnit h0 h1 h2 h3
    | pair02_13 =>
        exact input.complementaryPairIncidence_iff_of_topologyEquivalent
          firstUnit secondUnit h0 h2 h1 h3
    | pair03_12 =>
        exact input.complementaryPairIncidence_iff_of_topologyEquivalent
          firstUnit secondUnit h0 h3 h1 h2
  · have rightLength : right.length ≠ 4 := by
      intro rightFour
      exact four (by
        rw [List.Forall₂.length_eq related]
        exact rightFour)
    exact ⟨
      fun derived =>
        (input.not_declarativeLocalizedRule3CoupledMatching_of_length_ne_four
          left four matching derived).elim,
      fun derived =>
        (input.not_declarativeLocalizedRule3CoupledMatching_of_length_ne_four
          right rightLength matching derived).elim⟩

/-! ## Exhaustive matching search

The executable search enumerates the frame physical-unit universe and filters by the independent
matching relation.  Pointwise related frames therefore run the same membership test over the same
unit universe, and the resulting duplicate-free lists are permutations. -/

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
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    matching ∈ input.localizedRule3CoupledPerfectMatchingsExec left ↔
      matching ∈ input.localizedRule3CoupledPerfectMatchingsExec right := by
  have frame : ∀ unit : input.LocalizedRule3PhysicalUnitId,
      unit ∈ input.localizedRule3FramePhysicalUnits left ↔
        unit ∈ input.localizedRule3FramePhysicalUnits right :=
    fun unit =>
      input.mem_localizedRule3FramePhysicalUnits_iff_of_forall₂ left right related unit
  have derivedIff :=
    input.declarativeLocalizedRule3CoupledMatching_iff_of_forall₂
      left right matching related
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

/-- The two executable perfect-matching lists are permutations of one another. -/
theorem localizedRule3CoupledPerfectMatchingsExec_perm_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    List.Perm
      (input.localizedRule3CoupledPerfectMatchingsExec left)
      (input.localizedRule3CoupledPerfectMatchingsExec right) :=
  perm_of_nodup_of_mem_iff
    (input.localizedRule3CoupledPerfectMatchingsExec_nodup left)
    (input.localizedRule3CoupledPerfectMatchingsExec_nodup right)
    (fun matching =>
      input.mem_localizedRule3CoupledPerfectMatchingsExec_iff_of_forall₂
        left right matching related)

/-- Topology resolution is invariant as a full `Option`: absence, a unique coupled matching, and
refusal are classified identically on pointwise related frames.  A permutation cannot change the
empty/singleton/multiple shape of a list, and a singleton permutation forces the same element. -/
theorem localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    input.localizedRule3CoupledTopologyResolutionExec? left =
      input.localizedRule3CoupledTopologyResolutionExec? right := by
  have permutation :=
    input.localizedRule3CoupledPerfectMatchingsExec_perm_of_forall₂ left right related
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

/-- The original (non-executable) topology resolver is invariant under the same relation. -/
theorem localizedRule3CoupledTopologyResolution?_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right) :
    input.localizedRule3CoupledTopologyResolution? left =
      input.localizedRule3CoupledTopologyResolution? right := by
  rw [← input.localizedRule3CoupledTopologyResolutionExec?_eq_original left,
    ← input.localizedRule3CoupledTopologyResolutionExec?_eq_original right]
  exact input.localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂ left right related

/-! ## Excluded physical units

For a fixed resolved topology the excluded set is the ordinary shared-unit domain, or that domain
with the two retained coupled units removed.  Both operations preserve membership under the
pointwise relation, so the exclusion *set* is determined even when list order is not. -/

/-- For one and the same resolved topology, exclusion membership is invariant. -/
theorem mem_localizedRule3CoupledExcludedPhysicalUnits_iff_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right)
    (resolution : input.LocalizedRule3CoupledTopologyResolution)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left resolution ↔
      unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right resolution := by
  cases resolution with
  | ordinary =>
      simpa using
        input.mem_localizedRule3SharedPhysicalUnits_iff_of_forall₂
          left right related unit
  | coupled matching =>
      rw [input.mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff,
        input.mem_localizedRule3CoupledExcludedPhysicalUnits_coupled_iff,
        input.mem_localizedRule3SharedPhysicalUnits_iff_of_forall₂
          left right related unit]

/-- Exclusions produced by separately evaluated executable resolutions have the same membership:
the resolutions themselves are equal, hence carry the same retained coupled matching. -/
theorem mem_localizedRule3CoupledExcludedPhysicalUnits_congruence
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) left right)
    (leftResolution rightResolution : input.LocalizedRule3CoupledTopologyResolution)
    (leftComputed :
      input.localizedRule3CoupledTopologyResolutionExec? left = some leftResolution)
    (rightComputed :
      input.localizedRule3CoupledTopologyResolutionExec? right = some rightResolution)
    (unit : input.LocalizedRule3PhysicalUnitId) :
    unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits left leftResolution ↔
      unit ∈ input.localizedRule3CoupledExcludedPhysicalUnits right rightResolution := by
  have computed :=
    input.localizedRule3CoupledTopologyResolutionExec?_eq_of_forall₂ left right related
  rw [leftComputed, rightComputed] at computed
  have sameResolution : leftResolution = rightResolution := Option.some.inj computed
  rw [← sameResolution]
  exact
    input.mem_localizedRule3CoupledExcludedPhysicalUnits_iff_of_forall₂
      left right related leftResolution unit

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
