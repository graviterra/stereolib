import TetraStereo.OneCenter.LocalizedActualOrderedRootEightRuleConnection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The root's declarative descriptor judgment at a multi-reference root

The eight-rule comparison connection (`LocalizedActualOrderedRootEightRuleConnection`) feeds the
sorted-order and orientation conclusion of the ordered Rule-5 root theorem
(`orderedReferenceState_top_eq_classify_physical_rule5`).  For an arbitrary physical centre setup
with pairwise properly distinguishable branches and nondegenerate canonical root coordinates:

* `orderedReferenceState_top_descriptorJudgment` — the ordered evaluator's own fixed point at the
  centre is `classifyTetrahedralRSPseudo rs count`, where
  - `rsDescriptor rs` satisfies the specialized problem's declarative `DescriptorJudgment`: a
    complete ranking of the four ligands by declarative `Problem.Higher` (every pair decided by the
    first decisive rule among `1a … 5`) whose orientation judgment
    (`geometricOrientation`: the oriented-volume reading of the ligand atoms' points in ranking
    order) is `rs`;
  - it is the **only** descriptor with a declarative judgment (`descriptorJudgment_unique`:
    declarative rankings are unique, and the orientation judgment is functional);
  - `count` is the declarative Rule-5 pair count (`declarativeRule5PairCount`: the unordered pairs
    of ligands on which every rule before Rule 5 ties), equal to the independent physical
    enantiomorphic pair count (`declarativeRule5PairCount_eq_physical`).

The orientation judgment of `Problem` sees a ranking, not the descriptor map, so the
pseudoasymmetric case is stated through the declarative Rule-5 pair count rather than inside
`orientationJudgment`.  This is the root's judgment; it is not a whole-molecule `CIPSpec` fixed
point and it does not cover rings.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP

noncomputable section
open scoped Classical

namespace CertifiedLocalizedCIPInput

/-- The uppercase descriptor named by an `R/S` reading. -/
def rsDescriptor : RS → Descriptor
  | .R => .R
  | .S => .S

theorem rsDescriptor_injective {a b : RS} (h : rsDescriptor a = rsDescriptor b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- **The geometric orientation judgment**: the oriented-volume reading of the four ligand atoms'
points listed in ranking order. -/
def geometricOrientation (input : CertifiedLocalizedCIPInput) :
    DetectedOccurrence input.moleculeGraph → Equiv.Perm (Fin 4) → Descriptor → Prop :=
  fun unit ranking descriptor =>
    ∃ (points : Fin 4 → CartesianPoint3) (rs : RS),
      (∀ k, input.spatialPointAt? (input.localizedDetectedFrame.ligand unit k) = some (points k)) ∧
        RationalTetrahedralDescriptor ((List.finRange 4).map fun k => points (ranking k)) rs ∧
        descriptor = rsDescriptor rs

theorem rationalTetrahedralDescriptor_unique {points : List CartesianPoint3} {rs rs' : RS}
    (h : RationalTetrahedralDescriptor points rs) (h' : RationalTetrahedralDescriptor points rs') :
    rs = rs' := by
  obtain ⟨a, b, c, d, hp, hs⟩ := h
  obtain ⟨a', b', c', d', hp', hs'⟩ := h'
  rw [hp] at hp'
  simp only [List.cons.injEq, and_true] at hp'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hp'
  cases rs <;> cases rs'
  · rfl
  · exact (lt_asymm hs hs').elim
  · exact (lt_asymm hs' hs).elim
  · rfl

/-- The geometric orientation judgment is functional. -/
theorem geometricOrientation_functional (input : CertifiedLocalizedCIPInput)
    {unit : DetectedOccurrence input.moleculeGraph} {ranking : Equiv.Perm (Fin 4)}
    {d d' : Descriptor} (h : input.geometricOrientation unit ranking d)
    (h' : input.geometricOrientation unit ranking d') : d = d' := by
  obtain ⟨points, rs, hpts, hrs, rfl⟩ := h
  obtain ⟨points', rs', hpts', hrs', rfl⟩ := h'
  have hp : points = points' := funext fun k => Option.some.inj ((hpts k).symm.trans (hpts' k))
  subst hp
  rw [rationalTetrahedralDescriptor_unique hrs hrs']

end CertifiedLocalizedCIPInput

/-- A strictly monotone self-map of `Fin 4` is the identity. -/
theorem strictMono_fin4_eq (f : Fin 4 → Fin 4) (h : ∀ a b, a < b → f a < f b) (a : Fin 4) :
    f a = a := by
  have h01 := h 0 1 (by decide)
  have h12 := h 1 2 (by decide)
  have h23 := h 2 3 (by decide)
  have b3 := (f 3).isLt
  rw [Fin.lt_def] at h01 h12 h23
  fin_cases a <;> apply Fin.ext <;> simp <;> omega

namespace Rule4aTableBridge
namespace ActualCentrePhysicalSetup

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open RootedTetrahedralBranchSymmetry
open EightRuleAssembly

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The specialized problem with the geometric orientation judgment. -/
abbrev geoProblem := declProblem (input := input) input.certified.geometricOrientation

theorem ordering_eq_prior_then_c5 (ℓ m : Fin 4) :
    (S.orderedRootComparison ℓ m).ordering =
      (input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
        (input.certified.outcomeOrdered (S.slotKey m).prior)).then (S.c5 ℓ m) := by
  unfold orderedRootComparison
  rw [compareLocalizedRerootCompoundThroughRule5_ordering]
  rfl

section Distinct

variable (distinct : ∀ i j : Fin 4, i ≠ j →
  ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
include distinct

/-- Declarative strict priority is asymmetric. -/
theorem higher_asymm {x y : Fin 4}
    (hxy : (geoProblem (input := input)).Higher (actualReferenceDescriptorMap input) S.declUnit x y)
    (hyx : (geoProblem (input := input)).Higher (actualReferenceDescriptorMap input) S.declUnit y x) : False := by
  have h1 := (S.ordering_eq_gt_iff_higher _ distinct x y).2 hxy
  have h2 := (S.ordering_eq_lt_iff_higher _ distinct x y).2 hyx
  rw [h1] at h2
  cases h2

/-- **Declarative rankings are unique.** -/
theorem ranks_unique {ranking ranking' : Equiv.Perm (Fin 4)}
    (h : (geoProblem (input := input)).Ranks (actualReferenceDescriptorMap input) S.declUnit ranking)
    (h' : (geoProblem (input := input)).Ranks (actualReferenceDescriptorMap input) S.declUnit ranking') :
    ranking = ranking' := by
  have hmono : ∀ a b, a < b → (ranking'.symm (ranking a)) < (ranking'.symm (ranking b)) := by
    intro a b hab
    by_contra hnot
    have hne : ranking'.symm (ranking a) ≠ ranking'.symm (ranking b) := fun he =>
      (ne_of_lt hab) (ranking.injective (ranking'.symm.injective he))
    have hlt : ranking'.symm (ranking b) < ranking'.symm (ranking a) :=
      lt_of_le_of_ne (not_lt.1 hnot) (Ne.symm hne)
    have hrev := h' _ _ hlt
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hrev
    exact S.higher_asymm distinct (h a b hab) hrev
  ext a
  have := strictMono_fin4_eq (fun k => ranking'.symm (ranking k)) hmono a
  have h2 := congrArg ranking' this
  rw [Equiv.apply_symm_apply] at h2
  rw [h2]

/-- **Rule 5 is reached exactly at the ordered prior ties.** -/
theorem earlierRulesTie5_iff (ℓ m : Fin 4) :
    (geoProblem (input := input)).EarlierRulesTie (actualReferenceDescriptorMap input)
        .rule5EnantiomorphicDescriptor S.declUnit ℓ m ↔
      priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot ℓ)
        (S.slot m) := by
  have hchar := S.characterizes input.certified.geometricOrientation distinct ℓ m
  constructor
  · intro h
    have hd := prefix_of_ruleOutcome hchar (by decide) h
    show input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
      (input.certified.outcomeOrdered (S.slotKey m).prior) = .eq
    have e1 : S.c1a ℓ m = .eq := hd .rule1aAtomicNumber (before_of_rank (by decide))
    have e2 : S.c1b ℓ m = .eq := hd .rule1bDuplicateNodeProximity (before_of_rank (by decide))
    have e3 : S.c2 ℓ m = .eq := hd .rule2AtomicMass (before_of_rank (by decide))
    have e4 : S.cdesc ℓ m = .eq := hd .rule4aStereogenicUnitKind (before_of_rank (by decide))
    have e5 : S.c4b ℓ m = .eq := hd .rule4bLikeUnlikeDescriptorPairs (before_of_rank (by decide))
    rw [S.prior_compare_eq ℓ m, e1, e2, e3, e4, e5]
    rfl
  · intro h
    apply prefix_of_d hchar (by decide)
    have h' : input.certified.compareLocalizedRerootCompoundRule4bcKeys
        (input.certified.outcomeOrdered (S.slotKey ℓ).prior)
        (input.certified.outcomeOrdered (S.slotKey m).prior) = .eq := h
    rw [S.prior_compare_eq ℓ m, then_eq_eq_iff, then_eq_eq_iff, then_eq_eq_iff,
      then_eq_eq_iff] at h'
    obtain ⟨⟨⟨h1a, h1b, h2⟩, h4a⟩, h4b⟩ := h'
    intro e he
    cases e with
    | rule1aAtomicNumber => exact h1a
    | rule1bDuplicateNodeProximity => exact h1b
    | rule2AtomicMass => exact h2
    | rule3DoubleBondGeometry => rfl
    | rule4aStereogenicUnitKind => exact h4a
    | rule4bLikeUnlikeDescriptorPairs => exact h4b
    | rule4cPseudoasymmetricDescriptor => rfl
    | rule5EnantiomorphicDescriptor => exact absurd he (not_before_of_rank (by decide))
    | rule6ReferencePromotion => exact absurd he (not_before_of_rank (by decide))

/-- **The declarative Rule-5 pair count**: unordered pairs of distinct ligands on which every
rule before Rule 5 ties. -/
def declarativeRule5PairCount : ℕ :=
  sourceEnantiomorphicPairCount fun ℓ m =>
    ℓ ≠ m ∧ (geoProblem (input := input)).EarlierRulesTie (actualReferenceDescriptorMap input)
      .rule5EnantiomorphicDescriptor S.declUnit ℓ m

theorem declarativeRule5PairCount_eq_physical :
    S.declarativeRule5PairCount =
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule S.cfg S.c := by
  rw [← S.orderedPriorTieCount_eq_physical distinct]
  have hsymm : ∀ i j : Fin 4,
      compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) i j →
        compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey) j i :=
    fun i j h => (S.orderedPriorTie_iff_enantiomorphic distinct j i).2
      (enantiomorphic_symm _ _ _ ((S.orderedPriorTie_iff_enantiomorphic distinct i j).1 h))
  rw [← sourceEnantiomorphicPairCount_perm _ hsymm S.slotEquiv]
  apply sourceEnantiomorphicPairCount_congr_of_forall
  intro ℓ m
  rw [S.earlierRulesTie5_iff distinct ℓ m]
  constructor
  · rintro ⟨hne, htie⟩
    exact ⟨S.slot_injective.ne hne, htie⟩
  · rintro ⟨hne, htie⟩
    exact ⟨fun h => hne (congrArg S.slot h), htie⟩

/-- A pair placed in sorted order by the root theorem is strictly ordered by the evaluator. -/
theorem ordering_gt_of_sorted {ℓ m : Fin 4} (hne : ℓ ≠ m)
    (hindep : S.independentKey ℓ ≠ S.independentKey m → S.independentKey m < S.independentKey ℓ)
    (hrule5 : compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey)
        (S.slot ℓ) (S.slot m) →
      ∀ (u : input.certified.LocalizedRerootRule5Reading) tailU
        (v : input.certified.LocalizedRerootRule5Reading) tailV,
        (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings = u :: tailU →
        (orderedKeys input.certified S.frameKey (S.slot m)).rule5Readings = v :: tailV →
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          u.commonR.descriptor v.commonR.descriptor = .gt) :
    (S.orderedRootComparison ℓ m).ordering = .gt := by
  by_cases hk : S.independentKey ℓ = S.independentKey m
  · have hic := (S.independentCompare_eq_eq_iff ℓ m).2 hk
    unfold independentCompare at hic
    rw [then_eq_eq_iff] at hic
    have hprior := (S.rule4bc_ordered_eq_signatureCompare hic.1).trans hic.2
    have tie : priorKeyTie input.certified (orderedKeys input.certified S.frameKey) (S.slot ℓ)
        (S.slot m) := hprior
    obtain ⟨u, tailU, hu⟩ := S.exists_head ℓ
    obtain ⟨v, tailV, hv⟩ := S.exists_head m
    have hc5 : S.c5 ℓ m = .gt := (S.c5_eq_head distinct hne tie hu hv).trans
      (hrule5 ⟨S.slot_injective.ne hne, tie⟩ u tailU v tailV hu hv)
    rw [S.ordering_eq_prior_then_c5, hprior, hc5]
    rfl
  · have hlt := hindep hk
    have hne' : S.independentCompare ℓ m ≠ .eq := fun h => hk ((S.independentCompare_eq_eq_iff ℓ m).1 h)
    have hnlt : S.independentCompare ℓ m ≠ .lt := fun h =>
      lt_asymm ((S.independentCompare_eq_lt_iff ℓ m).1 h) hlt
    rw [S.orderedRootComparison_of_independent_ne hne']
    show S.independentCompare ℓ m = .gt
    cases hc : S.independentCompare ℓ m with
    | lt => exact absurd hc hnlt
    | eq => exact absurd hc hne'
    | gt => rfl

/-- **The root's declarative descriptor judgment.**  The ordered evaluator's fixed point at the
centre is the pseudo-aware classification of the unique descriptor licensed by the specialized
problem's declarative `DescriptorJudgment`, with the declarative Rule-5 pair count. -/
theorem orderedReferenceState_top_descriptorJudgment
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ rs : RS,
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
          some (classifyTetrahedralRSPseudo rs (S.declarativeRule5PairCount)) ∧
        (geoProblem (input := input)).DescriptorJudgment (actualReferenceDescriptorMap input) S.declUnit
          (rsDescriptor rs) ∧
        ∀ descriptor, (geoProblem (input := input)).DescriptorJudgment (actualReferenceDescriptorMap input)
          S.declUnit descriptor → descriptor = rsDescriptor rs := by
  obtain ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, rational, _, _, indep, rule5⟩ :=
    S.orderedReferenceState_top_eq_classify_physical_rule5 distinct coordinates
  -- the ligand-indexed sorted list and its ranking
  set L := tracked.highestFirst.map S.slotEquiv.symm with hLdef
  have hLperm : L.Perm (List.finRange 4) :=
    (perm.map _).trans (Rule4aTableBridge.finRange_map_perm _)
  have nd : L.Nodup := hLperm.nodup_iff.2 (List.nodup_finRange 4)
  have hlen : L.length = 4 := by rw [hLperm.length_eq, List.length_finRange]
  have hmem : ∀ x, x ∈ L := fun x => hLperm.mem_iff.2 (List.mem_finRange x)
  let ranking : Equiv.Perm (Fin 4) :=
    (finCongr hlen.symm).trans (List.Nodup.getEquivOfForallMemList L nd hmem)
  have ranking_apply : ∀ k, ranking k = L.get (Fin.cast hlen.symm k) := fun _ => rfl
  -- the pairwise order facts on ligand indices
  have hL : L.Pairwise fun ℓ m =>
      (S.independentKey ℓ ≠ S.independentKey m → S.independentKey m < S.independentKey ℓ) ∧
        (compoundPriorTieRelation input.certified (orderedKeys input.certified S.frameKey)
            (S.slot ℓ) (S.slot m) →
          ∀ (u : input.certified.LocalizedRerootRule5Reading) tailU
            (v : input.certified.LocalizedRerootRule5Reading) tailV,
            (orderedKeys input.certified S.frameKey (S.slot ℓ)).rule5Readings = u :: tailU →
            (orderedKeys input.certified S.frameKey (S.slot m)).rule5Readings = v :: tailV →
            OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
              u.commonR.descriptor v.commonR.descriptor = .gt) := by
    refine List.Pairwise.and indep ?_
    rw [List.pairwise_map]
    refine rule5.imp ?_
    intro i j h
    rwa [S.slot_slotEquiv_symm, S.slot_slotEquiv_symm]
  -- declarative ranking
  have hranks : (geoProblem (input := input)).Ranks (actualReferenceDescriptorMap input) S.declUnit ranking := by
    intro a b hab
    have hab' : Fin.cast hlen.symm a < Fin.cast hlen.symm b := hab
    obtain ⟨hindep, hrule5⟩ := List.pairwise_iff_get.1 hL _ _ hab'
    have hne : ranking a ≠ ranking b := fun h => (ne_of_lt hab) (ranking.injective h)
    rw [ranking_apply, ranking_apply] at hne
    rw [ranking_apply, ranking_apply]
    exact (S.ordering_eq_gt_iff_higher _ distinct _ _).1
      (S.ordering_gt_of_sorted distinct hne hindep hrule5)
  -- the orientation
  have hmapR : (List.finRange 4).map ranking = L := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_finRange, hlen]
    · intro n h1 h2
      rw [List.getElem_map, List.getElem_finRange, ranking_apply]
      rfl
  have hpoints : (List.finRange 4).map (fun k => pointsAt (S.slot (ranking k))) =
      tracked.highestFirst.map pointsAt := by
    have : (fun k => pointsAt (S.slot (ranking k))) = (fun ℓ => pointsAt (S.slot ℓ)) ∘ ranking :=
      rfl
    rw [this, ← List.map_map, hmapR, hLdef, List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, S.slot_slotEquiv_symm]
  have horient : input.certified.geometricOrientation S.declUnit ranking
      (rsDescriptor normalizedRS) := by
    refine ⟨fun k => pointsAt (S.slot k), normalizedRS, ?_, ?_, rfl⟩
    · intro k
      rw [localizedDetectedFrame_ligand_topUnit]
      have h := spatial (S.slot k)
      rw [S.spatialPoint_cursorAt, S.slotEquiv_symm_slot] at h
      exact h
    · rw [hpoints]
      exact rational
  refine ⟨normalizedRS, ?_, ⟨ranking, hranks, horient⟩, ?_⟩
  · rw [stateEq, S.declarativeRule5PairCount_eq_physical distinct]
  · rintro descriptor ⟨ranking', hranks', horient'⟩
    have hr := S.ranks_unique distinct hranks' hranks
    subst hr
    exact input.certified.geometricOrientation_functional horient' horient

end Distinct

end ActualCentrePhysicalSetup
end Rule4aTableBridge

end

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.geometricOrientation_functional
assert_kernel_only TetraStereo.OneCenter.strictMono_fin4_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ranks_unique
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.earlierRulesTie5_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.declarativeRule5PairCount_eq_physical
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ordering_gt_of_sorted
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_descriptorJudgment
