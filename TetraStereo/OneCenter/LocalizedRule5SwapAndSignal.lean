import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace LocalizedRule5SwapAndSignal

/-!
# Swap laws and the exact pseudo signal for the localized compound Rule-5 key

This module proves, over the *actual* definitions in
`TetraStereo.OneCenter.OfficialRuleMajorKey` and
`TetraStereo.OneCenter.CertifiedLocalizedCIPInput`:

* generic antisymmetry (`Ordering.swap`) laws for the sparse entry/layer/layers comparators,
  parameterized by an oriented element comparator;
* the argument-swap law of the prior compound Rules-4b/4c comparator;
* the argument-swap law of each common-reference Rule-5 reading-list comparator;
* the argument-swap law of the through-Rule-5 ordering, and symmetry of its `pseudo` flag;
* the exact characterization of the `pseudo` flag as
  "prior comparator ties, the common-R reading is strict, and the common-S reading disagrees";
* under an explicit cross-reading relation (`MirrorReadings`, which states only addressed
  descriptor equalities between the R and S projections), the S comparison is the swap of the R
  comparison, and the flag reduces to "prior ties and the common-R comparison is strict".

The cross-reading relation is a statement about descriptor data.  It is *not* claimed to be, and
does not construct, a physical mirror/reflection of any molecular graph.  It is index-wise in the
canonical reading order fixed by the preceding compound key: `List.compareLex` is order-sensitive,
so no permutation invariance is asserted here.  A singleton corollary is provided separately.
-/

open CertifiedLocalizedCIPInput

/-! ## Generic sparse comparator orientation and swap laws -/

/-- The sparse entry comparator is oriented whenever the observation comparator is oriented. -/
theorem compareSparseEntry_oriented {α : Type*} (compareObservation : α → α → Ordering)
    [Std.OrientedCmp compareObservation] :
    Std.OrientedCmp (OfficialRuleMajorKey.compareSparseEntry compareObservation) := by
  letI : Std.OrientedCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- The sparse layer comparator is oriented whenever the observation comparator is oriented. -/
theorem compareSparseLayer_oriented {α : Type*} (compareObservation : α → α → Ordering)
    [Std.OrientedCmp compareObservation] :
    Std.OrientedCmp (OfficialRuleMajorKey.compareSparseLayer compareObservation) := by
  haveI : Std.OrientedCmp (OfficialRuleMajorKey.compareSparseEntry compareObservation) :=
    compareSparseEntry_oriented compareObservation
  unfold OfficialRuleMajorKey.compareSparseLayer
  infer_instance

/-- The sparse layers comparator is oriented whenever the observation comparator is oriented. -/
theorem compareSparseLayers_oriented {α : Type*} (compareObservation : α → α → Ordering)
    [Std.OrientedCmp compareObservation] :
    Std.OrientedCmp (OfficialRuleMajorKey.compareSparseLayers compareObservation) := by
  haveI : Std.OrientedCmp (OfficialRuleMajorKey.compareSparseLayer compareObservation) :=
    compareSparseLayer_oriented compareObservation
  unfold OfficialRuleMajorKey.compareSparseLayers
  infer_instance

/-- Element-comparator swap law for addressed sparse entries. -/
theorem compareSparseEntry_eq_swap {α : Type*} (compareObservation : α → α → Ordering)
    [Std.OrientedCmp compareObservation] (left right : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry compareObservation left right =
      (OfficialRuleMajorKey.compareSparseEntry compareObservation right left).swap := by
  haveI : Std.OrientedCmp (OfficialRuleMajorKey.compareSparseEntry compareObservation) :=
    compareSparseEntry_oriented compareObservation
  exact Std.OrientedCmp.eq_swap

/-- Element-comparator swap law for sparse layers. -/
theorem compareSparseLayer_eq_swap {α : Type*} (compareObservation : α → α → Ordering)
    [Std.OrientedCmp compareObservation]
    (left right : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer compareObservation left right =
      (OfficialRuleMajorKey.compareSparseLayer compareObservation right left).swap := by
  haveI : Std.OrientedCmp (OfficialRuleMajorKey.compareSparseLayer compareObservation) :=
    compareSparseLayer_oriented compareObservation
  exact Std.OrientedCmp.eq_swap

/-- Element-comparator swap law for sparse layer lists. -/
theorem compareSparseLayers_eq_swap {α : Type*} (compareObservation : α → α → Ordering)
    [Std.OrientedCmp compareObservation]
    (left right : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation left right =
      (OfficialRuleMajorKey.compareSparseLayers compareObservation right left).swap := by
  haveI : Std.OrientedCmp (OfficialRuleMajorKey.compareSparseLayers compareObservation) :=
    compareSparseLayers_oriented compareObservation
  exact Std.OrientedCmp.eq_swap

/-! ## Generic list algebra used by the common-reference swap -/

/-- A keyed `compareLex` is ordinary `compareLex` of the projected lists. -/
theorem compareLex_byKey_eq {α β : Type*} (f : α → β) (cmp : β → β → Ordering)
    (left right : List α) :
    List.compareLex (Ordering.byKey f cmp) left right =
      List.compareLex cmp (left.map f) (right.map f) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head tail ih =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.compareLex_cons_cons, Ordering.byKey,
            ih rightTail]

/-- Pointwise projected equality out of a right-associated `List.Forall₂` relation. -/
theorem map_eq_of_forall₂ {α β γ : Type*} {R : α → β → Prop}
    (f : α → γ) (g : β → γ)
    (pointwise : ∀ a b, R a b → f a = g b) :
    ∀ {left : List α} {right : List β}, List.Forall₂ R left right →
      left.map f = right.map g
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons head tail => by
      simp only [List.map_cons, pointwise _ _ head,
        map_eq_of_forall₂ f g pointwise tail]

/-- A symmetric homogeneous relation transports across `List.Forall₂` in the opposite order. -/
theorem forall₂_symm {α : Type*} {R : α → α → Prop}
    (symmetric : ∀ a b, R a b → R b a) :
    ∀ {left right : List α}, List.Forall₂ R left right → List.Forall₂ R right left
  | _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, List.Forall₂.cons head tail =>
      List.Forall₂.cons (symmetric _ _ head) (forall₂_symm symmetric tail)

/-! ## The actual compound comparators -/

/-- The prior compound Rules-4b/4c comparator is oriented: exchanging the two keys exchanges
`lt` and `gt`.  This is the `TransCmp` orientation instance of the actual compound comparator. -/
theorem compareLocalizedRerootCompoundRule4bcKeys_eq_swap
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      (input.compareLocalizedRerootCompoundRule4bcKeys right left).swap := by
  letI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
    input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
  exact Std.OrientedCmp.eq_swap

/-- Each common-reference reading-list comparator is oriented. -/
theorem compareLocalizedRerootCompoundRule5Readings_eq_swap
    (input : CertifiedLocalizedCIPInput) (commonReference : RS)
    (left right : List input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundRule5Readings commonReference left right =
      (input.compareLocalizedRerootCompoundRule5Readings commonReference right left).swap := by
  letI : Std.TransCmp
      (input.compareLocalizedRerootCompoundRule5Readings commonReference) :=
    input.compareLocalizedRerootCompoundRule5Readings_transCmp commonReference
  exact Std.OrientedCmp.eq_swap

/-! ## Exact pseudo-signal characterization -/

/-- The `pseudo` flag of the actual through-Rule-5 comparison is true exactly when the prior
compound comparator ties, the common-R reading comparison is strict, and the common-S reading
comparison does not agree with the common-R decision. -/
theorem compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = true ↔
      input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
          Ordering.eq ∧
        input.compareLocalizedRerootCompoundRule5Readings .R
            left.rule5Readings right.rule5Readings ≠ Ordering.eq ∧
          input.compareLocalizedRerootCompoundRule5Readings .S
              left.rule5Readings right.rule5Readings ≠
            input.compareLocalizedRerootCompoundRule5Readings .R
              left.rule5Readings right.rule5Readings := by
  unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5
  generalize priorEq : input.compareLocalizedRerootCompoundRule4bcKeys
    left.prior right.prior = prior
  cases prior with
  | lt => simp
  | gt => simp
  | eq =>
      generalize cmpREq : input.compareLocalizedRerootCompoundRule5Readings
        .R left.rule5Readings right.rule5Readings = cmpR
      generalize cmpSEq : input.compareLocalizedRerootCompoundRule5Readings
        .S left.rule5Readings right.rule5Readings = cmpS
      cases cmpR <;> cases cmpS <;> simp

/-- `Ordering.swap` changes a decision exactly when that decision is strict. -/
theorem ordering_swap_ne_self_iff (ordering : Ordering) :
    ordering.swap ≠ ordering ↔ ordering ≠ Ordering.eq := by
  constructor
  · intro swappedEqual equal
    exact swappedEqual (by simp [equal])
  · intro notEqual swappedEqual
    exact notEqual (Ordering.eq_swap_iff_eq_eq.mp swappedEqual.symm)

/-! ## Explicit cross-reading (mirror-reading) relation

The relation below is purely algebraic descriptor data: it says that, index by index in the
canonical reading order, the left key's common-R addressed descriptor equals the right key's
common-S addressed descriptor and conversely.  It is deliberately *not* a physical reflection of
a molecular graph and it does not assert equality of any comparator outcome.  Because
`List.compareLex` inspects the readings in order, the relation is index-wise rather than up to an
arbitrary permutation; the singleton case is stated separately below.
-/

/-- Cross common-reference addressed descriptor equalities for one pair of readings. -/
def MirrorReading (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule5Reading) : Prop :=
  left.commonR.descriptor = right.commonS.descriptor ∧
    left.commonS.descriptor = right.commonR.descriptor

/-- The same relation, index-wise along the canonical reading list. -/
def MirrorReadings (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule5Reading) : Prop :=
  List.Forall₂ (MirrorReading input) left right

/-- The cross-reading relation is symmetric. -/
theorem MirrorReading.symm {input : CertifiedLocalizedCIPInput}
    {left right : input.LocalizedRerootRule5Reading}
    (mirror : MirrorReading input left right) :
    MirrorReading input right left :=
  ⟨mirror.2.symm, mirror.1.symm⟩

/-- The list-level cross-reading relation is symmetric. -/
theorem MirrorReadings.symm {input : CertifiedLocalizedCIPInput}
    {left right : List input.LocalizedRerootRule5Reading}
    (mirror : MirrorReadings input left right) :
    MirrorReadings input right left :=
  forall₂_symm (fun _ _ h => MirrorReading.symm h) mirror

/-- Under the explicit cross-reading relation, comparing the two reading lists under the common
reference `.S` is exactly the `Ordering.swap` of comparing them under `.R`. -/
theorem compareLocalizedRerootCompoundRule5Readings_S_eq_swap_of_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule5Reading)
    (mirror : MirrorReadings input left right) :
    input.compareLocalizedRerootCompoundRule5Readings .S left right =
      (input.compareLocalizedRerootCompoundRule5Readings .R left right).swap := by
  have eqRS : left.map (input.localizedRerootRule5Descriptor .S) =
      right.map (input.localizedRerootRule5Descriptor .R) :=
    map_eq_of_forall₂ (input.localizedRerootRule5Descriptor .S)
      (input.localizedRerootRule5Descriptor .R) (fun _ _ h => h.2) mirror
  have mirrorSymm : MirrorReadings input right left := MirrorReadings.symm mirror
  have eqSR : right.map (input.localizedRerootRule5Descriptor .S) =
      left.map (input.localizedRerootRule5Descriptor .R) :=
    map_eq_of_forall₂ (input.localizedRerootRule5Descriptor .S)
      (input.localizedRerootRule5Descriptor .R) (fun _ _ h => h.2) mirrorSymm
  have hS := compareLex_byKey_eq (input.localizedRerootRule5Descriptor .S)
    (OfficialRuleMajorKey.compareSparseLayers
      CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority) left right
  have hR := compareLex_byKey_eq (input.localizedRerootRule5Descriptor .R)
    (OfficialRuleMajorKey.compareSparseLayers
      CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority) right left
  calc
    input.compareLocalizedRerootCompoundRule5Readings .S left right
        = List.compareLex
            (OfficialRuleMajorKey.compareSparseLayers
              CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority)
            (left.map (input.localizedRerootRule5Descriptor .S))
            (right.map (input.localizedRerootRule5Descriptor .S)) := hS
    _ = List.compareLex
            (OfficialRuleMajorKey.compareSparseLayers
              CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority)
            (right.map (input.localizedRerootRule5Descriptor .R))
            (left.map (input.localizedRerootRule5Descriptor .R)) := by
          rw [eqRS, eqSR]
    _ = input.compareLocalizedRerootCompoundRule5Readings .R right left := hR.symm
    _ = (input.compareLocalizedRerootCompoundRule5Readings .R left right).swap := by
          have orientation :=
            compareLocalizedRerootCompoundRule5Readings_eq_swap input .R left right
          rw [orientation, Ordering.swap_swap]

/-- Singleton form of the common-reference swap: a single reading pair needs only the two cross
addressed descriptor equalities. -/
theorem compareLocalizedRerootCompoundRule5Readings_singleton_S_eq_swap_of_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule5Reading)
    (crossRS : left.commonR.descriptor = right.commonS.descriptor)
    (crossSR : left.commonS.descriptor = right.commonR.descriptor) :
    input.compareLocalizedRerootCompoundRule5Readings .S [left] [right] =
      (input.compareLocalizedRerootCompoundRule5Readings .R [left] [right]).swap :=
  compareLocalizedRerootCompoundRule5Readings_S_eq_swap_of_mirror input [left] [right]
    (List.Forall₂.cons ⟨crossRS, crossSR⟩ List.Forall₂.nil)

/-- Under the explicit cross-reading relation the `pseudo` signal is true exactly when the prior
compound comparator ties and the common-R comparison is strict.  No chemical or physical mirror
hypothesis is used beyond the stated descriptor equations. -/
theorem compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (mirror : MirrorReadings input left.rule5Readings right.rule5Readings) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = true ↔
      input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
          Ordering.eq ∧
        input.compareLocalizedRerootCompoundRule5Readings .R
            left.rule5Readings right.rule5Readings ≠ Ordering.eq := by
  rw [compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff,
    compareLocalizedRerootCompoundRule5Readings_S_eq_swap_of_mirror input
      left.rule5Readings right.rule5Readings mirror,
    ordering_swap_ne_self_iff]
  constructor
  · rintro ⟨priorTie, strict, _⟩
    exact ⟨priorTie, strict⟩
  · rintro ⟨priorTie, strict⟩
    exact ⟨priorTie, strict, strict⟩

/-- Prior-tie specialization: after a complete prior tie, the flag is exactly the strictness of
the common-R reading comparison. -/
theorem compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror_of_prior_tie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (mirror : MirrorReadings input left.rule5Readings right.rule5Readings)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = true ↔
      input.compareLocalizedRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings ≠ Ordering.eq := by
  rw [compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror
    input left right mirror]
  exact ⟨fun matched => matched.2, fun strict => ⟨priorTie, strict⟩⟩

/-! ## Swap laws of the actual through-Rule-5 decision -/

/-- Exchanging the two keys swaps the through-Rule-5 ordering decision.  The proof uses only the
orientation of the actual prior compound comparator and of the actual common-R reading
comparator; no reading-list relation is needed for the ordering. -/
theorem compareLocalizedRerootCompoundThroughRule5_ordering_eq_swap
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key) :
    (input.compareLocalizedRerootCompoundThroughRule5 right left).ordering =
      (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering.swap := by
  unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5
  generalize hLR : input.compareLocalizedRerootCompoundRule4bcKeys
    left.prior right.prior = priorLeftRight
  generalize hRL : input.compareLocalizedRerootCompoundRule4bcKeys
    right.prior left.prior = priorRightLeft
  have priorSwap : priorLeftRight = priorRightLeft.swap := by
    rw [← hLR, ← hRL]
    exact compareLocalizedRerootCompoundRule4bcKeys_eq_swap input
      left.prior right.prior
  have priorRightLeftEq : priorRightLeft = priorLeftRight.swap := by
    have swapped := congrArg Ordering.swap priorSwap
    simpa using swapped.symm
  generalize hRR : input.compareLocalizedRerootCompoundRule5Readings .R
    right.rule5Readings left.rule5Readings = readingRightLeft
  generalize hLRR : input.compareLocalizedRerootCompoundRule5Readings .R
    left.rule5Readings right.rule5Readings = readingLeftRight
  have readingSwap : readingLeftRight = readingRightLeft.swap := by
    rw [← hLRR, ← hRR]
    exact compareLocalizedRerootCompoundRule5Readings_eq_swap input .R
      left.rule5Readings right.rule5Readings
  have readingRightLeftEq : readingRightLeft = readingLeftRight.swap := by
    have swapped := congrArg Ordering.swap readingSwap
    simpa using swapped.symm
  cases priorLeftRight with
  | lt => simp [priorRightLeftEq]
  | gt => simp [priorRightLeftEq]
  | eq =>
      cases readingLeftRight with
      | lt => simp [priorRightLeftEq, readingRightLeftEq]
      | gt => simp [priorRightLeftEq, readingRightLeftEq]
      | eq => simp [priorRightLeftEq, readingRightLeftEq]

/-- The `pseudo` flag is symmetric under exchange of the two keys: it records a disagreement
between the two common-reference directions, and exchanging the keys swaps both directions. -/
theorem compareLocalizedRerootCompoundThroughRule5_pseudo_eq_swap
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key) :
    (input.compareLocalizedRerootCompoundThroughRule5 right left).pseudo =
      (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo := by
  unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5
  generalize hLR : input.compareLocalizedRerootCompoundRule4bcKeys
    left.prior right.prior = priorLeftRight
  generalize hRL : input.compareLocalizedRerootCompoundRule4bcKeys
    right.prior left.prior = priorRightLeft
  have priorSwap : priorLeftRight = priorRightLeft.swap := by
    rw [← hLR, ← hRL]
    exact compareLocalizedRerootCompoundRule4bcKeys_eq_swap input
      left.prior right.prior
  have priorRightLeftEq : priorRightLeft = priorLeftRight.swap := by
    have swapped := congrArg Ordering.swap priorSwap
    simpa using swapped.symm
  generalize hRR : input.compareLocalizedRerootCompoundRule5Readings .R
    right.rule5Readings left.rule5Readings = readingRightLeft
  generalize hLRR : input.compareLocalizedRerootCompoundRule5Readings .R
    left.rule5Readings right.rule5Readings = readingLeftRight
  have readingSwap : readingLeftRight = readingRightLeft.swap := by
    rw [← hLRR, ← hRR]
    exact compareLocalizedRerootCompoundRule5Readings_eq_swap input .R
      left.rule5Readings right.rule5Readings
  have readingRightLeftEq : readingRightLeft = readingLeftRight.swap := by
    have swapped := congrArg Ordering.swap readingSwap
    simpa using swapped.symm
  generalize hSSR : input.compareLocalizedRerootCompoundRule5Readings .S
    right.rule5Readings left.rule5Readings = sensorRightLeft
  generalize hSLR : input.compareLocalizedRerootCompoundRule5Readings .S
    left.rule5Readings right.rule5Readings = sensorLeftRight
  have sensorSwap : sensorLeftRight = sensorRightLeft.swap := by
    rw [← hSLR, ← hSSR]
    exact compareLocalizedRerootCompoundRule5Readings_eq_swap input .S
      left.rule5Readings right.rule5Readings
  have sensorRightLeftEq : sensorRightLeft = sensorLeftRight.swap := by
    have swapped := congrArg Ordering.swap sensorSwap
    simpa using swapped.symm
  cases priorLeftRight with
  | lt => simp [priorRightLeftEq]
  | gt => simp [priorRightLeftEq]
  | eq =>
      cases readingLeftRight <;> cases sensorLeftRight <;>
        simp [priorRightLeftEq, readingRightLeftEq, sensorRightLeftEq] <;>
        decide

end LocalizedRule5SwapAndSignal
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareSparseEntry_oriented
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareSparseLayer_oriented
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareSparseLayers_oriented
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareSparseEntry_eq_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareSparseLayer_eq_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareSparseLayers_eq_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLex_byKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.map_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.forall₂_symm
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundRule4bcKeys_eq_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundRule5Readings_eq_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.ordering_swap_ne_self_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.MirrorReading
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.MirrorReadings
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.MirrorReading.symm
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.MirrorReadings.symm
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundRule5Readings_S_eq_swap_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundRule5Readings_singleton_S_eq_swap_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror_of_prior_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_ordering_eq_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_swap
