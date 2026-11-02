import TetraStereo.OneCenter.P93MolecularFullereneHelicalNumberingPath

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

/-!
# Fu-3.1 proper-axis order and axis-end-kind preference

Fu-3.1.1 examines proper rotation axes from highest order downward and stops as soon as at least
one contiguous helical pathway exists.  Fu-3.1.2 then prefers a ring end to a bond end and a bond
end to an atom end.  This module applies those two global preference layers to the exact finite
axis/path universe established previously.

Axis order is carried with a proof that it is the maximum order of every admitted rotation grouped
under the same invariant end-cell set.  Maximum selection is performed only over axes that have an
eligible contiguous helix, so a higher-order axis without such a path cannot incorrectly suppress
the lower-order axis required by Fu-3.1.1.
-/

/-! ## All eligible axis/path pairs with exact axis order -/

/-- A Fu-3.1.1 axis/end/path candidate together with the independently derived order of its grouped
proper rotation axis. -/
structure MolecularFullereneAxialContiguousHelicalNumberingCandidate where
  axis : MolecularFullereneProperRotationAxis
  axisOrder : ℕ
  axisCandidate : MolecularFullereneAxisContiguousHelicalNumberingCandidate

/-- Independent meaning of one order-annotated axial helix candidate. -/
structure MolecularFullereneAxialContiguousHelicalNumberingJudgment
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) : Prop where
  axisOrderExact : molecularFullereneProperRotationAxisOrder?
    molecule input candidate.axis = some candidate.axisOrder
  axisCandidateJudged : MolecularFullereneAxisContiguousHelicalNumberingJudgment
    molecule input candidate.axis candidate.axisCandidate

noncomputable instance molecularFullereneAxialContiguousHelicalNumberingJudgmentDecidable
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    Decidable (MolecularFullereneAxialContiguousHelicalNumberingJudgment
      molecule input candidate) :=
  Classical.propDecidable _

/-- Every annotated eligible-axis order is nontrivial. -/
theorem MolecularFullereneAxialContiguousHelicalNumberingJudgment.axisOrder_gt_one
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate)
    (judged : MolecularFullereneAxialContiguousHelicalNumberingJudgment
      molecule input candidate) :
    1 < candidate.axisOrder :=
  molecularFullereneProperRotationAxisOrder?_gt_one_of_eq_some
    molecule input candidate.axis candidate.axisOrder judged.axisOrderExact

/-- Exhaust every grouped proper axis, derive its exact order, and pair it with every eligible
contiguous helix at every invariant end. -/
noncomputable def molecularFullereneAxialContiguousHelicalNumberingCandidates
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    List MolecularFullereneAxialContiguousHelicalNumberingCandidate :=
  (molecularFullereneProperRotationAxes molecule input).toList.flatMap fun axis =>
    match molecularFullereneProperRotationAxisOrder? molecule input axis with
    | none => []
    | some axisOrder =>
        (molecularFullereneAxisContiguousHelicalNumberingCandidates
          molecule input axis).map fun axisCandidate =>
            { axis := axis
              axisOrder := axisOrder
              axisCandidate := axisCandidate }

/-- The global finite family contains exactly the independently judged order/axis/end/path
quadruples. -/
@[simp] theorem mem_molecularFullereneAxialContiguousHelicalNumberingCandidates_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    candidate ∈ molecularFullereneAxialContiguousHelicalNumberingCandidates molecule input ↔
      MolecularFullereneAxialContiguousHelicalNumberingJudgment
        molecule input candidate := by
  classical
  constructor
  · intro present
    rcases List.mem_flatMap.mp present with ⟨axis, _axisPresent, generatedPresent⟩
    cases orderEq : molecularFullereneProperRotationAxisOrder? molecule input axis with
    | none => simp [orderEq] at generatedPresent
    | some axisOrder =>
        have mappedPresent : candidate ∈
            (molecularFullereneAxisContiguousHelicalNumberingCandidates
              molecule input axis).map fun axisCandidate =>
                { axis := axis
                  axisOrder := axisOrder
                  axisCandidate := axisCandidate } := by
          simpa [orderEq] using generatedPresent
        rcases List.mem_map.mp mappedPresent with
          ⟨axisCandidate, axisCandidatePresent, candidateEq⟩
        subst candidate
        exact
          { axisOrderExact := orderEq
            axisCandidateJudged :=
              (mem_molecularFullereneAxisContiguousHelicalNumberingCandidates_iff
                molecule input axis axisCandidate).mp axisCandidatePresent }
  · intro judged
    apply List.mem_flatMap.mpr
    refine ⟨candidate.axis, ?_, ?_⟩
    · simpa using judged.axisCandidateJudged.axisPresent
    · rw [judged.axisOrderExact]
      apply List.mem_map.mpr
      refine ⟨candidate.axisCandidate, ?_, ?_⟩
      · exact (mem_molecularFullereneAxisContiguousHelicalNumberingCandidates_iff
          molecule input candidate.axis candidate.axisCandidate).mpr
            judged.axisCandidateJudged
      · cases candidate
        rfl

/-! ## Highest eligible proper-axis order (Fu-3.1.1) -/

/-- Orders represented by at least one eligible contiguous axial helix. -/
noncomputable def molecularFullereneEligibleHelicalAxisOrders
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) : Finset ℕ :=
  ((molecularFullereneAxialContiguousHelicalNumberingCandidates molecule input).map
    MolecularFullereneAxialContiguousHelicalNumberingCandidate.axisOrder).toFinset

/-- Exact eligible-order membership. -/
@[simp] theorem mem_molecularFullereneEligibleHelicalAxisOrders_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axisOrder : ℕ) :
    axisOrder ∈ molecularFullereneEligibleHelicalAxisOrders molecule input ↔
      ∃ candidate,
        MolecularFullereneAxialContiguousHelicalNumberingJudgment
          molecule input candidate ∧
        candidate.axisOrder = axisOrder := by
  classical
  constructor
  · intro present
    have mappedPresent : axisOrder ∈
        (molecularFullereneAxialContiguousHelicalNumberingCandidates molecule input).map
          MolecularFullereneAxialContiguousHelicalNumberingCandidate.axisOrder :=
      List.mem_toFinset.mp (by
        simpa [molecularFullereneEligibleHelicalAxisOrders] using present)
    rcases List.mem_map.mp mappedPresent with ⟨candidate, candidatePresent, orderEq⟩
    exact ⟨candidate,
      (mem_molecularFullereneAxialContiguousHelicalNumberingCandidates_iff
        molecule input candidate).mp candidatePresent,
      orderEq⟩
  · rintro ⟨candidate, judged, orderEq⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨candidate,
      (mem_molecularFullereneAxialContiguousHelicalNumberingCandidates_iff
        molecule input candidate).mpr judged,
      orderEq⟩

/-- Maximum of a finite natural-number set, with refusal on the empty set. -/
private noncomputable def finiteNatMaximum? (values : Finset ℕ) : Option ℕ :=
  if nonempty : values.Nonempty then
    some (values.max' nonempty)
  else
    none

private theorem finiteNatMaximum?_eq_some_iff
    (values : Finset ℕ)
    (value : ℕ) :
    finiteNatMaximum? values = some value ↔
      value ∈ values ∧ ∀ other ∈ values, other ≤ value := by
  classical
  unfold finiteNatMaximum?
  by_cases nonempty : values.Nonempty
  · rw [dif_pos nonempty]
    constructor
    · intro computed
      have maximumEq : values.max' nonempty = value := Option.some.inj computed
      subst value
      exact ⟨values.max'_mem nonempty,
        fun other otherPresent => values.le_max' other otherPresent⟩
    · rintro ⟨present, greatest⟩
      apply congrArg some
      exact Nat.le_antisymm
        (greatest (values.max' nonempty) (values.max'_mem nonempty))
        (values.le_max' value present)
  · rw [dif_neg nonempty]
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨present, _greatest⟩
      exact False.elim (nonempty ⟨value, present⟩)

private theorem finiteNatMaximum?_eq_none_iff
    (values : Finset ℕ) :
    finiteNatMaximum? values = none ↔ values = ∅ := by
  classical
  unfold finiteNatMaximum?
  by_cases nonempty : values.Nonempty
  · rw [dif_pos nonempty]
    constructor
    · intro impossible
      cases impossible
    · intro empty
      subst values
      simp at nonempty
  · rw [dif_neg nonempty]
    exact ⟨fun _ => Finset.not_nonempty_iff_eq_empty.mp nonempty, fun _ => rfl⟩

/-- Highest proper-axis order among, and only among, axes admitting a contiguous helix. -/
noncomputable def molecularFullereneHighestEligibleHelicalAxisOrder?
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) : Option ℕ :=
  finiteNatMaximum? (molecularFullereneEligibleHelicalAxisOrders molecule input)

/-- Exact Fu-3.1.1 highest-eligible-order semantics. -/
@[simp] theorem molecularFullereneHighestEligibleHelicalAxisOrder?_eq_some_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (axisOrder : ℕ) :
    molecularFullereneHighestEligibleHelicalAxisOrder? molecule input = some axisOrder ↔
      (∃ candidate,
        MolecularFullereneAxialContiguousHelicalNumberingJudgment
          molecule input candidate ∧
        candidate.axisOrder = axisOrder) ∧
      ∀ other,
        MolecularFullereneAxialContiguousHelicalNumberingJudgment
          molecule input other →
        other.axisOrder ≤ axisOrder := by
  rw [molecularFullereneHighestEligibleHelicalAxisOrder?,
    finiteNatMaximum?_eq_some_iff]
  constructor
  · rintro ⟨orderPresent, greatest⟩
    refine ⟨(mem_molecularFullereneEligibleHelicalAxisOrders_iff
      molecule input axisOrder).mp orderPresent, ?_⟩
    intro other otherJudged
    exact greatest other.axisOrder
      ((mem_molecularFullereneEligibleHelicalAxisOrders_iff
        molecule input other.axisOrder).mpr ⟨other, otherJudged, rfl⟩)
  · rintro ⟨orderWitness, greatest⟩
    refine ⟨(mem_molecularFullereneEligibleHelicalAxisOrders_iff
      molecule input axisOrder).mpr orderWitness, ?_⟩
    intro otherOrder otherOrderPresent
    rcases (mem_molecularFullereneEligibleHelicalAxisOrders_iff
      molecule input otherOrder).mp otherOrderPresent with
      ⟨other, otherJudged, orderEq⟩
    simpa [← orderEq] using greatest other otherJudged

/-- Refusal is exactly absence of any proper axis admitting a contiguous helix. -/
@[simp] theorem molecularFullereneHighestEligibleHelicalAxisOrder?_eq_none_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    molecularFullereneHighestEligibleHelicalAxisOrder? molecule input = none ↔
      ¬∃ candidate,
        MolecularFullereneAxialContiguousHelicalNumberingJudgment
          molecule input candidate := by
  rw [molecularFullereneHighestEligibleHelicalAxisOrder?,
    finiteNatMaximum?_eq_none_iff]
  constructor
  · intro ordersEmpty candidateExists
    rcases candidateExists with ⟨candidate, judged⟩
    have orderPresent : candidate.axisOrder ∈
        molecularFullereneEligibleHelicalAxisOrders molecule input :=
      (mem_molecularFullereneEligibleHelicalAxisOrders_iff
        molecule input candidate.axisOrder).mpr ⟨candidate, judged, rfl⟩
    rw [ordersEmpty] at orderPresent
    simp at orderPresent
  · intro noCandidate
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro axisOrder orderPresent
    rcases (mem_molecularFullereneEligibleHelicalAxisOrders_iff
      molecule input axisOrder).mp orderPresent with ⟨candidate, judged, _orderEq⟩
    exact noCandidate ⟨candidate, judged⟩

/-- Retain exactly the candidates on axes of the highest order that actually admits a contiguous
helix. -/
noncomputable def molecularFullereneHighestOrderAxialHelicalNumberingCandidates
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    List MolecularFullereneAxialContiguousHelicalNumberingCandidate :=
  (molecularFullereneAxialContiguousHelicalNumberingCandidates molecule input).filter
    fun candidate => decide
      (molecularFullereneHighestEligibleHelicalAxisOrder? molecule input =
        some candidate.axisOrder)

/-- Exact highest-eligible-axis filter. -/
@[simp] theorem mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    candidate ∈ molecularFullereneHighestOrderAxialHelicalNumberingCandidates molecule input ↔
      MolecularFullereneAxialContiguousHelicalNumberingJudgment molecule input candidate ∧
        molecularFullereneHighestEligibleHelicalAxisOrder? molecule input =
          some candidate.axisOrder := by
  constructor
  · intro present
    have filtered := List.mem_filter.mp present
    exact ⟨(mem_molecularFullereneAxialContiguousHelicalNumberingCandidates_iff
      molecule input candidate).mp filtered.1, of_decide_eq_true filtered.2⟩
  · rintro ⟨judged, highestEq⟩
    apply List.mem_filter.mpr
    exact ⟨(mem_molecularFullereneAxialContiguousHelicalNumberingCandidates_iff
      molecule input candidate).mpr judged,
      by simpa only [decide_eq_true_eq] using highestEq⟩

/-- Highest-order filtering neither creates emptiness nor invents a path. -/
theorem molecularFullereneHighestOrderAxialHelicalNumberingCandidates_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    molecularFullereneHighestOrderAxialHelicalNumberingCandidates molecule input ≠ [] ↔
      molecularFullereneAxialContiguousHelicalNumberingCandidates molecule input ≠ [] := by
  constructor
  · intro nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact List.ne_nil_of_mem
      ((mem_molecularFullereneAxialContiguousHelicalNumberingCandidates_iff
        molecule input candidate).mpr
          ((mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
            molecule input candidate).mp present).1)
  · intro nonempty
    obtain ⟨candidate, candidatePresent⟩ := List.exists_mem_of_ne_nil _ nonempty
    have candidateJudged :=
      (mem_molecularFullereneAxialContiguousHelicalNumberingCandidates_iff
        molecule input candidate).mp candidatePresent
    have orderSetNonempty :
        (molecularFullereneEligibleHelicalAxisOrders molecule input).Nonempty :=
      ⟨candidate.axisOrder,
        (mem_molecularFullereneEligibleHelicalAxisOrders_iff
          molecule input candidate.axisOrder).mpr ⟨candidate, candidateJudged, rfl⟩⟩
    let highestOrder :=
      (molecularFullereneEligibleHelicalAxisOrders molecule input).max' orderSetNonempty
    have highestEq :
        molecularFullereneHighestEligibleHelicalAxisOrder? molecule input =
          some highestOrder := by
      change finiteNatMaximum?
          (molecularFullereneEligibleHelicalAxisOrders molecule input) = some highestOrder
      simp [finiteNatMaximum?, orderSetNonempty, highestOrder]
    rcases (molecularFullereneHighestEligibleHelicalAxisOrder?_eq_some_iff
      molecule input highestOrder).mp highestEq with
      ⟨⟨best, bestJudged, bestOrderEq⟩, _greatest⟩
    exact List.ne_nil_of_mem
      ((mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
        molecule input best).mpr ⟨bestJudged, by simpa [bestOrderEq] using highestEq⟩)

/-! ## Ring > bond > atom among highest-order axes (Fu-3.1.2) -/

/-- End-kind ranks represented after the Fu-3.1.1 highest-axis-order filter. -/
noncomputable def molecularFullereneHighestOrderHelicalAxisEndKindRanks
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) : Finset ℕ :=
  ((molecularFullereneHighestOrderAxialHelicalNumberingCandidates molecule input).map
    fun candidate => fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind).toFinset

/-- Exact end-kind-rank membership after highest-axis-order selection. -/
@[simp] theorem mem_molecularFullereneHighestOrderHelicalAxisEndKindRanks_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (kindRank : ℕ) :
    kindRank ∈ molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input ↔
      ∃ candidate,
        MolecularFullereneAxialContiguousHelicalNumberingJudgment
          molecule input candidate ∧
        molecularFullereneHighestEligibleHelicalAxisOrder? molecule input =
          some candidate.axisOrder ∧
        fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind = kindRank := by
  classical
  constructor
  · intro present
    have rawPresent := present
    change kindRank ∈
      ((molecularFullereneHighestOrderAxialHelicalNumberingCandidates molecule input).map
        fun candidate =>
          fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind).toFinset at rawPresent
    have mappedPresent := List.mem_toFinset.mp rawPresent
    rcases List.mem_map.mp mappedPresent with ⟨candidate, candidatePresent, rankEq⟩
    have preferred :=
      (mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
        molecule input candidate).mp candidatePresent
    exact ⟨candidate, preferred.1, preferred.2, rankEq⟩
  · rintro ⟨candidate, judged, highestEq, rankEq⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨candidate,
      (mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
        molecule input candidate).mpr ⟨judged, highestEq⟩,
      rankEq⟩

/-- Maximum Fu-3.1.2 end-kind rank among candidates already surviving Fu-3.1.1. -/
noncomputable def molecularFullerenePreferredHelicalAxisEndKindRank?
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) : Option ℕ :=
  finiteNatMaximum?
    (molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input)

/-- Exact maximum end-kind selection; rank `2`, `1`, and `0` mean ring, bond, and atom. -/
@[simp] theorem molecularFullerenePreferredHelicalAxisEndKindRank?_eq_some_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (kindRank : ℕ) :
    molecularFullerenePreferredHelicalAxisEndKindRank? molecule input = some kindRank ↔
      kindRank ∈ molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input ∧
        ∀ otherRank ∈ molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input,
          otherRank ≤ kindRank := by
  exact finiteNatMaximum?_eq_some_iff
    (molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input) kindRank

/-- Retain the Fu-3.1.2-preferred end kind after Fu-3.1.1 has fixed the eligible axis order. -/
noncomputable def molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    List MolecularFullereneAxialContiguousHelicalNumberingCandidate :=
  (molecularFullereneHighestOrderAxialHelicalNumberingCandidates molecule input).filter
    fun candidate => decide
      (molecularFullerenePreferredHelicalAxisEndKindRank? molecule input =
        some (fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind))

/-- Exact composition of Fu-3.1.1 and Fu-3.1.2. -/
@[simp] theorem mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput)
    (candidate : MolecularFullereneAxialContiguousHelicalNumberingCandidate) :
    candidate ∈ molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates
        molecule input ↔
      MolecularFullereneAxialContiguousHelicalNumberingJudgment molecule input candidate ∧
        molecularFullereneHighestEligibleHelicalAxisOrder? molecule input =
          some candidate.axisOrder ∧
        molecularFullerenePreferredHelicalAxisEndKindRank? molecule input =
          some (fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind) := by
  constructor
  · intro present
    have filtered := List.mem_filter.mp present
    have highest :=
      (mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
        molecule input candidate).mp filtered.1
    exact ⟨highest.1, highest.2, of_decide_eq_true filtered.2⟩
  · rintro ⟨judged, highestEq, kindEq⟩
    apply List.mem_filter.mpr
    exact ⟨(mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
      molecule input candidate).mpr ⟨judged, highestEq⟩,
      by simpa only [decide_eq_true_eq] using kindEq⟩

/-- End-kind filtering preserves nonemptiness exactly. -/
theorem molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_nonempty_iff
    (molecule : RawMolecule)
    (input : MolecularFullereneConfigurationInput) :
    molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates molecule input ≠ [] ↔
      molecularFullereneHighestOrderAxialHelicalNumberingCandidates molecule input ≠ [] := by
  constructor
  · intro nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    have preferred :=
      (mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff
        molecule input candidate).mp present
    exact List.ne_nil_of_mem
      ((mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
        molecule input candidate).mpr ⟨preferred.1, preferred.2.1⟩)
  · intro nonempty
    obtain ⟨candidate, candidatePresent⟩ := List.exists_mem_of_ne_nil _ nonempty
    have highest :=
      (mem_molecularFullereneHighestOrderAxialHelicalNumberingCandidates_iff
        molecule input candidate).mp candidatePresent
    have ranksNonempty :
        (molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input).Nonempty :=
      ⟨fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind,
        (mem_molecularFullereneHighestOrderHelicalAxisEndKindRanks_iff molecule input
          (fullereneAxisEndKindRank candidate.axisCandidate.axisEnd.kind)).mpr
            ⟨candidate, highest.1, highest.2, rfl⟩⟩
    let bestRank :=
      (molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input).max' ranksNonempty
    have bestRankEq :
        molecularFullerenePreferredHelicalAxisEndKindRank? molecule input = some bestRank := by
      change finiteNatMaximum?
          (molecularFullereneHighestOrderHelicalAxisEndKindRanks molecule input) = some bestRank
      simp [finiteNatMaximum?, ranksNonempty, bestRank]
    have bestRankPresent :=
      (molecularFullerenePreferredHelicalAxisEndKindRank?_eq_some_iff
        molecule input bestRank).mp bestRankEq |>.1
    rcases (mem_molecularFullereneHighestOrderHelicalAxisEndKindRanks_iff
      molecule input bestRank).mp bestRankPresent with
      ⟨best, bestJudged, bestHighestEq, bestKindEq⟩
    exact List.ne_nil_of_mem
      ((mem_molecularFullerenePreferredAxisEndKindHelicalNumberingCandidates_iff
        molecule input best).mpr
          ⟨bestJudged, bestHighestEq, by simpa [bestKindEq] using bestRankEq⟩)

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
