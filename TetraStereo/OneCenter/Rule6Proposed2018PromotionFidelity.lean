import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP
namespace ProductionOccurrenceRules456






























































variable {mol : RawMolecule}

/-! ## 1. Fail-closed promotion-result aggregation from the source passage -/

/-- One possible result of a single promotion.

* `operationalFailure` records that the engine's ranking computation returned `none`: no ranking
  was produced, so the promotion multiset is incomplete and no source conclusion is available.
* `unresolved` records a ranking that *completed* but was not unique (a remaining tie); the source
  counts only actual descriptors in cancellation, so such a result contributes nothing.
* `descriptor` records a completed unique ranking with that descriptor. -/
inductive PromotionOutcome where
  | operationalFailure
  | unresolved
  | descriptor (descriptor : RS)
  deriving DecidableEq, Repr

/-- Signed cancellation balance.  `some` carries `+1` per `R`, `-1` per `S`, and `0` per completed
non-unique promotion.  The balance is `none` as soon as an operational failure occurs: cancellation
is only defined on a complete promotion multiset. -/
def promotionBalance : List PromotionOutcome → Option Int
  | [] => some 0
  | .operationalFailure :: _ => none
  | .unresolved :: rest => promotionBalance rest
  | .descriptor RS.R :: rest => (promotionBalance rest).map (· + 1)
  | .descriptor RS.S :: rest => (promotionBalance rest).map (· - 1)

/-- The source aggregation: cancel matching `R`/`S` pairs.  A strict positive balance leaves `R`, a
strict negative balance leaves `S`, and a zero balance leaves no descriptor
(`Hanson2018-preprint.txt:1022-1024`).  The outer `none` is *operational failure*, not a source
outcome: it means at least one promotion never produced a ranking, so no descriptor may be claimed.
-/
def promotionAggregate (outcomes : List PromotionOutcome) : Option (Option RS) :=
  match promotionBalance outcomes with
  | none => none
  | some balance =>
      if 0 < balance then some (some RS.R)
      else if balance < 0 then some (some RS.S)
      else some none

@[simp] theorem promotionBalance_nil : promotionBalance [] = some 0 := rfl

@[simp] theorem promotionBalance_operationalFailure (rest : List PromotionOutcome) :
    promotionBalance (PromotionOutcome.operationalFailure :: rest) = none := rfl

@[simp] theorem promotionBalance_unresolved (rest : List PromotionOutcome) :
    promotionBalance (PromotionOutcome.unresolved :: rest) = promotionBalance rest := rfl

@[simp] theorem promotionBalance_descriptor_R (rest : List PromotionOutcome) :
    promotionBalance (PromotionOutcome.descriptor RS.R :: rest) =
      (promotionBalance rest).map (· + 1) := rfl

@[simp] theorem promotionBalance_descriptor_S (rest : List PromotionOutcome) :
    promotionBalance (PromotionOutcome.descriptor RS.S :: rest) =
      (promotionBalance rest).map (· - 1) := rfl

/-- The balance is defined exactly when every promotion completed.  Operational failure is the only
source of `none`; completed non-unique promotions do not block cancellation. -/
theorem promotionBalance_eq_none_iff (outcomes : List PromotionOutcome) :
    promotionBalance outcomes = none ↔
      PromotionOutcome.operationalFailure ∈ outcomes := by
  induction outcomes with
  | nil => simp [promotionBalance]
  | cons head tail ih =>
      cases head with
      | operationalFailure => simp [promotionBalance]
      | unresolved => simp [promotionBalance, ih]
      | descriptor descriptor => cases descriptor <;> simp [promotionBalance, ih]

/-- The aggregate of a multiset whose balance is computed: the explicit source result. -/
theorem promotionAggregate_eq_of_balance (outcomes : List PromotionOutcome) (balance : Int)
    (h : promotionBalance outcomes = some balance) :
    promotionAggregate outcomes =
      (if 0 < balance then some (some RS.R)
        else if balance < 0 then some (some RS.S) else some none) := by
  simp only [promotionAggregate, h]

/-- A computed balance never yields the `none` outer aggregate. -/
theorem promotionAggregate_ne_none_of_balance_some (outcomes : List PromotionOutcome)
    (balance : Int) (h : promotionBalance outcomes = some balance) :
    promotionAggregate outcomes ≠ none := by
  intro hnone
  rw [promotionAggregate_eq_of_balance outcomes balance h] at hnone
  by_cases hpos : 0 < balance
  · simp [hpos] at hnone
  · by_cases hneg : balance < 0
    · simp [hpos, hneg] at hnone
    · simp [hpos, hneg] at hnone

/-- **Fail-closed source aggregation.**  The outer aggregate is `none` exactly when some promotion
failed operationally.  In particular a failed promotion can never be silently discarded while a
descriptor survives. -/
theorem promotionAggregate_eq_none_iff (outcomes : List PromotionOutcome) :
    promotionAggregate outcomes = none ↔
      PromotionOutcome.operationalFailure ∈ outcomes := by
  constructor
  · intro hnone
    by_contra hmem
    have hbalance : promotionBalance outcomes ≠ none := by
      intro hnoneBalance
      exact hmem ((promotionBalance_eq_none_iff outcomes).mp hnoneBalance)
    cases hb : promotionBalance outcomes with
    | none => exact hbalance hb
    | some balance =>
        exact (promotionAggregate_ne_none_of_balance_some outcomes balance hb) hnone
  · intro hfailure
    have hbalance : promotionBalance outcomes = none :=
      (promotionBalance_eq_none_iff outcomes).mpr hfailure
    simp only [promotionAggregate, hbalance]

/-- Unresolved (completed, non-unique) promotions are ignored by the source cancellation
procedure.  This remains true when other promotions are operational failures: the outer `none`
still propagates. -/
theorem promotionAggregate_unresolved (rest : List PromotionOutcome) :
    promotionAggregate (PromotionOutcome.unresolved :: rest) =
      promotionAggregate rest := by
  simp [promotionAggregate, promotionBalance]

/-- A matching `R`/`S` pair is ignored, exactly as the source passage states, whenever the remaining
multiset is complete.  If the remainder contains an operational failure, both sides are `none`. -/
theorem promotionAggregate_cancel_R_S (rest : List PromotionOutcome) :
    promotionAggregate (PromotionOutcome.descriptor RS.R ::
      PromotionOutcome.descriptor RS.S :: rest) = promotionAggregate rest := by
  have h : promotionBalance (PromotionOutcome.descriptor RS.R ::
      PromotionOutcome.descriptor RS.S :: rest) = promotionBalance rest := by
    rw [promotionBalance_descriptor_R, promotionBalance_descriptor_S]
    cases promotionBalance rest with
    | none => rfl
    | some n =>
        simp only [Option.map_some]
        congr 1
        omega
  simp [promotionAggregate, h]

/-- The mirror-image cancellation law. -/
theorem promotionAggregate_cancel_S_R (rest : List PromotionOutcome) :
    promotionAggregate (PromotionOutcome.descriptor RS.S ::
      PromotionOutcome.descriptor RS.R :: rest) = promotionAggregate rest := by
  have h : promotionBalance (PromotionOutcome.descriptor RS.S ::
      PromotionOutcome.descriptor RS.R :: rest) = promotionBalance rest := by
    rw [promotionBalance_descriptor_S, promotionBalance_descriptor_R]
    cases promotionBalance rest with
    | none => rfl
    | some n =>
        simp only [Option.map_some]
        congr 1
        omega
  simp [promotionAggregate, h]

/-- If every promotion resolves to `R`, all of its balance survives cancellation. -/
theorem promotionBalance_all_R (outcomes : List PromotionOutcome)
    (h : ∀ o, o ∈ outcomes → o = PromotionOutcome.descriptor RS.R) :
    promotionBalance outcomes = some (outcomes.length : Int) := by
  induction outcomes with
  | nil => simp [promotionBalance]
  | cons head tail ih =>
      have hhead : head = PromotionOutcome.descriptor RS.R := h head (by simp)
      have htail : ∀ o, o ∈ tail → o = PromotionOutcome.descriptor RS.R :=
        fun o ho => h o (by simp [ho])
      subst hhead
      rw [promotionBalance_descriptor_R, ih htail, List.length_cons]
      simp only [Option.map_some]
      congr 1

/-- If every promotion resolves to `S`, all of its balance survives cancellation. -/
theorem promotionBalance_all_S (outcomes : List PromotionOutcome)
    (h : ∀ o, o ∈ outcomes → o = PromotionOutcome.descriptor RS.S) :
    promotionBalance outcomes = some (-(outcomes.length : Int)) := by
  induction outcomes with
  | nil => simp [promotionBalance]
  | cons head tail ih =>
      have hhead : head = PromotionOutcome.descriptor RS.S := h head (by simp)
      have htail : ∀ o, o ∈ tail → o = PromotionOutcome.descriptor RS.S :=
        fun o ho => h o (by simp [ho])
      subst hhead
      rw [promotionBalance_descriptor_S, ih htail, List.length_cons]
      simp only [Option.map_some]
      congr 1; omega

/-- A nonempty list of identical resolved outcomes aggregates to that descriptor. -/
theorem promotionAggregate_all_descriptor (outcomes : List PromotionOutcome) (descriptor : RS)
    (h : ∀ o, o ∈ outcomes → o = PromotionOutcome.descriptor descriptor)
    (hne : outcomes ≠ []) : promotionAggregate outcomes = some (some descriptor) := by
  have hposNat : 0 < outcomes.length := List.length_pos_iff.mpr hne
  cases descriptor with
  | R =>
      have hbalance : promotionBalance outcomes = some (outcomes.length : Int) :=
        promotionBalance_all_R outcomes h
      have hpos : 0 < (outcomes.length : Int) := by exact_mod_cast hposNat
      rw [promotionAggregate_eq_of_balance outcomes (outcomes.length : Int) hbalance]
      rw [if_pos hpos]
  | S =>
      have hbalance : promotionBalance outcomes = some (-(outcomes.length : Int)) :=
        promotionBalance_all_S outcomes h
      have hpos : 0 < (outcomes.length : Int) := by exact_mod_cast hposNat
      have hneg : -(outcomes.length : Int) < 0 := by omega
      have hnpos : ¬ 0 < -(outcomes.length : Int) := by omega
      rw [promotionAggregate_eq_of_balance outcomes (-(outcomes.length : Int)) hbalance]
      rw [if_neg hnpos, if_pos hneg]

/-- **Counterexample: an operational failure is not discarded.**  One resolved descriptor followed
by a failed promotion has *no* source aggregate, rather than retaining the descriptor.  This is the
exact behaviour the previous total adapter got wrong. -/
theorem promotionAggregate_operationalFailure_not_discarded :
    promotionAggregate [PromotionOutcome.descriptor RS.R,
      PromotionOutcome.operationalFailure] = none := by
  decide




theorem promotionAggregate_completedUnresolved_is_discarded :
    promotionAggregate [PromotionOutcome.descriptor RS.R,
      PromotionOutcome.unresolved] = some (some RS.R) := by
  decide

/-- A failed promotion blocks every descriptor conclusion. -/
theorem promotionAggregate_ne_some_of_mem_operationalFailure
    (outcomes : List PromotionOutcome) (descriptor : RS)
    (h : PromotionOutcome.operationalFailure ∈ outcomes) :
    promotionAggregate outcomes ≠ some (some descriptor) := by
  intro hconclusion
  have hnone := (promotionAggregate_eq_none_iff outcomes).mpr h
  rw [hnone] at hconclusion
  cases hconclusion

/-! ## 2. The current selected-class unanimity procedure -/

/-- The descriptor-level content of the engine's selected-class unanimity test: every promotion in
the selected reference class must resolve uniquely and to the same descriptor.  This is the
`references.tail.allM` condition of `rankOccurrenceEquivalentReferences?` expressed on outcomes.
Operational failure and completed non-uniqueness both refuse to certify unanimity. -/
def selectedClassUnanimity : List PromotionOutcome → Option RS
  | [] => none
  | .operationalFailure :: _ => none
  | .unresolved :: _ => none
  | .descriptor descriptor :: rest =>
      if rest.all (fun o => o == PromotionOutcome.descriptor descriptor) then
        some descriptor
      else none

/-- For promotion classes of at most two members, and with every promotion completed (no operational
failure and no unresolved tie), cancellation and strict unanimity give exactly the same inner
descriptor.  This covers the 2+2 selected class, whose two references are `sorted[1]` and
`sorted[0]`, under its explicit unique-success hypotheses. -/
theorem promotionAggregate_eq_selectedClassUnanimity_of_length_le_two
    (outcomes : List PromotionOutcome) (h_len : outcomes.length ≤ 2)
    (h_no_failure : ∀ o, o ∈ outcomes → o ≠ PromotionOutcome.operationalFailure)
    (h_completed : ∀ o, o ∈ outcomes → o ≠ PromotionOutcome.unresolved) :
    promotionAggregate outcomes = some (selectedClassUnanimity outcomes) := by
  cases outcomes with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil =>
          cases first with
          | operationalFailure =>
              exact absurd rfl (h_no_failure PromotionOutcome.operationalFailure (by simp))
          | unresolved =>
              exact absurd rfl (h_completed PromotionOutcome.unresolved (by simp))
          | descriptor descriptor => cases descriptor <;> decide
      | cons second rest' =>
          cases rest' with
          | nil =>
              cases first with
              | operationalFailure =>
                  exact absurd rfl (h_no_failure PromotionOutcome.operationalFailure (by simp))
              | unresolved =>
                  exact absurd rfl (h_completed PromotionOutcome.unresolved (by simp))
              | descriptor firstDescriptor =>
                  cases second with
                  | operationalFailure =>
                      exact absurd rfl
                        (h_no_failure PromotionOutcome.operationalFailure (by simp))
                  | unresolved =>
                      exact absurd rfl
                        (h_completed PromotionOutcome.unresolved (by simp))
                  | descriptor secondDescriptor =>
                      cases firstDescriptor <;> cases secondDescriptor <;> decide
          | cons third rest'' =>
              simp only [List.length_cons] at h_len
              omega

/-- A resolved `R,R,S` promotion class distinguishes the source aggregation from strict
unanimity: one `R`/`S` pair cancels and `R` remains. -/
theorem promotionAggregate_three_twoOne :
    promotionAggregate
        [PromotionOutcome.descriptor RS.R, PromotionOutcome.descriptor RS.R,
          PromotionOutcome.descriptor RS.S] = some (some RS.R) := by
  decide

theorem selectedClassUnanimity_three_twoOne :
    selectedClassUnanimity
        [PromotionOutcome.descriptor RS.R, PromotionOutcome.descriptor RS.R,
          PromotionOutcome.descriptor RS.S] = none := by
  decide

/-- Unanimity is strictly stronger than source cancellation for three-member promotion classes.
This matters for the 3+1 carrier, whose selected class has three references; whether an admitted
molecule realizes a resolved 2-1 split is the explicitly stated residual obligation below. -/
theorem selectedClassUnanimity_not_aggregate_for_three :
    ∃ outcomes : List PromotionOutcome,
      outcomes.length = 3 ∧
        (∀ o, o ∈ outcomes → o ≠ PromotionOutcome.operationalFailure) ∧
        (∀ o, o ∈ outcomes → o ≠ PromotionOutcome.unresolved) ∧
        promotionAggregate outcomes ≠ some (selectedClassUnanimity outcomes) := by
  refine ⟨[PromotionOutcome.descriptor RS.R, PromotionOutcome.descriptor RS.R,
      PromotionOutcome.descriptor RS.S], rfl, ?_, ?_, ?_⟩
  · intro o ho
    simp at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · intro o ho
    simp at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · rw [promotionAggregate_three_twoOne, selectedClassUnanimity_three_twoOne]
    decide

/-! ## 3. Failure-aware lifting of actual authoritative promoted rankings -/

/-- One actual promotion result.  The result is an `Option`:

* `none` -- the ranking computation itself failed (operational failure);
* `some .unresolved` -- the ranking completed but was not unique;
* `some (.descriptor d)` -- the ranking completed uniquely with descriptor `d`.

There is deliberately no total adapter.  Note that promotion is by atom identity inside
`compareOccurrenceRule6PairLabels`, so ring-return occurrences of the same atom are all promoted;
this definition inherits that behaviour rather than assuming one atom is one occurrence. -/
def promotionOutcomeOfRanking? (parity : TetrahedralInputParity)
    (ranking : Option Rule6TrackedRanking) : Option PromotionOutcome :=
  match ranking with
  | none => none
  | some ranking =>
      if ranking.unique then
        some (PromotionOutcome.descriptor
          (RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven ranking.positions)))
      else some PromotionOutcome.unresolved

theorem promotionOutcomeOfRanking?_eq_descriptor (parity : TetrahedralInputParity)
    (ranking : Rule6TrackedRanking) (hunique : ranking.unique = true) :
    promotionOutcomeOfRanking? parity (some ranking) =
      some (PromotionOutcome.descriptor
        (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions))) := by
  simp [promotionOutcomeOfRanking?, hunique]

/-- A completed ranking that is not unique is a source `unresolved`, not an operational failure. -/
theorem promotionOutcomeOfRanking?_eq_unresolved_of_not_unique (parity : TetrahedralInputParity)
    (ranking : Rule6TrackedRanking) (hunique : ranking.unique = false) :
    promotionOutcomeOfRanking? parity (some ranking) = some PromotionOutcome.unresolved := by
  simp [promotionOutcomeOfRanking?, hunique]

/-- The adapter is `none` exactly when the ranking computation failed. -/
theorem promotionOutcomeOfRanking?_eq_none_iff (parity : TetrahedralInputParity)
    (ranking : Option Rule6TrackedRanking) :
    promotionOutcomeOfRanking? parity ranking = none ↔ ranking = none := by
  cases ranking with
  | none => simp [promotionOutcomeOfRanking?]
  | some ranking =>
      cases hunique : ranking.unique <;> simp [promotionOutcomeOfRanking?, hunique]

/-- Fail-closed traversal of a reference list under an arbitrary ranking callback.  It is `none` as
soon as one callback result is `none`, so a partial outcome list is never produced. -/
def promotionOutcomesOfRankings? (parity : TetrahedralInputParity)
    (ranking : Nat → Option Rule6TrackedRanking) :
    List Nat → Option (List PromotionOutcome)
  | [] => some []
  | referencePosition :: rest =>
      match promotionOutcomeOfRanking? parity (ranking referencePosition) with
      | none => none
      | some outcome =>
          match promotionOutcomesOfRankings? parity ranking rest with
          | none => none
          | some outcomes => some (outcome :: outcomes)

theorem promotionOutcomesOfRankings?_cons (parity : TetrahedralInputParity)
    (ranking : Nat → Option Rule6TrackedRanking) (referencePosition : Nat)
    (rest : List Nat) :
    promotionOutcomesOfRankings? parity ranking (referencePosition :: rest) =
      match promotionOutcomeOfRanking? parity (ranking referencePosition) with
      | none => none
      | some outcome =>
          match promotionOutcomesOfRankings? parity ranking rest with
          | none => none
          | some outcomes => some (outcome :: outcomes) := rfl

/-- The actual promotion multiset induced by the occurrence engine.  Each reference is a ligand
position; the ranking is the real `rankOccurrencePositionsThroughRule6Tracked?` computation used by
the two-group and four-way carriers.  The result is `none` as soon as one ranking computation fails:
a partial multiset is never presented as a source outcome. -/
def authoritativePromotionOutcomes? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (references : List Nat) : Option (List PromotionOutcome) :=
  promotionOutcomesOfRankings? parity
    (fun referencePosition =>
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
        referencePosition) references

@[simp] theorem authoritativePromotionOutcomes?_nil
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) :
    authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted parity [] =
      some [] := rfl

theorem authoritativePromotionOutcomes?_cons
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (referencePosition : Nat) (rest : List Nat) :
    authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted parity
        (referencePosition :: rest) =
      match promotionOutcomeOfRanking? parity
          (rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
            sorted referencePosition) with
      | none => none
      | some outcome =>
          match authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted
              parity rest with
          | none => none
          | some outcomes => some (outcome :: outcomes) := rfl

/-- **Complete multiset from pointwise successes.**  If every selected reference has its own actual
successful ranking producing `g`, the authoritative outcome list is exactly the image list.  This is
the lemma used by the accepted-reference trace: the trace supplies the pointwise successes; the
absence of operational failure is *derived*, never assumed. -/
theorem authoritativePromotionOutcomes?_eq_some_map_of_each
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (references : List Nat)
    (g : Nat → PromotionOutcome)
    (h : ∀ referencePosition, referencePosition ∈ references →
      promotionOutcomeOfRanking? parity
        (rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
          sorted referencePosition) = some (g referencePosition)) :
    authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted parity references =
      some (references.map g) := by
  induction references with
  | nil => rfl
  | cons head tail ih =>
      rw [authoritativePromotionOutcomes?_cons, h head (by simp)]
      have htail : authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted
          parity tail = some (tail.map g) :=
        ih (fun referencePosition member => h referencePosition (by simp [member]))
      rw [htail]
      rfl

/-- **Failure characterization.**  The authoritative multiset is `none` exactly when some selected
reference's ranking computation failed.  A completed non-unique ranking is a `some` outcome. -/
theorem authoritativePromotionOutcomes?_eq_none_iff
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (references : List Nat) :
    authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted parity references =
        none ↔
      ∃ referencePosition, referencePosition ∈ references ∧
        rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
          referencePosition = none := by
  induction references with
  | nil => simp [authoritativePromotionOutcomes?, promotionOutcomesOfRankings?]
  | cons head tail ih =>
      rw [authoritativePromotionOutcomes?_cons]
      constructor
      · intro hnone
        cases hhead : promotionOutcomeOfRanking? parity
            (rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
              sorted head) with
        | none =>
            exact ⟨head, by simp,
              (promotionOutcomeOfRanking?_eq_none_iff parity _).mp hhead⟩
        | some outcome =>
            cases htail : authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands
                sorted parity tail with
            | none =>
                rcases ih.mp htail with ⟨referencePosition, member, hfailed⟩
                exact ⟨referencePosition, by simp [member], hfailed⟩
            | some outcomes => exact absurd hnone (by simp [hhead, htail])
      · rintro ⟨referencePosition, member, hfailed⟩
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rw [(promotionOutcomeOfRanking?_eq_none_iff parity _).mpr hfailed]
        · cases hhead : promotionOutcomeOfRanking? parity
              (rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
                sorted head) with
          | none => rfl
          | some outcome =>
              rw [ih.mpr ⟨referencePosition, member, hfailed⟩]

/-- The source-facing aggregate over the actual engine rankings.  The outer `none` preserves
operational failure; the inner result is the completed source cancellation. -/
def authoritativePromotionAggregate? (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (references : List Nat) : Option (Option RS) :=
  (authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted parity
    references).bind promotionAggregate

/-- If any selected ranking computation fails, the source aggregate is absent (outer `none`). -/
theorem authoritativePromotionAggregate?_eq_none_of_exists_failure
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (references : List Nat)
    (h : ∃ referencePosition, referencePosition ∈ references ∧
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
        referencePosition = none) :
    authoritativePromotionAggregate? (mol := mol) aux fuel roots ligands sorted parity
        references = none := by
  unfold authoritativePromotionAggregate?
  rw [(authoritativePromotionOutcomes?_eq_none_iff (mol := mol) aux fuel roots ligands sorted
    parity references).mpr h]
  rfl

/-- **Acceptance eliminates operational failure.**  A successful selected-class acceptance supplies,
through the actual trace, a unique ranking for every selected reference.  Hence the authoritative
outcome list is complete, and source cancellation retains the accepted descriptor.  No absence of
failure is assumed at the call site; it is a consequence of the acceptance equation. -/
theorem promotionAggregate_authoritativeEquivalentReferences
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted references : List Nat)
    (parity : TetrahedralInputParity) (first : Rule6TrackedRanking)
    (accepted : rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands
      sorted references = some first) :
    authoritativePromotionAggregate? (mol := mol) aux fuel roots ligands sorted parity references =
      some (some (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions))) := by
  rcases occurrenceEquivalentReferencesTrace_complete (mol := mol) aux fuel roots parity
      ligands sorted references first accepted with ⟨trace⟩
  have houtcomes : authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted
        parity references =
      some (references.map fun _ => PromotionOutcome.descriptor
        (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven first.positions))) := by
    apply authoritativePromotionOutcomes?_eq_some_map_of_each
    intro referencePosition member
    rcases trace.all_references referencePosition member with
      ⟨ranking, rankingTrace, uniqueEq, descriptorEq⟩
    have rankingEq := rankingTrace.sound
    simp [promotionOutcomeOfRanking?, rankingEq, uniqueEq, descriptorEq]
  have hrefs_ne : references ≠ [] := by
    cases references with
    | nil =>
        have hhead := trace.reference_head
        simp at hhead
    | cons head tail => simp
  have hmap_ne :
      references.map
        (fun _ => PromotionOutcome.descriptor
          (RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven first.positions))) ≠ [] := by
    intro hnil
    exact hrefs_ne (List.map_eq_nil_iff.mp hnil)
  unfold authoritativePromotionAggregate?
  rw [houtcomes]
  simp only [Option.bind_some]
  exact promotionAggregate_all_descriptor
    (references.map fun _ => PromotionOutcome.descriptor
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions)))
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven first.positions))
    (fun o ho => by
      rcases List.mem_map.mp ho with ⟨referencePosition, _, hEq⟩
      exact hEq.symm)
    hmap_ne

/-- Accepted acceptance really rules out any failed ranking among the selected references. -/
theorem accepted_ranking_has_no_operational_failure
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted references : List Nat)
    (parity : TetrahedralInputParity) (first : Rule6TrackedRanking)
    (accepted : rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands
      sorted references = some first) :
    ¬ ∃ referencePosition, referencePosition ∈ references ∧
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
        referencePosition = none := by
  intro hfailure
  have hnone := authoritativePromotionAggregate?_eq_none_of_exists_failure (mol := mol)
    aux fuel roots ligands sorted parity references hfailure
  have hsome := promotionAggregate_authoritativeEquivalentReferences (mol := mol) aux fuel roots
    ligands sorted references parity first accepted
  rw [hnone] at hsome
  cases hsome

/-- **Completeness of the current selected-class check for a two-reference class.**  When both
actual promotions resolve uniquely to the same descriptor, the engine's check accepts the first
ranking.  Combined with the previous theorem, this makes selected-class unanimity and source
cancellation equivalent on the 2+2 carrier. -/
theorem authoritativeEquivalentReferences_twoTwo
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking)
    (first_eq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
      sorted (sorted.getD 1 0) = some first)
    (first_unique : first.unique = true)
    (second_eq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
      sorted (sorted.getD 0 0) = some second)
    (second_unique : second.unique = true)
    (same_descriptor : RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven second.positions) =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions)) :
    rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands sorted
      [sorted.getD 1 0, sorted.getD 0 0] = some first := by
  change rankProductionRule6EquivalentReferencesWithBackend?
    (productionOccurrenceRule6RankingBackend (mol := mol) aux fuel roots ligands sorted)
    parity [sorted.getD 1 0, sorted.getD 0 0] = some first
  exact rankProductionRule6EquivalentReferencesWithBackend?_complete
    (productionOccurrenceRule6RankingBackend (mol := mol) aux fuel roots ligands sorted)
    parity [sorted.getD 1 0, sorted.getD 0 0] first
    { firstReferencePosition := sorted.getD 1 0
      reference_head := rfl
      first_ranking := by
        simpa [productionOccurrenceRule6RankingBackend] using first_eq
      first_unique := first_unique
      all_references := by
        intro referencePosition member
        simp at member
        rcases member with rfl | rfl
        · exact ⟨first, by
            simpa [productionOccurrenceRule6RankingBackend] using first_eq,
            first_unique, rfl⟩
        · exact ⟨second, by
            simpa [productionOccurrenceRule6RankingBackend] using second_eq,
            second_unique, same_descriptor⟩ }

/-- **2+2 equivalence.**  The selected class of a 2+2 carrier is exactly the two references
`sorted[1]` and `sorted[0]`.  Given that both real promoted rankings resolve uniquely, the current
selected-class check accepts iff the fail-closed source aggregation leaves a descriptor, and the two
descriptors are the same.  The unique-success premises are actual computation equations; they
supply the complete multiset and therefore discharge operational-failure concerns. -/
theorem twoTwo_promotionAggregate_iff
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking)
    (first_eq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
      sorted (sorted.getD 1 0) = some first)
    (first_unique : first.unique = true)
    (second_eq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
      sorted (sorted.getD 0 0) = some second)
    (second_unique : second.unique = true) :
    (rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands sorted
        [sorted.getD 1 0, sorted.getD 0 0] = some first) ↔
      authoritativePromotionAggregate? (mol := mol) aux fuel roots ligands sorted parity
          [sorted.getD 1 0, sorted.getD 0 0] =
        some (some (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven first.positions))) := by
  let firstDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven first.positions)
  let secondDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven second.positions)
  constructor
  · intro accepted
    exact promotionAggregate_authoritativeEquivalentReferences (mol := mol) aux fuel roots
      ligands sorted [sorted.getD 1 0, sorted.getD 0 0] parity first accepted
  · intro aggregate
    have outcomeFirst : promotionOutcomeOfRanking? parity
        (rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
          (sorted.getD 1 0)) = some (PromotionOutcome.descriptor firstDescriptor) := by
      rw [first_eq]
      exact promotionOutcomeOfRanking?_eq_descriptor parity first first_unique
    have outcomeSecond : promotionOutcomeOfRanking? parity
        (rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands sorted
          (sorted.getD 0 0)) = some (PromotionOutcome.descriptor secondDescriptor) := by
      rw [second_eq]
      exact promotionOutcomeOfRanking?_eq_descriptor parity second second_unique
    have outcomesEq : authoritativePromotionOutcomes? (mol := mol) aux fuel roots ligands sorted
        parity [sorted.getD 1 0, sorted.getD 0 0] =
        some [PromotionOutcome.descriptor firstDescriptor,
          PromotionOutcome.descriptor secondDescriptor] := by
      rw [authoritativePromotionOutcomes?_cons, outcomeFirst,
        authoritativePromotionOutcomes?_cons, outcomeSecond,
        authoritativePromotionOutcomes?_nil]
    unfold authoritativePromotionAggregate? at aggregate
    rw [outcomesEq] at aggregate
    simp only [Option.bind_some] at aggregate
    have same : firstDescriptor = secondDescriptor := by
      revert aggregate
      cases firstDescriptor <;> cases secondDescriptor <;>
        simp [promotionAggregate, promotionBalance]
    exact authoritativeEquivalentReferences_twoTwo (mol := mol) aux fuel roots ligands sorted
      parity first second first_eq first_unique second_eq second_unique same.symm

/-! ## 4. Actual partition patterns for the two-group carriers -/

/-- The 2+2 selected class enumerates the two members of the senior group. -/
theorem rule6EquivalentReferencePositions_of_twoTwo (sorted : List Nat) :
    rule6EquivalentReferencePositions sorted
        [some Ordering.eq, some Ordering.gt, some Ordering.eq] =
      [sorted.getD 1 0, sorted.getD 0 0] := by
  simp [rule6EquivalentReferencePositions]

/-- The 3+1 selected class enumerates the three members of the senior group. -/
theorem rule6EquivalentReferencePositions_of_threeOne (sorted : List Nat) :
    rule6EquivalentReferencePositions sorted
        [some Ordering.eq, some Ordering.eq, some Ordering.gt] =
      [sorted.getD 1 0, sorted.getD 2 0, sorted.getD 0 0] := by
  simp [rule6EquivalentReferencePositions]

/-- The 1+3 selected class enumerates the three members of the junior group. -/
theorem rule6EquivalentReferencePositions_of_oneThree (sorted : List Nat) :
    rule6EquivalentReferencePositions sorted
        [some Ordering.gt, some Ordering.eq, some Ordering.eq] =
      [sorted.getD 1 0, sorted.getD 2 0, sorted.getD 3 0] := by
  simp [rule6EquivalentReferencePositions]

theorem threeOne_selectedClass_length (sorted : List Nat) :
    (rule6EquivalentReferencePositions sorted
        [some Ordering.eq, some Ordering.eq, some Ordering.gt]).length = 3 := by
  rw [rule6EquivalentReferencePositions_of_threeOne]
  simp

theorem oneThree_selectedClass_length (sorted : List Nat) :
    (rule6EquivalentReferencePositions sorted
        [some Ordering.gt, some Ordering.eq, some Ordering.eq]).length = 3 := by
  rw [rule6EquivalentReferencePositions_of_oneThree]
  simp

/-- The full 2+2 main theorem on the actual references returned by the engine's partition
enumeration.  `adjacency` is the certified adjacent partition; the hypothesis fixes the 2+2 shape. -/
theorem twoTwo_selectedClass_aggregate_iff
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (adjacency : List (Option Ordering)) (parity : TetrahedralInputParity)
    (first second : Rule6TrackedRanking)
    (adjacency_eq : adjacency =
      [some Ordering.eq, some Ordering.gt, some Ordering.eq])
    (first_eq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
      sorted (sorted.getD 1 0) = some first)
    (first_unique : first.unique = true)
    (second_eq : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands
      sorted (sorted.getD 0 0) = some second)
    (second_unique : second.unique = true) :
    (rankOccurrenceEquivalentReferences? (mol := mol) aux fuel roots parity ligands sorted
        (rule6EquivalentReferencePositions sorted adjacency) = some first) ↔
      authoritativePromotionAggregate? (mol := mol) aux fuel roots ligands sorted parity
          (rule6EquivalentReferencePositions sorted adjacency) =
        some (some (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven first.positions))) := by
  rw [adjacency_eq, rule6EquivalentReferencePositions_of_twoTwo]
  exact twoTwo_promotionAggregate_iff (mol := mol) aux fuel roots ligands sorted parity
    first second first_eq first_unique second_eq second_unique

/-! ## 5. Adjacent-partition classification under the executable gates -/

/-- A length-three complete adjacent partition with no strict decrease is `[eq,gt,eq]` exactly when
the middle edge is `gt` and there are two groups.  This is the structural gate shape of the 2+2
carrier. -/
theorem adjacency_eq_twoTwo_of_gates (adjacency : List (Option Ordering))
    (h_length : adjacency.length = 3)
    (h_all_some : ∀ entry, entry ∈ adjacency → ∃ ordering, entry = some ordering)
    (h_no_lt : some Ordering.lt ∉ adjacency)
    (h_count : rule6GroupCount adjacency = 2)
    (h_middle : adjacency[1]? = some (some Ordering.gt)) :
    adjacency = [some Ordering.eq, some Ordering.gt, some Ordering.eq] := by
  rcases List.length_eq_three.mp h_length with ⟨a, b, c, rfl⟩
  have hb : b = some Ordering.gt := by simpa using h_middle
  subst hb
  obtain ⟨oa, rfl⟩ := h_all_some a (by simp)
  obtain ⟨oc, rfl⟩ := h_all_some c (by simp)
  have hoa : oa ≠ Ordering.lt := by
    intro h
    apply h_no_lt
    simp [h]
  have hoc : oc ≠ Ordering.lt := by
    intro h
    apply h_no_lt
    simp [h]
  have hcount :
      (List.filter (fun decision => decision == some Ordering.gt)
        [some oa, some Ordering.gt, some oc]).length = 1 := by
    have hc := h_count
    simp [rule6GroupCount] at hc
    omega
  rcases oa with _ | _ | _
  · exact absurd rfl hoa
  · rcases oc with _ | _ | _
    · exact absurd rfl hoc
    · simp [List.filter] at hcount ⊢
    · simp [List.filter] at hcount
  · rcases oc with _ | _ | _
    · exact absurd rfl hoc
    · simp [List.filter] at hcount
    · simp [List.filter] at hcount

/-- The 1+2+1 middle-pair gate shape.  The executable three-group branch additionally requires the
middle edge to be `eq`; with three groups and no strict decrease this forces every entry to be
fixed. -/
theorem adjacency_eq_threeGroupMiddlePair_of_gates (adjacency : List (Option Ordering))
    (h_length : adjacency.length = 3)
    (h_all_some : ∀ entry, entry ∈ adjacency → ∃ ordering, entry = some ordering)
    (h_no_lt : some Ordering.lt ∉ adjacency)
    (h_count : rule6GroupCount adjacency = 3)
    (h_middle : adjacency[1]? = some (some Ordering.eq)) :
    adjacency = [some Ordering.gt, some Ordering.eq, some Ordering.gt] := by
  rcases List.length_eq_three.mp h_length with ⟨a, b, c, rfl⟩
  have hb : b = some Ordering.eq := by simpa using h_middle
  subst hb
  obtain ⟨oa, rfl⟩ := h_all_some a (by simp)
  obtain ⟨oc, rfl⟩ := h_all_some c (by simp)
  have hoa : oa ≠ Ordering.lt := by
    intro h
    apply h_no_lt
    simp [h]
  have hoc : oc ≠ Ordering.lt := by
    intro h
    apply h_no_lt
    simp [h]
  have hcount :
      (List.filter (fun decision => decision == some Ordering.gt)
        [some oa, some Ordering.eq, some oc]).length = 2 := by
    have hc := h_count
    simp [rule6GroupCount] at hc
    omega
  rcases oa with _ | _ | _ <;> rcases oc with _ | _ | _ <;>
    simp [List.filter] at hcount ⊢

/-! ## 6. Source applicability: the 1+2+1 partition is not a Rule 6 case -/

/-- Run lengths of the Rules-1--5 partition certified by the adjacent comparisons. -/
def rule6GroupSizes : List (Option Ordering) → List Nat
  | [] => [1]
  | ordering :: rest =>
      match rule6GroupSizes rest with
      | [] => [1]
      | size :: sizes =>
          if ordering = some Ordering.eq then (size + 1) :: sizes
          else 1 :: size :: sizes

/-- The source's stated applicability domain (`Hanson2018-preprint.txt:970-975`): after Rule 5 there
must be two pairs of identical ligands, or three or four identical ligands.  On the four-ligand
partition this is: at least two groups of size two, or a group of size at least three. -/
def sourceRule6Applicable (sizes : List Nat) : Bool :=
  decide (2 ≤ (sizes.filter (fun size => size == 2)).length) ||
    sizes.any (fun size => decide (3 ≤ size))

@[simp] theorem rule6GroupSizes_twoTwo :
    rule6GroupSizes [some Ordering.eq, some Ordering.gt, some Ordering.eq] = [2, 2] := rfl

@[simp] theorem rule6GroupSizes_threeOne :
    rule6GroupSizes [some Ordering.eq, some Ordering.eq, some Ordering.gt] = [3, 1] := rfl

@[simp] theorem rule6GroupSizes_oneThree :
    rule6GroupSizes [some Ordering.gt, some Ordering.eq, some Ordering.eq] = [1, 3] := rfl

@[simp] theorem rule6GroupSizes_threeGroupMiddlePair :
    rule6GroupSizes [some Ordering.gt, some Ordering.eq, some Ordering.gt] = [1, 2, 1] := rfl

@[simp] theorem sourceRule6Applicable_twoTwo : sourceRule6Applicable [2, 2] = true := by decide

@[simp] theorem sourceRule6Applicable_threeOne : sourceRule6Applicable [3, 1] = true := by decide

@[simp] theorem sourceRule6Applicable_oneThree : sourceRule6Applicable [1, 3] = true := by decide

@[simp] theorem sourceRule6Applicable_four : sourceRule6Applicable [4] = true := by decide

@[simp] theorem sourceRule6Applicable_threeGroupMiddlePair :
    sourceRule6Applicable [1, 2, 1] = false := by decide

/-- **The 1+2+1 branch is outside the source applicability domain.**  The executable three-group
middle-pair gate produces exactly the partition `[1,2,1]`, which has only one pair of identical
ligands and no triple.  The proposed Rule 6 as stated in the saved preprint therefore does not
consider this partition a Rule 6 case. -/
theorem threeGroupMiddlePair_not_sourceApplicable (adjacency : List (Option Ordering))
    (h_length : adjacency.length = 3)
    (h_all_some : ∀ entry, entry ∈ adjacency → ∃ ordering, entry = some ordering)
    (h_no_lt : some Ordering.lt ∉ adjacency)
    (h_count : rule6GroupCount adjacency = 3)
    (h_middle : adjacency[1]? = some (some Ordering.eq)) :
    sourceRule6Applicable (rule6GroupSizes adjacency) = false := by
  rw [adjacency_eq_threeGroupMiddlePair_of_gates adjacency h_length h_all_some h_no_lt
    h_count h_middle]
  simp

/-- Derivation-based form of the same exclusion, taking the real adjacent-comparison trace rather
than a separately supplied all-`some` fact. -/
theorem threeGroupMiddlePair_not_sourceApplicable_of_derivation
    (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (sorted : List Nat)
    (adjacencyOut : List (Option Ordering))
    (derivation : Rule6InitialAdjacentDerivation (mol := mol) aux fuel roots sorted adjacencyOut)
    (h_length : adjacencyOut.length = 3)
    (h_no_lt : some Ordering.lt ∉ adjacencyOut)
    (h_count : rule6GroupCount adjacencyOut = 3)
    (h_middle : adjacencyOut[1]? = some (some Ordering.eq)) :
    sourceRule6Applicable (rule6GroupSizes adjacencyOut) = false := by
  apply threeGroupMiddlePair_not_sourceApplicable adjacencyOut h_length _ h_no_lt h_count h_middle
  intro entry member
  exact Rule6InitialAdjacentDerivation.mem_some derivation member

/-! ## Kernel-authority guards

Every exported core result is checked against `sorryAx`, compiler trust, and project axioms.  The
only permitted logical principles are Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`.  Guards cover the source aggregation, the actual acceptance bridge, the conditional
two-two equivalence, and the distinguishing counterexamples. -/

assert_kernel_only promotionBalance_nil
assert_kernel_only promotionBalance_operationalFailure
assert_kernel_only promotionBalance_unresolved
assert_kernel_only promotionBalance_descriptor_R
assert_kernel_only promotionBalance_descriptor_S
assert_kernel_only promotionBalance_eq_none_iff
assert_kernel_only promotionAggregate_unresolved
assert_kernel_only promotionAggregate_cancel_R_S
assert_kernel_only promotionAggregate_cancel_S_R
assert_kernel_only promotionBalance_all_R
assert_kernel_only promotionBalance_all_S
assert_kernel_only promotionAggregate_all_descriptor
assert_kernel_only promotionAggregate_eq_none_iff
assert_kernel_only promotionAggregate_ne_some_of_mem_operationalFailure
assert_kernel_only promotionAggregate_eq_selectedClassUnanimity_of_length_le_two
assert_kernel_only promotionAggregate_three_twoOne
assert_kernel_only selectedClassUnanimity_three_twoOne
assert_kernel_only selectedClassUnanimity_not_aggregate_for_three
assert_kernel_only promotionOutcomeOfRanking?_eq_descriptor
assert_kernel_only promotionOutcomeOfRanking?_eq_unresolved_of_not_unique
assert_kernel_only promotionOutcomeOfRanking?_eq_none_iff
assert_kernel_only authoritativePromotionOutcomes?_eq_some_map_of_each
assert_kernel_only authoritativePromotionOutcomes?_eq_none_iff
assert_kernel_only authoritativePromotionAggregate?_eq_none_of_exists_failure
assert_kernel_only promotionAggregate_authoritativeEquivalentReferences
assert_kernel_only accepted_ranking_has_no_operational_failure
assert_kernel_only authoritativeEquivalentReferences_twoTwo
assert_kernel_only twoTwo_promotionAggregate_iff
assert_kernel_only twoTwo_selectedClass_aggregate_iff
assert_kernel_only rule6EquivalentReferencePositions_of_twoTwo
assert_kernel_only rule6EquivalentReferencePositions_of_threeOne
assert_kernel_only rule6EquivalentReferencePositions_of_oneThree
assert_kernel_only threeOne_selectedClass_length
assert_kernel_only oneThree_selectedClass_length
assert_kernel_only adjacency_eq_twoTwo_of_gates
assert_kernel_only adjacency_eq_threeGroupMiddlePair_of_gates
assert_kernel_only sourceRule6Applicable_twoTwo
assert_kernel_only sourceRule6Applicable_threeOne
assert_kernel_only sourceRule6Applicable_oneThree
assert_kernel_only sourceRule6Applicable_four
assert_kernel_only sourceRule6Applicable_threeGroupMiddlePair
assert_kernel_only threeGroupMiddlePair_not_sourceApplicable
assert_kernel_only threeGroupMiddlePair_not_sourceApplicable_of_derivation

/-! ## Residual scope

* The 2+2 equivalence is proved on the selected class only: the source passage also permits
  promotion inside the other identical pair.  The engine's selected-class check is sound for every
  carrier shape (`promotionAggregate_authoritativeEquivalentReferences`), but a full all-four-ligand
  aggregation requires a proof relating the two classes; the current partition API exposes only the
  class containing rank 1.  No claim is made here about the other class, and no all-promotions
  molecular completeness claim is made.
* For the 3+1 carrier the selected class has three references, so cancellation can in principle
  retain a descriptor after a 2-1 split (`selectedClassUnanimity_not_aggregate_for_three`).  No
  admitted `RawMolecule` witnessing a resolved 2-1 split has been constructed or kernel-checked;
  that is the remaining obligation for either a structural impossibility theorem or a molecule
  witness.  The soundness theorem shows the engine cannot emit a descriptor that source cancellation
  would discard.
* Operational failure is now fail-closed.  This module proves that the accepted-reference trace and
  the two-two unique-success hypotheses eliminate failure; it does not prove that arbitrary carrier
  calls never fail, and it makes no source claim when they do.
* The 1+2+1 exclusion is relative to the *saved May 2018 author preprint*.  The journal version of
  record was not available and may differ; this module makes no claim about it.
-/

end ProductionOccurrenceRules456
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456.promotionAggregate_operationalFailure_not_discarded
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456.promotionAggregate_completedUnresolved_is_discarded
