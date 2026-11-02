import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Preserve prior pseudo evidence separately from Rule-6 promotion

The existing Rule-6 comparison intentionally clears the earlier pseudo flag when an earlier
rule decides, and its own pseudo field records decisive marker use. A temporary auxiliary
calculation must not confuse these two channels. This adapter retains both while reproducing
the existing Rule-6 ordering and promotion flag exactly.

These are facts about the actual comparison APIs for arbitrary inputs, including failure.
Neither channel alone supplies a new chemical case convention or generated auxiliary label.
-/

namespace TetraStereo.OneCenter

/-- Independent evidence from the prior comparison and from the Rule-6 marker fallback. -/
structure OccurrenceRule6DecisionEvidence where
  ordering : Ordering
  priorPseudo : Bool
  promotionUsed : Bool
  deriving DecidableEq, Repr

/-- The original API exposes only the marker-use channel in its pseudo field. -/
def OccurrenceRule6DecisionEvidence.forget (e : OccurrenceRule6DecisionEvidence) :
    Rule6TrackedDecision :=
  { ordering := e.ordering, pseudo := e.promotionUsed }

/-- Record a strict prior decision's own pseudo flag, using the existing marker fallback only
when the prior ties. The input state remains explicit and is not reclassified or updated. -/
def compareOccurrenceThroughRule6Evidence? (mol : RawMolecule)
    (aux : OccurrenceAuxState) (reference fuel : Nat)
    (left right : CanonicalRerootCursor) : Option OccurrenceRule6DecisionEvidence := do
  let prior ← compareOccurrenceBranches? mol aux fuel left right
  if prior.ordering != .eq then
    some { ordering := prior.ordering, priorPseudo := prior.pseudo, promotionUsed := false }
  else
    let result ← compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right
    some { ordering := result.ordering, priorPseudo := false, promotionUsed := result.pseudo }

/-- The adapter preserves the original complete result after forgetting the extra prior flag. -/
theorem compareOccurrenceThroughRule6Evidence_forget
    (mol : RawMolecule) (aux : OccurrenceAuxState) (reference fuel : Nat)
    (left right : CanonicalRerootCursor) :
    (compareOccurrenceThroughRule6Evidence? mol aux reference fuel left right).map
        OccurrenceRule6DecisionEvidence.forget =
      compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right := by
  cases hp : compareOccurrenceBranches? mol aux fuel left right with
  | none =>
      have original : compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right =
          none := by
        cases fuel <;> simp_all [compareOccurrenceBranchesThroughRule6At?]
      simp [compareOccurrenceThroughRule6Evidence?, hp, original]
  | some prior =>
      by_cases tied : prior.ordering = Ordering.eq
      · cases hr : compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right <;>
          simp [compareOccurrenceThroughRule6Evidence?, hp, tied, hr,
            OccurrenceRule6DecisionEvidence.forget]
      · have original : compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right =
            some { ordering := prior.ordering, pseudo := false } := by
          cases fuel <;> simp_all [compareOccurrenceBranchesThroughRule6At?]
        simp [compareOccurrenceThroughRule6Evidence?, hp, tied, original,
          OccurrenceRule6DecisionEvidence.forget]

/-- Strict ordinary decisions keep their actual pseudo evidence, without a promotion decision. -/
theorem compareOccurrenceThroughRule6Evidence_of_prior
    (mol : RawMolecule) (aux : OccurrenceAuxState) (reference fuel : Nat)
    (left right : CanonicalRerootCursor) (prior : OccurrenceComparison)
    (computed : compareOccurrenceBranches? mol aux fuel left right = some prior)
    (strict : prior.ordering ≠ .eq) :
    compareOccurrenceThroughRule6Evidence? mol aux reference fuel left right =
      some { ordering := prior.ordering, priorPseudo := prior.pseudo, promotionUsed := false } := by
  simp [compareOccurrenceThroughRule6Evidence?, computed, strict]

/-- A single comparison cannot simultaneously be decided by the prior rules and by promotion. -/
theorem compareOccurrenceThroughRule6Evidence_disjoint
    (mol : RawMolecule) (aux : OccurrenceAuxState) (reference fuel : Nat)
    (left right : CanonicalRerootCursor) (e : OccurrenceRule6DecisionEvidence)
    (computed : compareOccurrenceThroughRule6Evidence? mol aux reference fuel left right = some e) :
    (e.priorPseudo && e.promotionUsed) = false := by
  unfold compareOccurrenceThroughRule6Evidence? at computed
  cases hp : compareOccurrenceBranches? mol aux fuel left right with
  | none => simp [hp] at computed
  | some prior =>
      by_cases tied : prior.ordering = Ordering.eq
      · cases hf : compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right with
        | none => simp [hp, tied, hf] at computed
        | some result =>
            simp [hp, tied, hf] at computed
            subst e
            rfl
      · simp [hp, tied] at computed
        subst e
        simp

assert_kernel_only compareOccurrenceThroughRule6Evidence_forget
assert_kernel_only compareOccurrenceThroughRule6Evidence_of_prior
assert_kernel_only compareOccurrenceThroughRule6Evidence_disjoint

end TetraStereo.OneCenter
