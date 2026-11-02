import TetraStereo.OneCenter.OccurrenceRule6DecisionEvidence
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Final-pair evidence after the actual occurrence Rule-6 ranking

Keep the existing ranking (including its insertion-time marker count), and read the final adjacent
pairs again with the evidence-preserving comparator. Ordinary pseudo evidence and promotion
evidence remain separate. This is an optional diagnostic extension: invalid indices or an
unavailable final comparison cause refusal. Successful output preserves the actual original
ranking exactly. No temporary case policy or production entry point is changed.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP.ProductionOccurrenceRules456

structure OccurrenceRule6ComparedPair where
  left : CanonicalRerootCursor
  right : CanonicalRerootCursor
  decision : OccurrenceRule6DecisionEvidence

def compareOccurrenceRule6AdjacentEvidence? (mol : RawMolecule) (aux : OccurrenceAuxState)
    (reference fuel : Nat) : List CanonicalRerootCursor →
      Option (List OccurrenceRule6ComparedPair)
  | [] | [_] => some []
  | left :: right :: tail => do
      let decision ← compareOccurrenceThroughRule6Evidence? mol aux reference fuel left right
      let rest ← compareOccurrenceRule6AdjacentEvidence? mol aux reference fuel (right :: tail)
      some ({ left := left, right := right, decision := decision } :: rest)

structure OccurrenceRule6RankingEvidence where
  ranking : Rule6TrackedRanking
  reference : Nat
  pairs : List OccurrenceRule6ComparedPair

/-- Ordinary prior pseudo flags on final adjacent pairs; not a chemical casing judgment. -/
def OccurrenceRule6RankingEvidence.priorPseudoCount (e : OccurrenceRule6RankingEvidence) : Nat :=
  (e.pairs.filter fun p => p.decision.priorPseudo).length

/-- Final adjacent promotions; distinct from the ranking's insertion-time marker count. -/
def OccurrenceRule6RankingEvidence.adjacentPromotionCount
    (e : OccurrenceRule6RankingEvidence) : Nat :=
  (e.pairs.filter fun p => p.decision.promotionUsed).length

def rankOccurrenceWithRule6Evidence? (mol : RawMolecule) (aux : OccurrenceAuxState)
    (fuel : Nat) (roots : List CanonicalRerootCursor) (ligands start : List Nat)
    (referencePosition : Nat) : Option OccurrenceRule6RankingEvidence := do
  let ranking ← rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots
    ligands start referencePosition
  let reference ← ligands[referencePosition]?
  let sorted ← ranking.positions.mapM fun i => roots[i]?
  let pairs ← compareOccurrenceRule6AdjacentEvidence? mol aux reference fuel sorted
  some { ranking := ranking, reference := reference, pairs := pairs }

theorem compareOccurrenceRule6AdjacentEvidence_sound
    (mol : RawMolecule) (aux : OccurrenceAuxState) (reference fuel : Nat)
    (sorted : List CanonicalRerootCursor) (pairs : List OccurrenceRule6ComparedPair)
    (computed : compareOccurrenceRule6AdjacentEvidence? mol aux reference fuel sorted =
      some pairs) :
    ∀ pair ∈ pairs, compareOccurrenceThroughRule6Evidence? mol aux reference fuel
      pair.left pair.right = some pair.decision := by
  induction sorted generalizing pairs with
  | nil =>
      simp [compareOccurrenceRule6AdjacentEvidence?] at computed
      subst pairs
      simp
  | cons left tail ih =>
      cases tail with
      | nil =>
          simp [compareOccurrenceRule6AdjacentEvidence?] at computed
          subst pairs
          simp
      | cons right rest =>
          cases hd : compareOccurrenceThroughRule6Evidence? mol aux reference fuel left right with
          | none => simp [compareOccurrenceRule6AdjacentEvidence?, hd] at computed
          | some decision =>
              cases ht : compareOccurrenceRule6AdjacentEvidence? mol aux reference fuel
                  (right :: rest) with
              | none => simp [compareOccurrenceRule6AdjacentEvidence?, hd, ht] at computed
              | some deeper =>
                  simp [compareOccurrenceRule6AdjacentEvidence?, hd, ht] at computed
                  subst pairs
                  intro pair member
                  rcases List.mem_cons.mp member with same | below
                  · subst pair
                    exact hd
                  · exact ih deeper ht pair below

/-- A reported prior pseudo flag comes from an actual strict ordinary comparison. -/
theorem compareOccurrenceThroughRule6Evidence_priorPseudo
    (mol : RawMolecule) (aux : OccurrenceAuxState) (reference fuel : Nat)
    (left right : CanonicalRerootCursor) (e : OccurrenceRule6DecisionEvidence)
    (computed : compareOccurrenceThroughRule6Evidence? mol aux reference fuel left right = some e)
    (pseudo : e.priorPseudo = true) :
    ∃ prior, compareOccurrenceBranches? mol aux fuel left right = some prior ∧
      prior.ordering ≠ .eq ∧ prior.pseudo = true := by
  unfold compareOccurrenceThroughRule6Evidence? at computed
  cases hp : compareOccurrenceBranches? mol aux fuel left right with
  | none => simp [hp] at computed
  | some prior =>
      by_cases tied : prior.ordering = Ordering.eq
      · cases hr : compareOccurrenceBranchesThroughRule6At? mol aux reference fuel left right with
        | none => simp [hp, tied, hr] at computed
        | some result =>
            simp [hp, tied, hr] at computed
            subst e
            cases pseudo
      · simp [hp, tied] at computed
        subst e
        exact ⟨prior, rfl, tied, pseudo⟩

/-- The recorded sequence is obtained by projecting the returned positions and traversing all
final adjacent pairs, not by selecting arbitrary comparison witnesses. -/
theorem rankOccurrenceWithRule6Evidence_readback
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands start : List Nat) (referencePosition : Nat)
    (e : OccurrenceRule6RankingEvidence)
    (computed : rankOccurrenceWithRule6Evidence? mol aux fuel roots ligands start
      referencePosition = some e) :
    ∃ sorted, e.ranking.positions.mapM (fun i => roots[i]?) = some sorted ∧
      compareOccurrenceRule6AdjacentEvidence? mol aux e.reference fuel sorted = some e.pairs := by
  simp only [rankOccurrenceWithRule6Evidence?, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at computed
  rcases computed with ⟨ranking, _, reference, _, sorted, hs, pairs, hp, rfl⟩
  exact ⟨sorted, hs, hp⟩

/-- Success retains the literal production ranking and actual final-pair comparator evidence. -/
theorem rankOccurrenceWithRule6Evidence_sound
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands start : List Nat) (referencePosition : Nat)
    (e : OccurrenceRule6RankingEvidence)
    (computed : rankOccurrenceWithRule6Evidence? mol aux fuel roots ligands start
      referencePosition = some e) :
    rankOccurrencePositionsThroughRule6Tracked? (mol := mol) aux fuel roots ligands start
        referencePosition = some e.ranking ∧
      ligands[referencePosition]? = some e.reference ∧
      ∀ pair ∈ e.pairs, compareOccurrenceThroughRule6Evidence? mol aux e.reference fuel
        pair.left pair.right = some pair.decision := by
  simp only [rankOccurrenceWithRule6Evidence?, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq] at computed
  rcases computed with ⟨ranking, hr, reference, href, sorted, _, pairs, hp, rfl⟩
  exact ⟨hr, href, compareOccurrenceRule6AdjacentEvidence_sound mol aux reference fuel
    sorted pairs hp⟩

/-- Each ordinary pseudo flag is traceable to a strict prior decision, and never also a promotion. -/
theorem rankOccurrenceWithRule6Evidence_priorWitness
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands start : List Nat) (referencePosition : Nat)
    (e : OccurrenceRule6RankingEvidence)
    (computed : rankOccurrenceWithRule6Evidence? mol aux fuel roots ligands start
      referencePosition = some e) (pair : OccurrenceRule6ComparedPair)
    (member : pair ∈ e.pairs) (pseudo : pair.decision.priorPseudo = true) :
    (∃ prior, compareOccurrenceBranches? mol aux fuel pair.left pair.right = some prior ∧
      prior.ordering ≠ .eq ∧ prior.pseudo = true) ∧ pair.decision.promotionUsed = false := by
  have actual := (rankOccurrenceWithRule6Evidence_sound mol aux fuel roots ligands start
    referencePosition e computed).2.2 pair member
  refine ⟨compareOccurrenceThroughRule6Evidence_priorPseudo mol aux e.reference fuel
    pair.left pair.right pair.decision actual pseudo, ?_⟩
  have disjoint := compareOccurrenceThroughRule6Evidence_disjoint mol aux e.reference fuel
    pair.left pair.right pair.decision actual
  simpa [pseudo] using disjoint

assert_kernel_only compareOccurrenceRule6AdjacentEvidence_sound
assert_kernel_only compareOccurrenceThroughRule6Evidence_priorPseudo
assert_kernel_only rankOccurrenceWithRule6Evidence_readback
assert_kernel_only rankOccurrenceWithRule6Evidence_sound
assert_kernel_only rankOccurrenceWithRule6Evidence_priorWitness

end TetraStereo.OneCenter
