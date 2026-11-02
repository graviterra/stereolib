import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceComparator
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

set_option autoImplicit false

namespace TetraStereo.OneCenter

open DeclarativeCIP.ProductionOccurrenceRules456

/-!
# Proof-relevant conformance for width-unbounded occurrence facts

The public authoritative tetrahedral override is computed by
`tetrahedralOccurrenceFactAuthoritative?`.  This file removes that function as an opaque proof
boundary.  A successful fact is decomposed into its atom/parity observation, exact four-ligand
frame, comparison-certified insertion sort, comparison-certified adjacent strictness traversal,
written-to-priority permutation, and uppercase/lowercase classification.

The comparison certificates name the five primitive sequence-rule stages and the pure precedence
assembler.  They do not store an equation for either the combined comparator or the final fact
evaluator.  Thus later chemical refinement can target the primitive stages without trusting the
orchestration code which assembles them.
-/

variable {mol : RawMolecule}

/-- The exact Rule-4c stage used by the width-unbounded fallback comparator. -/
def authoritativeRule4cStage? (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) : Option OccurrenceRule4cDecision :=
  if aux.any fun fact => !fact.uppercase then
    let before := compareOccurrenceDescriptorBranchAtAuthoritative? mol aux fuel .rule4c
    compareOccurrenceRule4cWithWitnessAuthoritative? mol aux before before fuel [(left, right)]
  else some { ordering := Ordering.eq }

/-- The width-unbounded fallback comparator is exactly the pure precedence assembly of its five
separately named primitive stages. -/
theorem compareOccurrenceBranchesAuthoritative?_factorization
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) :
    compareOccurrenceBranchesAuthoritative? mol aux fuel left right =
      assembleOccurrenceComparison?
        (certifiedConstitutionalStageAuthoritative? mol fuel left right)
        (compareOccurrenceDescriptorAtTiedRootAuthoritative? mol aux fuel .rule4a left right)
        (compareOccurrenceRule4bAuthoritative? mol aux fuel left right)
        (authoritativeRule4cStage? mol aux fuel left right)
        (compareOccurrenceRule5Authoritative? mol aux fuel left right) := by
  unfold compareOccurrenceBranchesAuthoritative? assembleOccurrenceComparison?
    authoritativeRule4cStage?
  cases constitutional : certifiedConstitutionalStageAuthoritative? mol fuel left right with
  | none => simp
  | some constitutionalResult =>
      cases constitutionalResult <;>
        by_cases hasLower : ∃ fact ∈ aux, fact.uppercase = false <;>
        simp [hasLower]

/-- Primitive-stage evidence for one successful width-unbounded fallback decision.  There is no
field containing the combined `compareOccurrenceBranchesAuthoritative?` equation. -/
structure AuthoritativeRule45Evaluation (mol : RawMolecule) (aux : OccurrenceAuxState)
    (fuel : Nat) (left right : CanonicalRerootCursor) (decision : OccurrenceComparison) where
  constitutionalResult : Option Ordering
  constitutionalEquation : certifiedConstitutionalStageAuthoritative? mol fuel left right =
    constitutionalResult
  rule4aResult : Option Ordering
  rule4aEquation : compareOccurrenceDescriptorAtTiedRootAuthoritative? mol aux fuel .rule4a
    left right = rule4aResult
  rule4bResult : Option Ordering
  rule4bEquation : compareOccurrenceRule4bAuthoritative? mol aux fuel left right = rule4bResult
  rule4cResult : Option OccurrenceRule4cDecision
  rule4cEquation : authoritativeRule4cStage? mol aux fuel left right = rule4cResult
  rule5Result : Option RawRule5Comparison
  rule5Equation : compareOccurrenceRule5Authoritative? mol aux fuel left right = rule5Result
  precedenceEquation : assembleOccurrenceComparison? constitutionalResult rule4aResult
    rule4bResult rule4cResult rule5Result = some decision

/-- The separately retained authoritative stage equations reconstruct the combined fallback
decision. -/
theorem AuthoritativeRule45Evaluation.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {left right : CanonicalRerootCursor} {decision : OccurrenceComparison}
    (evaluation : AuthoritativeRule45Evaluation mol aux fuel left right decision) :
    compareOccurrenceBranchesAuthoritative? mol aux fuel left right = some decision := by
  rw [compareOccurrenceBranchesAuthoritative?_factorization]
  rw [evaluation.constitutionalEquation, evaluation.rule4aEquation,
    evaluation.rule4bEquation, evaluation.rule4cEquation, evaluation.rule5Equation]
  exact evaluation.precedenceEquation

/-- Decompose a successful combined fallback call into its primitive stage equations. -/
def authoritativeRule45Evaluation (mol : RawMolecule) (aux : OccurrenceAuxState)
    (fuel : Nat) (left right : CanonicalRerootCursor) (decision : OccurrenceComparison)
    (fullEquation : compareOccurrenceBranchesAuthoritative? mol aux fuel left right =
      some decision) :
    AuthoritativeRule45Evaluation mol aux fuel left right decision :=
  { constitutionalResult := certifiedConstitutionalStageAuthoritative? mol fuel left right
    constitutionalEquation := rfl
    rule4aResult := compareOccurrenceDescriptorAtTiedRootAuthoritative? mol aux fuel .rule4a
      left right
    rule4aEquation := rfl
    rule4bResult := compareOccurrenceRule4bAuthoritative? mol aux fuel left right
    rule4bEquation := rfl
    rule4cResult := authoritativeRule4cStage? mol aux fuel left right
    rule4cEquation := rfl
    rule5Result := compareOccurrenceRule5Authoritative? mol aux fuel left right
    rule5Equation := rfl
    precedenceEquation := by
      rw [← compareOccurrenceBranchesAuthoritative?_factorization]
      exact fullEquation }

/-- A successful complete comparison is certified either by the already proved fast-path stage
decomposition or, after a literal fast-path failure, by the width-unbounded stage decomposition. -/
inductive CompleteRule45Evaluation (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (decision : OccurrenceComparison) : Prop where
  | fast
      (evaluation : Rule45Evaluation (mol := mol) aux fuel
        { left := left, right := right, decision := decision }) :
      CompleteRule45Evaluation mol aux fuel left right decision
  | fallback
      (fastNone : compareOccurrenceBranches? mol aux fuel left right = none)
      (evaluation : AuthoritativeRule45Evaluation mol aux fuel left right decision) :
      CompleteRule45Evaluation mol aux fuel left right decision

theorem CompleteRule45Evaluation.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {left right : CanonicalRerootCursor} {decision : OccurrenceComparison}
    (evaluation : CompleteRule45Evaluation mol aux fuel left right decision) :
    compareOccurrenceBranchesComplete? mol aux fuel left right = some decision := by
  cases evaluation with
  | fast evaluation => simp [compareOccurrenceBranchesComplete?, evaluation.production_eq]
  | fallback fastNone evaluation =>
      simp [compareOccurrenceBranchesComplete?, fastNone, evaluation.production_eq]

/-- Every successful complete comparison yields primitive-stage evidence for the path actually
taken. -/
theorem completeRule45Evaluation_of_production
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (decision : OccurrenceComparison)
    (computed : compareOccurrenceBranchesComplete? mol aux fuel left right = some decision) :
    CompleteRule45Evaluation mol aux fuel left right decision := by
  unfold compareOccurrenceBranchesComplete? at computed
  cases fastEq : compareOccurrenceBranches? mol aux fuel left right with
  | none =>
      exact .fallback fastEq
        (authoritativeRule45Evaluation mol aux fuel left right decision (by
          simpa [fastEq] using computed))
  | some fastDecision =>
      have decisionEq : fastDecision = decision := by simpa [fastEq] using computed
      subst fastDecision
      exact .fast (rule45Evaluation (mol := mol) aux fuel
        { left := left, right := right, decision := decision } fastEq)

/-! ## Structural sort and strict-adjacency certificates -/

inductive AuthoritativeInsertOccurrenceDerivation (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat) (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop where
  | nil : AuthoritativeInsertOccurrenceDerivation mol aux fuel candidate [] ([candidate], 0)
  | before (head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
      (decision : OccurrenceComparison)
      (stage : CompleteRule45Evaluation mol aux fuel candidate head decision)
      (not_lt : (decision.ordering == Ordering.lt) = false) :
      AuthoritativeInsertOccurrenceDerivation mol aux fuel candidate (head :: tail)
        (candidate :: head :: tail, if decision.pseudo then 1 else 0)
  | after (head : CanonicalRerootCursor) (tail inserted : List CanonicalRerootCursor)
      (count : Nat) (decision : OccurrenceComparison)
      (stage : CompleteRule45Evaluation mol aux fuel candidate head decision)
      (is_lt : (decision.ordering == Ordering.lt) = true)
      (deeper : AuthoritativeInsertOccurrenceDerivation mol aux fuel candidate tail
        (inserted, count)) :
      AuthoritativeInsertOccurrenceDerivation mol aux fuel candidate (head :: tail)
        (head :: inserted, (if decision.pseudo then 1 else 0) + count)

theorem AuthoritativeInsertOccurrenceDerivation.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {candidate : CanonicalRerootCursor} {input : List CanonicalRerootCursor}
    {output : List CanonicalRerootCursor × Nat}
    (derivation : AuthoritativeInsertOccurrenceDerivation mol aux fuel candidate input output) :
    insertOccurrenceTrackedAuthoritative? mol aux fuel candidate input = some output := by
  induction derivation with
  | nil => rfl
  | before head tail decision stage not_lt =>
      have not_lt' : decision.ordering ≠ Ordering.lt := by simpa using not_lt
      simp [insertOccurrenceTrackedAuthoritative?, stage.production_eq, not_lt']
  | after head tail inserted count decision stage is_lt deeper inductionHypothesis =>
      have is_lt' : decision.ordering = Ordering.lt := by simpa using is_lt
      simp [insertOccurrenceTrackedAuthoritative?, stage.production_eq, is_lt',
        inductionHypothesis]

theorem authoritativeInsertOccurrenceDerivation_of_production
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) (input : List CanonicalRerootCursor)
    (output : List CanonicalRerootCursor × Nat)
    (computed : insertOccurrenceTrackedAuthoritative? mol aux fuel candidate input =
      some output) :
    AuthoritativeInsertOccurrenceDerivation mol aux fuel candidate input output := by
  induction input generalizing output with
  | nil =>
      simp [insertOccurrenceTrackedAuthoritative?] at computed
      subst output
      exact .nil
  | cons head tail inductionHypothesis =>
      simp only [insertOccurrenceTrackedAuthoritative?] at computed
      cases comparisonEq : compareOccurrenceBranchesComplete? mol aux fuel candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          cases isLt : decision.ordering == Ordering.lt with
          | false =>
              have notLt : decision.ordering ≠ Ordering.lt := by simpa using isLt
              have direct : insertOccurrenceTrackedAuthoritative? mol aux fuel candidate
                  (head :: tail) =
                    some (candidate :: head :: tail, if decision.pseudo then 1 else 0) := by
                simp [insertOccurrenceTrackedAuthoritative?, comparisonEq, notLt]
              have outputEq : output =
                  (candidate :: head :: tail, if decision.pseudo then 1 else 0) :=
                Option.some.inj (computed.symm.trans direct)
              subst output
              exact .before head tail decision
                (completeRule45Evaluation_of_production mol aux fuel candidate head decision
                  comparisonEq) isLt
          | true =>
              have isLt' : decision.ordering = Ordering.lt := by simpa using isLt
              cases deeperEq : insertOccurrenceTrackedAuthoritative? mol aux fuel candidate tail with
              | none =>
                  simp [comparisonEq, isLt', deeperEq]
                    at computed
              | some deeper =>
                  have direct : insertOccurrenceTrackedAuthoritative? mol aux fuel candidate
                      (head :: tail) = some (head :: deeper.1,
                        (if decision.pseudo then 1 else 0) + deeper.2) := by
                    simp [insertOccurrenceTrackedAuthoritative?, comparisonEq, isLt', deeperEq]
                  have outputEq : output = (head :: deeper.1,
                      (if decision.pseudo then 1 else 0) + deeper.2) :=
                    Option.some.inj (computed.symm.trans direct)
                  subst output
                  exact .after head tail deeper.1 deeper.2 decision
                    (completeRule45Evaluation_of_production mol aux fuel candidate head decision
                      comparisonEq) isLt
                    (inductionHypothesis deeper deeperEq)

inductive AuthoritativeSortOccurrencesDerivation (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop where
  | nil : AuthoritativeSortOccurrencesDerivation mol aux fuel [] ([], 0)
  | cons (cursor : CanonicalRerootCursor) (cursors : List CanonicalRerootCursor)
      (sorted inserted : List CanonicalRerootCursor × Nat)
      (tail : AuthoritativeSortOccurrencesDerivation mol aux fuel cursors sorted)
      (insertion : AuthoritativeInsertOccurrenceDerivation mol aux fuel cursor sorted.1 inserted) :
      AuthoritativeSortOccurrencesDerivation mol aux fuel (cursor :: cursors)
        (inserted.1, sorted.2 + inserted.2)

theorem AuthoritativeSortOccurrencesDerivation.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List CanonicalRerootCursor × Nat}
    (derivation : AuthoritativeSortOccurrencesDerivation mol aux fuel input output) :
    sortOccurrencesTrackedAuthoritative? mol aux fuel input = some output := by
  induction derivation with
  | nil => rfl
  | cons cursor cursors sorted inserted tail insertion tailHypothesis =>
      simp [sortOccurrencesTrackedAuthoritative?, tailHypothesis, insertion.production_eq]

theorem authoritativeSortOccurrencesDerivation_of_production
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor) (output : List CanonicalRerootCursor × Nat)
    (computed : sortOccurrencesTrackedAuthoritative? mol aux fuel input = some output) :
    AuthoritativeSortOccurrencesDerivation mol aux fuel input output := by
  induction input generalizing output with
  | nil =>
      simp [sortOccurrencesTrackedAuthoritative?] at computed
      subst output
      exact .nil
  | cons cursor cursors inductionHypothesis =>
      simp only [sortOccurrencesTrackedAuthoritative?] at computed
      cases sortedEq : sortOccurrencesTrackedAuthoritative? mol aux fuel cursors with
      | none => simp [sortedEq] at computed
      | some sorted =>
          cases insertedEq : insertOccurrenceTrackedAuthoritative? mol aux fuel cursor sorted.1 with
          | none => simp [sortedEq, insertedEq] at computed
          | some inserted =>
              simp [sortedEq, insertedEq] at computed
              subst output
              exact .cons cursor cursors sorted inserted
                (inductionHypothesis sorted sortedEq)
                (authoritativeInsertOccurrenceDerivation_of_production mol aux fuel cursor
                  sorted.1 inserted insertedEq)

inductive AuthoritativeAdjacentComparisonsDerivation (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → List OccurrenceComparison → Prop where
  | nil : AuthoritativeAdjacentComparisonsDerivation mol aux fuel [] []
  | singleton (cursor : CanonicalRerootCursor) :
      AuthoritativeAdjacentComparisonsDerivation mol aux fuel [cursor] []
  | cons (left right : CanonicalRerootCursor) (remaining : List CanonicalRerootCursor)
      (decision : OccurrenceComparison) (deeper : List OccurrenceComparison)
      (stage : CompleteRule45Evaluation mol aux fuel left right decision)
      (tail : AuthoritativeAdjacentComparisonsDerivation mol aux fuel
        (right :: remaining) deeper) :
      AuthoritativeAdjacentComparisonsDerivation mol aux fuel (left :: right :: remaining)
        (decision :: deeper)

theorem AuthoritativeAdjacentComparisonsDerivation.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List OccurrenceComparison}
    (derivation : AuthoritativeAdjacentComparisonsDerivation mol aux fuel input output) :
    compareOccurrenceAdjacentPairsAuthoritative? mol aux fuel input = some output := by
  induction derivation with
  | nil => rfl
  | singleton cursor => rfl
  | cons left right remaining decision deeper stage tail inductionHypothesis =>
      simp [compareOccurrenceAdjacentPairsAuthoritative?, stage.production_eq,
        inductionHypothesis]

theorem authoritativeAdjacentComparisonsDerivation_of_production
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor) (output : List OccurrenceComparison)
    (computed : compareOccurrenceAdjacentPairsAuthoritative? mol aux fuel input = some output) :
    AuthoritativeAdjacentComparisonsDerivation mol aux fuel input output := by
  induction input generalizing output with
  | nil =>
      simp [compareOccurrenceAdjacentPairsAuthoritative?] at computed
      subst output
      exact .nil
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [compareOccurrenceAdjacentPairsAuthoritative?] at computed
          subst output
          exact .singleton left
      | cons right remaining =>
          simp only [compareOccurrenceAdjacentPairsAuthoritative?] at computed
          cases comparisonEq : compareOccurrenceBranchesComplete? mol aux fuel left right with
          | none => simp [comparisonEq] at computed
          | some decision =>
              cases deeperEq : compareOccurrenceAdjacentPairsAuthoritative? mol aux fuel
                  (right :: remaining) with
              | none => simp [comparisonEq, deeperEq] at computed
              | some deeper =>
                  simp [comparisonEq, deeperEq] at computed
                  subst output
                  exact .cons left right remaining decision deeper
                    (completeRule45Evaluation_of_production mol aux fuel left right decision
                      comparisonEq)
                    (inductionHypothesis deeper deeperEq)

/-! ## Final authoritative occurrence-fact relation -/

/-- Independent primitive-stage certificate for one successful authoritative occurrence fact.
It does not contain an `legacyOccurrenceFactAuthoritative? = some ...` premise. -/
structure LegacyAuthoritativeOrdinaryFactCertificate (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  spec : AtomSpec
  parity : TetrahedralInputParity
  roots : List CanonicalRerootCursor
  sorted : List CanonicalRerootCursor × Nat
  positions : List Nat
  decisions : List OccurrenceComparison
  atom_spec : mol.atomAt? node.atom = some spec
  tetrahedral : spec.tetrahedral? = some parity
  frame : occurrenceLigandFrame? mol node = some roots
  ranking : AuthoritativeSortOccurrencesDerivation mol aux fuel roots sorted
  positions_eq :
    (sorted.1.mapM fun cursor =>
      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
        fun entry => entry.1 == cursor.node.atom).map Prod.snd) = some positions
  comparisons : AuthoritativeAdjacentComparisonsDerivation mol aux fuel sorted.1 decisions
  strict : decisions.all (fun decision => decision.ordering != Ordering.eq) = true
  fact_eq : fact =
    { key := canonicalOccurrenceKey node
      atom := node.atom
      descriptor := RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions)
      uppercase := (decisions.filter fun decision => decision.pseudo).length % 2 == 0
      priorityPositions := positions }

/-- Proof-irrelevant declarative meaning of a successful authoritative occurrence fact. -/
def LegacyAuthoritativeOrdinaryFactClauses (mol : RawMolecule) (aux : OccurrenceAuxState)
    (fuel : Nat) (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) : Prop :=
  Nonempty (LegacyAuthoritativeOrdinaryFactCertificate mol aux fuel node fact)

theorem LegacyAuthoritativeOrdinaryFactClauses.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (clauses : LegacyAuthoritativeOrdinaryFactClauses mol aux fuel node fact) :
    legacyOccurrenceFactAuthoritative? mol fuel aux node = some fact := by
  rcases clauses with ⟨certificate⟩
  have allStrict := List.all_eq_true.mp certificate.strict
  simp [legacyOccurrenceFactAuthoritative?, certificate.atom_spec, certificate.tetrahedral,
    certificate.frame, certificate.ranking.production_eq, certificate.positions_eq,
    certificate.comparisons.production_eq, ← certificate.fact_eq]
  intro decision member
  simpa using allStrict decision member

/-- Every successful authoritative occurrence fact yields the primitive-stage certificate. -/
theorem legacyAuthoritativeOrdinaryFactClauses_of_production
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (computed : legacyOccurrenceFactAuthoritative? mol fuel aux node = some fact) :
    LegacyAuthoritativeOrdinaryFactClauses mol aux fuel node fact := by
  refine ⟨?_⟩
  unfold legacyOccurrenceFactAuthoritative? at computed
  cases atomEq : mol.atomAt? node.atom with
  | none => simp [atomEq] at computed
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none => simp [atomEq, parityEq] at computed
      | some parity =>
          cases frameEq : occurrenceLigandFrame? mol node with
          | none => simp [atomEq, frameEq] at computed
          | some roots =>
              cases rankingEq : sortOccurrencesTrackedAuthoritative? mol aux fuel roots with
              | none => simp [atomEq, frameEq, rankingEq] at computed
              | some sorted =>
                  cases positionsEq : (sorted.1.mapM fun cursor =>
                      ((mol.ligandsWithLonePair node.atom).zipIdx.find?
                        fun entry => entry.1 == cursor.node.atom).map Prod.snd) with
                  | none =>
                      simp [atomEq, frameEq, rankingEq, positionsEq] at computed
                  | some positions =>
                      cases decisionsEq : compareOccurrenceAdjacentPairsAuthoritative? mol aux fuel
                          sorted.1 with
                      | none =>
                          simp [atomEq, frameEq, rankingEq, positionsEq,
                            decisionsEq] at computed
                      | some decisions =>
                          have simplified := computed
                          simp [atomEq, parityEq, frameEq, rankingEq, positionsEq,
                            decisionsEq] at simplified
                          have strictEq : decisions.all
                              (fun decision => decision.ordering != Ordering.eq) = true := by
                            simpa [List.all_eq_true] using simplified.1
                          have factEq : fact =
                              { key := canonicalOccurrenceKey node
                                atom := node.atom
                                descriptor := RawMolecule.descriptorOfParity parity
                                  (RawMolecule.permutationIsEven positions)
                                uppercase :=
                                  (decisions.filter fun decision => decision.pseudo).length % 2 == 0
                                priorityPositions := positions } := simplified.2.symm
                          exact
                            { spec := spec
                              parity := parity
                              roots := roots
                              sorted := sorted
                              positions := positions
                              decisions := decisions
                              atom_spec := atomEq
                              tetrahedral := parityEq
                              frame := frameEq
                              ranking := authoritativeSortOccurrencesDerivation_of_production
                                mol aux fuel roots sorted rankingEq
                              positions_eq := positionsEq
                              comparisons :=
                                authoritativeAdjacentComparisonsDerivation_of_production
                                  mol aux fuel sorted.1 decisions decisionsEq
                              strict := strictEq
                              fact_eq := factEq }

/-- Exact independent-certificate boundary for the width-unbounded occurrence fact. -/
theorem legacyAuthoritativeOrdinaryFactClauses_iff_production
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) :
    LegacyAuthoritativeOrdinaryFactClauses mol aux fuel node fact ↔
      legacyOccurrenceFactAuthoritative? mol fuel aux node = some fact :=
  ⟨LegacyAuthoritativeOrdinaryFactClauses.production_eq,
    legacyAuthoritativeOrdinaryFactClauses_of_production⟩

/-- Primitive evidence for the profile-selected authoritative evaluator. Legacy and repaired
comparisons retain separate derivations; no final fact equation is a certificate field. -/
inductive AuthoritativeOrdinaryFactCertificate (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  | legacy (unavailable : FrameRuntime.profile? mol node = none)
      (certificate : LegacyAuthoritativeOrdinaryFactCertificate mol aux fuel node fact)
  | framed (certificate : FramedOrdinaryConformance.OrdinaryFactCertificateComplete
      (mol := mol) true aux fuel node fact)

def AuthoritativeOrdinaryFactClauses (mol : RawMolecule) (aux : OccurrenceAuxState)
    (fuel : Nat) (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) : Prop :=
  Nonempty (AuthoritativeOrdinaryFactCertificate mol aux fuel node fact)

theorem AuthoritativeOrdinaryFactClauses.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (clauses : AuthoritativeOrdinaryFactClauses mol aux fuel node fact) :
    occurrenceFactAuthoritative? mol fuel aux node = some fact := by
  rcases clauses with ⟨certificate⟩
  cases certificate with
  | legacy unavailable certificate =>
      rw [occurrenceFactAuthoritative?_eq_legacy_of_profile_none mol fuel aux node unavailable]
      exact LegacyAuthoritativeOrdinaryFactClauses.production_eq ⟨certificate⟩
  | framed certificate =>
      rw [occurrenceFactAuthoritative?_eq_framed_of_profile_some mol fuel aux node
        certificate.profile certificate.profile_eq,
        framedOccurrenceFactAuthoritative?_eq_complete]
      exact certificate.production_eq

theorem authoritativeOrdinaryFactClauses_of_production
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (computed : occurrenceFactAuthoritative? mol fuel aux node = some fact) :
    AuthoritativeOrdinaryFactClauses mol aux fuel node fact := by
  cases profileEq : FrameRuntime.profile? mol node with
  | none =>
      have legacyComputed : legacyOccurrenceFactAuthoritative? mol fuel aux node = some fact := by
        simpa only [occurrenceFactAuthoritative?, profileEq] using computed
      rcases legacyAuthoritativeOrdinaryFactClauses_of_production legacyComputed with ⟨certificate⟩
      exact ⟨.legacy profileEq certificate⟩
  | some profile =>
      have framedComputed : FramedCompleteRuntime.occurrenceFactComplete?
          mol true fuel aux node = some fact := by
        rw [← framedOccurrenceFactAuthoritative?_eq_complete]
        simpa only [occurrenceFactAuthoritative?, profileEq] using computed
      rcases FramedOrdinaryConformance.ordinaryFactClausesComplete_of_production
        framedComputed with ⟨certificate⟩
      exact ⟨.framed certificate⟩

theorem authoritativeOrdinaryFactClauses_iff_production
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) :
    AuthoritativeOrdinaryFactClauses mol aux fuel node fact ↔
      occurrenceFactAuthoritative? mol fuel aux node = some fact :=
  ⟨AuthoritativeOrdinaryFactClauses.production_eq,
    authoritativeOrdinaryFactClauses_of_production⟩

/-- Independent certificate for the public authoritative tetrahedral fact wrapper. -/
def AuthoritativeTetrahedralOccurrenceFactJudgment (mol : RawMolecule) (fuel center : Nat)
    (fact : RawDescriptorFact) : Prop :=
  ∃ aux occurrenceFact,
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    AuthoritativeOrdinaryFactClauses mol aux fuel (canonicalCenterRoot center) occurrenceFact ∧
    fact =
      { atom := center
        descriptor := occurrenceFact.descriptor
        uppercase := occurrenceFact.uppercase
        evidenceSize := max 1 aux.length
        decisiveRule? := none
        descriptorDependentPairs := aux.length
        priorityPositions := occurrenceFact.priorityPositions }

/-- A public authoritative tetrahedral fact is emitted exactly when the independently decomposed
primitive-stage judgment holds. -/
theorem tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_judgment
    (mol : RawMolecule) (fuel center : Nat) (fact : RawDescriptorFact) :
    tetrahedralOccurrenceFactAuthoritative? mol fuel center = some fact ↔
      AuthoritativeTetrahedralOccurrenceFactJudgment mol fuel center fact := by
  constructor
  · intro computed
    unfold tetrahedralOccurrenceFactAuthoritative? at computed
    cases auxEq : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
    | none => simp [auxEq] at computed
    | some aux =>
        cases occurrenceEq : occurrenceFactAuthoritative? mol fuel aux
            (canonicalCenterRoot center) with
        | none => simp [auxEq, occurrenceEq] at computed
        | some occurrenceFact =>
            have factEq : fact =
                { atom := center
                  descriptor := occurrenceFact.descriptor
                  uppercase := occurrenceFact.uppercase
                  evidenceSize := max 1 aux.length
                  decisiveRule? := none
                  descriptorDependentPairs := aux.length
                  priorityPositions := occurrenceFact.priorityPositions } := by
              simpa [auxEq, occurrenceEq] using computed.symm
            exact ⟨aux, occurrenceFact, auxEq,
              authoritativeOrdinaryFactClauses_of_production occurrenceEq, factEq⟩
  · rintro ⟨aux, occurrenceFact, auxEq, clauses, rfl⟩
    simp [tetrahedralOccurrenceFactAuthoritative?, auxEq, clauses.production_eq]

end TetraStereo.OneCenter
