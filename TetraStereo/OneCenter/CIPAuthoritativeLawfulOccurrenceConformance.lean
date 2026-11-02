import TetraStereo.UniversalProof.NextFrontier.FramedSuccessfulOrderingTransitivity
import TetraStereo.OneCenter.CIPAuthoritativeStereoAssignmentConformance
import TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws
import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceDescriptorComparatorLaws

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Lawful unary-key evidence for authoritative occurrence assignments

The primitive-stage occurrence certificate records which comparison path executed. This module
strengthens it with the independently proved unary-key factor for every comparison used by
insertion sorting and by the final adjacent strictness check. Consequently a public authoritative
tetrahedral override carries a lawful comparison witness all the way to its emitted descriptor.
-/

/-- A complete Rules-1a--5 comparison is backed either by the lawful bounded fast key or, after
literal fast-path failure, by the lawful five-slot authoritative key. -/
inductive CompleteRule45LawfulFactor (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (decision : OccurrenceComparison) : Prop where
  | fast
      (computed : compareOccurrenceBranches? mol aux fuel left right = some decision)
      (factor :
        ProductionCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
          (ProductionCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
            mol aux fuel left)
          (ProductionCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
            mol aux fuel right) = decision.ordering) :
      CompleteRule45LawfulFactor mol aux fuel left right decision
  | fallback
      (fastNone : compareOccurrenceBranches? mol aux fuel left right = none)
      (computed : compareOccurrenceBranchesAuthoritative? mol aux fuel left right = some decision)
      (factor :
        AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareFailClosedOccurrenceBranchProjectedKeys
          (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
            mol aux fuel left)
          (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.buildFailClosedOccurrenceBranchProjectedKey
            mol aux fuel right) = decision.ordering) :
      CompleteRule45LawfulFactor mol aux fuel left right decision

/-- Every primitive-stage evaluation retained by the complete comparator yields its corresponding
lawful unary-key factor. -/
theorem CompleteRule45Evaluation.lawfulFactor
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {left right : CanonicalRerootCursor} {decision : OccurrenceComparison}
    (evaluation : CompleteRule45Evaluation mol aux fuel left right decision) :
    CompleteRule45LawfulFactor mol aux fuel left right decision := by
  cases evaluation with
  | fast evaluation =>
      have computed := evaluation.production_eq
      exact .fast computed
        (ProductionCIPOccurrenceDescriptorComparatorLaws.compareOccurrenceBranches_ordering_success_failClosed_factors
            mol aux fuel left right decision computed)
  | fallback fastNone evaluation =>
      have computed := evaluation.production_eq
      exact .fallback fastNone computed
        (AuthoritativeCIPOccurrenceDescriptorComparatorLaws.compareOccurrenceBranches_ordering_success_failClosed_factors
            mol aux fuel left right decision computed)

/-! ## Lawfulness propagated through the exact comparison traces -/

inductive LawfulAuthoritativeInsertOccurrenceDerivation (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat) (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop where
  | nil :
      LawfulAuthoritativeInsertOccurrenceDerivation mol aux fuel candidate [] ([candidate], 0)
  | before (head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
      (decision : OccurrenceComparison)
      (stage : CompleteRule45Evaluation mol aux fuel candidate head decision)
      (lawful : CompleteRule45LawfulFactor mol aux fuel candidate head decision)
      (not_lt : (decision.ordering == Ordering.lt) = false) :
      LawfulAuthoritativeInsertOccurrenceDerivation mol aux fuel candidate (head :: tail)
        (candidate :: head :: tail, if decision.pseudo then 1 else 0)
  | after (head : CanonicalRerootCursor) (tail inserted : List CanonicalRerootCursor)
      (count : Nat) (decision : OccurrenceComparison)
      (stage : CompleteRule45Evaluation mol aux fuel candidate head decision)
      (lawful : CompleteRule45LawfulFactor mol aux fuel candidate head decision)
      (is_lt : (decision.ordering == Ordering.lt) = true)
      (deeper : LawfulAuthoritativeInsertOccurrenceDerivation mol aux fuel candidate tail
        (inserted, count)) :
      LawfulAuthoritativeInsertOccurrenceDerivation mol aux fuel candidate (head :: tail)
        (head :: inserted, (if decision.pseudo then 1 else 0) + count)

theorem AuthoritativeInsertOccurrenceDerivation.lawful
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {candidate : CanonicalRerootCursor} {input : List CanonicalRerootCursor}
    {output : List CanonicalRerootCursor × Nat}
    (derivation : AuthoritativeInsertOccurrenceDerivation mol aux fuel candidate input output) :
    LawfulAuthoritativeInsertOccurrenceDerivation mol aux fuel candidate input output := by
  induction derivation with
  | nil => exact .nil
  | before head tail decision stage not_lt =>
      exact .before head tail decision stage stage.lawfulFactor not_lt
  | after head tail inserted count decision stage is_lt deeper inductionHypothesis =>
      exact .after head tail inserted count decision stage stage.lawfulFactor is_lt
        inductionHypothesis

inductive LawfulAuthoritativeSortOccurrencesDerivation (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop where
  | nil : LawfulAuthoritativeSortOccurrencesDerivation mol aux fuel [] ([], 0)
  | cons (cursor : CanonicalRerootCursor) (cursors : List CanonicalRerootCursor)
      (sorted inserted : List CanonicalRerootCursor × Nat)
      (tail : LawfulAuthoritativeSortOccurrencesDerivation mol aux fuel cursors sorted)
      (insertion : LawfulAuthoritativeInsertOccurrenceDerivation mol aux fuel cursor
        sorted.1 inserted) :
      LawfulAuthoritativeSortOccurrencesDerivation mol aux fuel (cursor :: cursors)
        (inserted.1, sorted.2 + inserted.2)

theorem AuthoritativeSortOccurrencesDerivation.lawful
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List CanonicalRerootCursor × Nat}
    (derivation : AuthoritativeSortOccurrencesDerivation mol aux fuel input output) :
    LawfulAuthoritativeSortOccurrencesDerivation mol aux fuel input output := by
  induction derivation with
  | nil => exact .nil
  | cons cursor cursors sorted inserted tail insertion tailLawful =>
      exact .cons cursor cursors sorted inserted tailLawful insertion.lawful

inductive LawfulAuthoritativeAdjacentComparisonsDerivation (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → List OccurrenceComparison → Prop where
  | nil : LawfulAuthoritativeAdjacentComparisonsDerivation mol aux fuel [] []
  | singleton (cursor : CanonicalRerootCursor) :
      LawfulAuthoritativeAdjacentComparisonsDerivation mol aux fuel [cursor] []
  | cons (left right : CanonicalRerootCursor) (remaining : List CanonicalRerootCursor)
      (decision : OccurrenceComparison) (deeper : List OccurrenceComparison)
      (stage : CompleteRule45Evaluation mol aux fuel left right decision)
      (lawful : CompleteRule45LawfulFactor mol aux fuel left right decision)
      (tail : LawfulAuthoritativeAdjacentComparisonsDerivation mol aux fuel
        (right :: remaining) deeper) :
      LawfulAuthoritativeAdjacentComparisonsDerivation mol aux fuel
        (left :: right :: remaining) (decision :: deeper)

theorem AuthoritativeAdjacentComparisonsDerivation.lawful
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List OccurrenceComparison}
    (derivation : AuthoritativeAdjacentComparisonsDerivation mol aux fuel input output) :
    LawfulAuthoritativeAdjacentComparisonsDerivation mol aux fuel input output := by
  induction derivation with
  | nil => exact .nil
  | singleton cursor => exact .singleton cursor
  | cons left right remaining decision deeper stage tail tailLawful =>
      exact .cons left right remaining decision deeper stage stage.lawfulFactor tailLawful

/-! ## Lawfulness for the fixed-profile comparison trace -/

open FramedOrdinaryConformance

/-- Each framed comparison is the comparison of two independently constructed keys in the
same fixed context. The comparator law is proved globally and the factor is derived from the
primitive stage evaluation; neither is an additional public caller hypothesis. -/
structure FramedRule45LawfulFactor (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (aux : OccurrenceAuxState) (fuel : Nat)
    (comparison : OccurrenceComparedPair mol aux fuel) : Prop where
  comparator_lawful : Std.TransCmp FramedSuccessfulOrderingTransitivity.compareFullKey
  factor : FramedSuccessfulOrderingTransitivity.compareFullKey
    (FramedSuccessfulOrderingTransitivity.buildFullKey mol profile authoritative aux fuel
      comparison.left)
    (FramedSuccessfulOrderingTransitivity.buildFullKey mol profile authoritative aux fuel
      comparison.right) = comparison.decision.ordering

theorem FramedOrdinaryConformance.FrameRule45Evaluation.lawfulFactor
    {mol : RawMolecule} {profile : FrameRuntime.Profile} {authoritative : Bool}
    {aux : OccurrenceAuxState} {fuel : Nat} {comparison : OccurrenceComparedPair mol aux fuel}
    (evaluation : FrameRule45Evaluation (mol := mol) profile authoritative aux fuel comparison) :
    FramedRule45LawfulFactor mol profile authoritative aux fuel comparison :=
  ⟨FramedSuccessfulOrderingTransitivity.compareFullKey_transCmp,
    FramedSuccessfulOrderingTransitivity.decisionComplete?_success_factors
      mol profile authoritative aux fuel comparison.left comparison.right comparison.decision
      evaluation.production_eq⟩

/-- Exact insertion trace, including the profile-admission check in the empty-list case and the
metadata count at each observed comparison. -/
inductive LawfulFramedInsertOccurrenceDerivation (mol : RawMolecule)
    (profile : FrameRuntime.Profile) (authoritative : Bool)
    (aux : OccurrenceAuxState) (fuel : Nat) (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop where
  | nil (distance : Nat)
      (observed : FrameRuntime.cursor? mol profile (.actual candidate) = some distance) :
      LawfulFramedInsertOccurrenceDerivation mol profile authoritative aux fuel
        candidate [] ([candidate], 0)
  | before (head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
      (decision : OccurrenceComparison)
      (stage : FrameRule45Evaluation (mol := mol) profile authoritative aux fuel
        { left := candidate, right := head, decision := decision })
      (lawful : FramedRule45LawfulFactor mol profile authoritative aux fuel
        { left := candidate, right := head, decision := decision })
      (not_lt : (decision.ordering == Ordering.lt) = false) :
      LawfulFramedInsertOccurrenceDerivation mol profile authoritative aux fuel
        candidate (head :: tail)
        (candidate :: head :: tail, if decision.pseudo then 1 else 0)
  | after (head : CanonicalRerootCursor) (tail inserted : List CanonicalRerootCursor)
      (count : Nat) (decision : OccurrenceComparison)
      (stage : FrameRule45Evaluation (mol := mol) profile authoritative aux fuel
        { left := candidate, right := head, decision := decision })
      (lawful : FramedRule45LawfulFactor mol profile authoritative aux fuel
        { left := candidate, right := head, decision := decision })
      (is_lt : (decision.ordering == Ordering.lt) = true)
      (deeper : LawfulFramedInsertOccurrenceDerivation mol profile authoritative aux fuel
        candidate tail (inserted, count)) :
      LawfulFramedInsertOccurrenceDerivation mol profile authoritative aux fuel
        candidate (head :: tail)
        (head :: inserted, (if decision.pseudo then 1 else 0) + count)

theorem FramedOrdinaryConformance.FrameInsertOccurrenceDerivation.lawful
    {mol : RawMolecule} {profile : FrameRuntime.Profile} {authoritative : Bool}
    {aux : OccurrenceAuxState} {fuel : Nat} {candidate : CanonicalRerootCursor}
    {input : List CanonicalRerootCursor} {output : List CanonicalRerootCursor × Nat}
    (derivation : FrameInsertOccurrenceDerivation (mol := mol) profile authoritative aux fuel
      candidate input output) :
    LawfulFramedInsertOccurrenceDerivation mol profile authoritative aux fuel
      candidate input output := by
  induction derivation with
  | nil distance observed => exact .nil distance observed
  | before head tail decision stage not_lt =>
      exact .before head tail decision stage stage.lawfulFactor not_lt
  | after head tail inserted count decision stage is_lt deeper inductionHypothesis =>
      exact .after head tail inserted count decision stage stage.lawfulFactor is_lt
        inductionHypothesis

inductive LawfulFramedSortOccurrencesDerivation (mol : RawMolecule)
    (profile : FrameRuntime.Profile) (authoritative : Bool)
    (aux : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop where
  | nil : LawfulFramedSortOccurrencesDerivation mol profile authoritative aux fuel [] ([], 0)
  | cons (cursor : CanonicalRerootCursor) (cursors : List CanonicalRerootCursor)
      (sorted inserted : List CanonicalRerootCursor × Nat)
      (tail : LawfulFramedSortOccurrencesDerivation mol profile authoritative aux fuel cursors sorted)
      (insertion : LawfulFramedInsertOccurrenceDerivation mol profile authoritative aux fuel
        cursor sorted.1 inserted) :
      LawfulFramedSortOccurrencesDerivation mol profile authoritative aux fuel
        (cursor :: cursors) (inserted.1, sorted.2 + inserted.2)

theorem FramedOrdinaryConformance.FrameSortOccurrencesDerivation.lawful
    {mol : RawMolecule} {profile : FrameRuntime.Profile} {authoritative : Bool}
    {aux : OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List CanonicalRerootCursor × Nat}
    (derivation : FrameSortOccurrencesDerivation (mol := mol) profile authoritative aux fuel
      input output) :
    LawfulFramedSortOccurrencesDerivation mol profile authoritative aux fuel input output := by
  induction derivation with
  | nil => exact .nil
  | cons cursor cursors sorted inserted tail insertion tailLawful =>
      exact .cons cursor cursors sorted inserted tailLawful insertion.lawful

/-- The adjacency trace retains each ordered pair and the complete decision, including Rule4c
carrier and Rule5 pseudo metadata. Only its ordering is projected into the unary key. -/
inductive LawfulFramedAdjacentComparisonsDerivation (mol : RawMolecule)
    (profile : FrameRuntime.Profile) (authoritative : Bool)
    (aux : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → List (OccurrenceComparedPair mol aux fuel) → Prop where
  | nil : LawfulFramedAdjacentComparisonsDerivation mol profile authoritative aux fuel [] []
  | singleton (cursor : CanonicalRerootCursor) :
      LawfulFramedAdjacentComparisonsDerivation mol profile authoritative aux fuel [cursor] []
  | cons (left right : CanonicalRerootCursor) (remaining : List CanonicalRerootCursor)
      (decision : OccurrenceComparison) (deeper : List (OccurrenceComparedPair mol aux fuel))
      (stage : FrameRule45Evaluation (mol := mol) profile authoritative aux fuel
        { left := left, right := right, decision := decision })
      (lawful : FramedRule45LawfulFactor mol profile authoritative aux fuel
        { left := left, right := right, decision := decision })
      (tail : LawfulFramedAdjacentComparisonsDerivation mol profile authoritative aux fuel
        (right :: remaining) deeper) :
      LawfulFramedAdjacentComparisonsDerivation mol profile authoritative aux fuel
        (left :: right :: remaining)
        ({ left := left, right := right, decision := decision } :: deeper)

theorem FramedOrdinaryConformance.FrameAdjacentComparisonsDerivation.lawful
    {mol : RawMolecule} {profile : FrameRuntime.Profile} {authoritative : Bool}
    {aux : OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List (OccurrenceComparedPair mol aux fuel)}
    (derivation : FrameAdjacentComparisonsDerivation (mol := mol) profile authoritative aux fuel
      input output) :
    LawfulFramedAdjacentComparisonsDerivation mol profile authoritative aux fuel input output := by
  induction derivation with
  | nil => exact .nil
  | singleton cursor => exact .singleton cursor
  | cons left right remaining decision deeper stage tail tailLawful =>
      exact .cons left right remaining decision deeper stage stage.lawfulFactor tailLawful

/-- Primitive framed fact evidence, strengthened along both actual comparison traces. -/
structure LawfulFramedOrdinaryFactCertificate (mol : RawMolecule) (authoritative : Bool)
    (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  base : OrdinaryFactCertificateComplete (mol := mol) authoritative aux fuel node fact
  ranking : LawfulFramedSortOccurrencesDerivation mol base.profile authoritative aux fuel
    base.roots base.sorted
  comparisons : LawfulFramedAdjacentComparisonsDerivation mol base.profile authoritative aux fuel
    base.sorted.1 base.compared

/-- The old backend's trace certificate remains explicit and retains its original trace types. -/
structure LegacyLawfulAuthoritativeOrdinaryFactCertificate (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  base : LegacyAuthoritativeOrdinaryFactCertificate mol aux fuel node fact
  ranking : LawfulAuthoritativeSortOccurrencesDerivation mol aux fuel base.roots base.sorted
  comparisons : LawfulAuthoritativeAdjacentComparisonsDerivation mol aux fuel
    base.sorted.1 base.decisions

/-- Public lawfulness records the actual profile-selected backend. Framed failure has no legacy
fallback. Both branches retain primitive fact evidence and every ordering/strictness comparison. -/
inductive LawfulAuthoritativeOrdinaryFactCertificate (mol : RawMolecule)
    (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) where
  | legacy (unavailable : FrameRuntime.profile? mol node = none)
      (certificate : LegacyLawfulAuthoritativeOrdinaryFactCertificate mol aux fuel node fact)
  | framed (certificate : LawfulFramedOrdinaryFactCertificate mol true aux fuel node fact)

/-- Forget lawfulness annotations while preserving the selected primitive certificate. -/
def LawfulAuthoritativeOrdinaryFactCertificate.base
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact} :
    LawfulAuthoritativeOrdinaryFactCertificate mol aux fuel node fact →
      AuthoritativeOrdinaryFactCertificate mol aux fuel node fact
  | .legacy unavailable certificate => .legacy unavailable certificate.base
  | .framed certificate => .framed certificate.base

def LawfulAuthoritativeOrdinaryFactClauses (mol : RawMolecule) (aux : OccurrenceAuxState)
    (fuel : Nat) (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) : Prop :=
  Nonempty (LawfulAuthoritativeOrdinaryFactCertificate mol aux fuel node fact)

theorem LawfulAuthoritativeOrdinaryFactClauses.production_eq
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (clauses : LawfulAuthoritativeOrdinaryFactClauses mol aux fuel node fact) :
    occurrenceFactAuthoritative? mol fuel aux node = some fact := by
  rcases clauses with ⟨certificate⟩
  exact AuthoritativeOrdinaryFactClauses.production_eq ⟨certificate.base⟩

theorem lawfulAuthoritativeOrdinaryFactClauses_of_production
    {mol : RawMolecule} {aux : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {fact : OccurrenceAuxFact}
    (computed : occurrenceFactAuthoritative? mol fuel aux node = some fact) :
    LawfulAuthoritativeOrdinaryFactClauses mol aux fuel node fact := by
  rcases authoritativeOrdinaryFactClauses_of_production computed with ⟨base⟩
  cases base with
  | legacy unavailable certificate =>
      exact ⟨.legacy unavailable
        { base := certificate
          ranking := certificate.ranking.lawful
          comparisons := certificate.comparisons.lawful }⟩
  | framed certificate =>
      exact ⟨.framed
        { base := certificate
          ranking := certificate.ranking.lawful
          comparisons := certificate.comparisons.lawful }⟩

theorem lawfulAuthoritativeOrdinaryFactClauses_iff_production
    (mol : RawMolecule) (aux : OccurrenceAuxState) (fuel : Nat)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact) :
    LawfulAuthoritativeOrdinaryFactClauses mol aux fuel node fact ↔
      occurrenceFactAuthoritative? mol fuel aux node = some fact :=
  ⟨LawfulAuthoritativeOrdinaryFactClauses.production_eq,
    lawfulAuthoritativeOrdinaryFactClauses_of_production⟩

/-! ## Strengthened public descriptor boundary -/

def AuthoritativeTetrahedralOccurrenceFactLawfulJudgment
    (mol : RawMolecule) (fuel center : Nat) (fact : RawDescriptorFact) : Prop :=
  ∃ aux occurrenceFact,
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    LawfulAuthoritativeOrdinaryFactClauses mol aux fuel (canonicalCenterRoot center)
      occurrenceFact ∧
    fact =
      { atom := center
        descriptor := occurrenceFact.descriptor
        uppercase := occurrenceFact.uppercase
        evidenceSize := max 1 aux.length
        decisiveRule? := none
        descriptorDependentPairs := aux.length
        priorityPositions := occurrenceFact.priorityPositions }

theorem tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_lawfulJudgment
    (mol : RawMolecule) (fuel center : Nat) (fact : RawDescriptorFact) :
    tetrahedralOccurrenceFactAuthoritative? mol fuel center = some fact ↔
      AuthoritativeTetrahedralOccurrenceFactLawfulJudgment mol fuel center fact := by
  constructor
  · intro computed
    rcases (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_judgment
      mol fuel center fact).mp computed with ⟨aux, occurrenceFact, auxEq, clauses, factEq⟩
    exact ⟨aux, occurrenceFact, auxEq,
      lawfulAuthoritativeOrdinaryFactClauses_of_production clauses.production_eq, factEq⟩
  · rintro ⟨aux, occurrenceFact, auxEq, clauses, factEq⟩
    apply (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_judgment
      mol fuel center fact).mpr
    exact ⟨aux, occurrenceFact, auxEq,
      authoritativeOrdinaryFactClauses_of_production clauses.production_eq, factEq⟩

def AuthoritativeOccurrenceStereoAssignmentLawfulJudgment
    (result : ChemistryNormalizationResult) (center : Nat)
    (assignment : StereoAssignment) : Prop :=
  ∃ spec parity fact,
    result.parsed.atomAt? center = some spec ∧
    spec.tetrahedral? = some parity ∧
    result.parsed.withExplicitHydrogens.isExtendedTetrahedralParityCarrier center = false ∧
    AuthoritativeTetrahedralOccurrenceFactLawfulJudgment
      result.parsed.withExplicitHydrogens
      (analysisFuel result.parsed.withExplicitHydrogens) center fact ∧
    assignment =
      { unit := StereoUnit.tetrahedral center
        outcome := authoritativeOccurrenceOutcome fact }

theorem authoritativeOccurrenceStereoAssignmentJudgment_iff_lawful
    (result : ChemistryNormalizationResult) (center : Nat) (assignment : StereoAssignment) :
    AuthoritativeOccurrenceStereoAssignmentJudgment result center assignment ↔
      AuthoritativeOccurrenceStereoAssignmentLawfulJudgment result center assignment := by
  constructor
  · rintro ⟨spec, parity, fact, specEq, parityEq, extendedEq, factJudgment, assignmentEq⟩
    have factComputed :=
      (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_judgment
        result.parsed.withExplicitHydrogens
        (analysisFuel result.parsed.withExplicitHydrogens) center fact).mpr factJudgment
    exact ⟨spec, parity, fact, specEq, parityEq, extendedEq,
      (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_lawfulJudgment
        result.parsed.withExplicitHydrogens
        (analysisFuel result.parsed.withExplicitHydrogens) center fact).mp factComputed,
      assignmentEq⟩
  · rintro ⟨spec, parity, fact, specEq, parityEq, extendedEq, factJudgment, assignmentEq⟩
    have factComputed :=
      (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_lawfulJudgment
        result.parsed.withExplicitHydrogens
        (analysisFuel result.parsed.withExplicitHydrogens) center fact).mpr factJudgment
    exact ⟨spec, parity, fact, specEq, parityEq, extendedEq,
      (tetrahedralOccurrenceFactAuthoritative?_eq_some_iff_judgment
        result.parsed.withExplicitHydrogens
        (analysisFuel result.parsed.withExplicitHydrogens) center fact).mp factComputed,
      assignmentEq⟩

theorem ChemistryNormalizationResult.authoritativeOccurrenceAssignment?_eq_some_iff_lawful
    (result : ChemistryNormalizationResult) (center : Nat) (assignment : StereoAssignment) :
    result.authoritativeOccurrenceAssignment? center = some assignment ↔
      AuthoritativeOccurrenceStereoAssignmentLawfulJudgment result center assignment := by
  rw [result.authoritativeOccurrenceAssignment?_eq_some_iff_judgment]
  exact authoritativeOccurrenceStereoAssignmentJudgment_iff_lawful result center assignment

theorem ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences_member_native_or_lawful
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ result.analyzeWithAuthoritativeOccurrences) :
    (assignment ∈ analyzeNormalized result) ∨
      ∃ center,
        AuthoritativeOccurrenceStereoAssignmentLawfulJudgment result center assignment := by
  rcases result.analyzeWithAuthoritativeOccurrences_member_native_or_judged assignment member with
    native | ⟨center, judged⟩
  · exact Or.inl native
  · exact Or.inr ⟨center,
      (authoritativeOccurrenceStereoAssignmentJudgment_iff_lawful
        result center assignment).mp judged⟩

theorem analyzeCertifiedNormalized_member_native_or_authoritative_lawful
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified) :
    (assignment ∈ analyzeNormalized certified.result) ∨
      ∃ center, AuthoritativeOccurrenceStereoAssignmentLawfulJudgment
        certified.result center assignment := by
  exact certified.result.analyzeWithAuthoritativeOccurrences_member_native_or_lawful
    assignment (by simpa [analyzeCertifiedNormalized] using member)

end TetraStereo.OneCenter
