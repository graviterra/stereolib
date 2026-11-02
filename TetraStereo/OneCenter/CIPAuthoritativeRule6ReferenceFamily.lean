import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceCompleteness
import TetraStereo.OneCenter.Rule6ReferenceFamilyCore

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6ReferenceFamily

open RawMolecule
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPOccurrenceCompleteness
open AuthoritativeCIPOccurrenceCompleteness.DescriptorRule6HierarchySupport
open Rule6ReferenceFamilySemantics

abbrev IndexedOccurrenceCursor := CanonicalRerootCursor × Nat

def insertIndexedOccurrenceThroughRule6Authoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (reference fuel : Nat)
    (candidate : IndexedOccurrenceCursor) :
    List IndexedOccurrenceCursor → Option (List IndexedOccurrenceCursor × Nat × Bool)
  | [] => some ([candidate], 0, true)
  | low :: remaining => do
      let decision ← compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
        mol state reference fuel candidate.1 low.1
      let observed := if decision.pseudo then 1 else 0
      match decision.ordering with
      | .lt =>
          let deeper ← insertIndexedOccurrenceThroughRule6Authoritative? mol state reference fuel
            candidate remaining
          some (low :: deeper.1, observed + deeper.2.1, deeper.2.2)
      | .eq => some (candidate :: low :: remaining, observed, false)
      | .gt => some (candidate :: low :: remaining, observed, true)

def sortIndexedOccurrencesThroughRule6Authoritative? (mol : RawMolecule)
    (state : OccurrenceAuxState) (reference fuel : Nat) :
    List IndexedOccurrenceCursor → Option (List IndexedOccurrenceCursor × Nat × Bool)
  | [] => some ([], 0, true)
  | candidate :: remaining => do
      let sorted ← sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel
        remaining
      let inserted ← insertIndexedOccurrenceThroughRule6Authoritative? mol state reference fuel
        candidate sorted.1
      some (inserted.1, sorted.2.1 + inserted.2.1, sorted.2.2 && inserted.2.2)

def rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    (roots : List CanonicalRerootCursor) : Option Rule6TrackedRanking := do
  let tracked ← sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel
    roots.zipIdx
  some { positions := tracked.1.map Prod.snd
         pseudoComparisons := tracked.2.1
         unique := tracked.2.2 }

def CursorsFrom (roots : List CanonicalRerootCursor)
    (entries : List IndexedOccurrenceCursor) : Prop :=
  ∀ entry, entry ∈ entries → entry.1 ∈ roots

theorem insertIndexedOccurrenceThroughRule6Authoritative?_perm
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    (candidate : IndexedOccurrenceCursor) :
    ∀ entries inserted,
      insertIndexedOccurrenceThroughRule6Authoritative? mol state reference fuel
          candidate entries = some inserted →
        inserted.1.Perm (candidate :: entries)
  | [], inserted, computed => by
      simp [insertIndexedOccurrenceThroughRule6Authoritative?] at computed
      subst inserted
      rfl
  | low :: remaining, inserted, computed => by
      unfold insertIndexedOccurrenceThroughRule6Authoritative? at computed
      cases decisionEq : compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          mol state reference fuel candidate.1 low.1 with
      | none => simp [decisionEq] at computed
      | some decision =>
          simp only [decisionEq] at computed
          cases orderingEq : decision.ordering with
          | lt =>
              cases deeperEq : insertIndexedOccurrenceThroughRule6Authoritative? mol state
                  reference fuel candidate remaining with
              | none => simp [orderingEq, deeperEq] at computed
              | some deeper =>
                  simp [orderingEq, deeperEq] at computed
                  subst inserted
                  exact (List.Perm.cons low
                    (insertIndexedOccurrenceThroughRule6Authoritative?_perm mol state reference
                      fuel candidate remaining deeper deeperEq)).trans
                    (List.Perm.swap candidate low remaining)
          | eq =>
              simp [orderingEq] at computed
              subst inserted
              rfl
          | gt =>
              simp [orderingEq] at computed
              subst inserted
              rfl

theorem sortIndexedOccurrencesThroughRule6Authoritative?_perm
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat) :
    ∀ entries sorted,
      sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel entries =
          some sorted →
        sorted.1.Perm entries
  | [], sorted, computed => by
      simp [sortIndexedOccurrencesThroughRule6Authoritative?] at computed
      subst sorted
      rfl
  | candidate :: remaining, sorted, computed => by
      unfold sortIndexedOccurrencesThroughRule6Authoritative? at computed
      cases remainingEq : sortIndexedOccurrencesThroughRule6Authoritative? mol state reference
          fuel remaining with
      | none => simp [remainingEq] at computed
      | some remainingSorted =>
          simp only [remainingEq] at computed
          cases insertedEq : insertIndexedOccurrenceThroughRule6Authoritative? mol state reference
              fuel candidate remainingSorted.1 with
          | none => simp [insertedEq] at computed
          | some inserted =>
              simp [insertedEq] at computed
              subst sorted
              exact (insertIndexedOccurrenceThroughRule6Authoritative?_perm mol state reference
                fuel candidate remainingSorted.1 inserted insertedEq).trans
                (List.Perm.cons candidate
                  (sortIndexedOccurrencesThroughRule6Authoritative?_perm mol state reference fuel
                    remaining remainingSorted remainingEq))

theorem rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?_positions_perm
    (mol : RawMolecule) (state : OccurrenceAuxState) (reference fuel : Nat)
    (roots : List CanonicalRerootCursor) (ranking : Rule6TrackedRanking)
    (computed : rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
      mol state reference fuel roots = some ranking) :
    ranking.positions.Perm (List.range roots.length) := by
  unfold rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative? at computed
  cases sortedEq : sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel
      roots.zipIdx with
  | none => simp [sortedEq] at computed
  | some sorted =>
      simp [sortedEq] at computed
      subst ranking
      have sortedPerm := sortIndexedOccurrencesThroughRule6Authoritative?_perm mol state reference
        fuel roots.zipIdx sorted sortedEq
      have positionsPerm := sortedPerm.map Prod.snd
      simpa [List.range_eq_range'] using positionsPerm

theorem insertIndexedOccurrenceThroughRule6Authoritative?_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {reference fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left ∈ roots → right ∈ roots →
      ∃ decision,
        compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          mol state reference fuel left right = some decision)
    (candidate : IndexedOccurrenceCursor) (candidateMember : candidate.1 ∈ roots) :
    ∀ entries, CursorsFrom roots entries →
      ∃ inserted,
        insertIndexedOccurrenceThroughRule6Authoritative? mol state reference fuel
            candidate entries = some inserted ∧
          CursorsFrom roots inserted.1
  | [], _ => by
      exact ⟨([candidate], 0, true), rfl, by simp [CursorsFrom, candidateMember]⟩
  | low :: remaining, entriesFrom => by
      have lowMember : low.1 ∈ roots := entriesFrom low (by simp)
      rcases comparisonTotal candidate.1 low.1 candidateMember lowMember with
        ⟨decision, decisionEq⟩
      cases orderingEq : decision.ordering with
      | lt =>
          have remainingFrom : CursorsFrom roots remaining := by
            intro entry member
            exact entriesFrom entry (by simp [member])
          rcases insertIndexedOccurrenceThroughRule6Authoritative?_exists comparisonTotal
              candidate candidateMember remaining remainingFrom with
            ⟨deeper, deeperEq, deeperFrom⟩
          refine ⟨(low :: deeper.1,
              (if decision.pseudo then 1 else 0) + deeper.2.1, deeper.2.2), ?_, ?_⟩
          · simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq, orderingEq,
              deeperEq]
          · intro entry member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact lowMember
            · exact deeperFrom entry member
      | eq =>
          refine ⟨(candidate :: low :: remaining,
            (if decision.pseudo then 1 else 0), false), ?_, ?_⟩
          · simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq, orderingEq]
          · intro entry member
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | member
            · exact candidateMember
            · exact lowMember
            · exact entriesFrom entry (by simp [member])
      | gt =>
          refine ⟨(candidate :: low :: remaining,
            (if decision.pseudo then 1 else 0), true), ?_, ?_⟩
          · simp [insertIndexedOccurrenceThroughRule6Authoritative?, decisionEq, orderingEq]
          · intro entry member
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | member
            · exact candidateMember
            · exact lowMember
            · exact entriesFrom entry (by simp [member])

theorem sortIndexedOccurrencesThroughRule6Authoritative?_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {reference fuel : Nat}
    {roots : List CanonicalRerootCursor}
    (comparisonTotal : ∀ left right,
      left ∈ roots → right ∈ roots →
      ∃ decision,
        compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          mol state reference fuel left right = some decision) :
    ∀ entries, CursorsFrom roots entries →
      ∃ sorted,
        sortIndexedOccurrencesThroughRule6Authoritative? mol state reference fuel entries =
            some sorted ∧
          CursorsFrom roots sorted.1
  | [], _ => ⟨([], 0, true), rfl, by simp [CursorsFrom]⟩
  | candidate :: remaining, entriesFrom => by
      have candidateMember : candidate.1 ∈ roots := entriesFrom candidate (by simp)
      have remainingFrom : CursorsFrom roots remaining := by
        intro entry member
        exact entriesFrom entry (by simp [member])
      rcases sortIndexedOccurrencesThroughRule6Authoritative?_exists comparisonTotal
          remaining remainingFrom with ⟨sorted, sortedEq, sortedFrom⟩
      rcases insertIndexedOccurrenceThroughRule6Authoritative?_exists comparisonTotal
          candidate candidateMember sorted.1 sortedFrom with
        ⟨inserted, insertedEq, insertedFrom⟩
      refine ⟨(inserted.1, sorted.2.1 + inserted.2.1, sorted.2.2 && inserted.2.2), ?_,
        insertedFrom⟩
      simp [sortIndexedOccurrencesThroughRule6Authoritative?, sortedEq, insertedEq]

theorem roots_zipIdx_cursorsFrom (roots : List CanonicalRerootCursor) :
    CursorsFrom roots roots.zipIdx := by
  intro entry member
  simpa using List.fst_mem_of_mem_zipIdx member

theorem rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {reference fuel : Nat}
    (roots : List CanonicalRerootCursor)
    (comparisonTotal : ∀ left right,
      left ∈ roots → right ∈ roots →
      ∃ decision,
        compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?
          mol state reference fuel left right = some decision) :
    ∃ ranking,
      rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
        mol state reference fuel roots = some ranking := by
  rcases sortIndexedOccurrencesThroughRule6Authoritative?_exists comparisonTotal
      roots.zipIdx (roots_zipIdx_cursorsFrom roots) with ⟨sorted, sortedEq, _⟩
  exact ⟨{ positions := sorted.1.map Prod.snd
           pseudoComparisons := sorted.2.1
           unique := sorted.2.2 }, by
    simp [rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?, sortedEq]⟩

def authoritativeOccurrenceRule6RankingBackend (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) : ProductionRule6RankingBackend :=
  fun reference => rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?
    mol state reference fuel roots

/-- Final descriptor emitted by the uncapped authoritative all-reference family. -/
def authoritativeOccurrenceRule6FamilyDescriptor? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (parity : TetrahedralInputParity) (references : List Nat) : Option RS := do
  let ranking ← rankProductionRule6EquivalentReferencesWithBackend?
    (authoritativeOccurrenceRule6RankingBackend mol state fuel roots) parity references
  some (RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven ranking.positions))

/-- The descriptor-producing all-reference function is exactly the independent common-descriptor
semantics; no selected first reference can change the result. -/
theorem authoritativeOccurrenceRule6FamilyDescriptor?_eq_some_iff_commonDescriptor
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (parity : TetrahedralInputParity)
    (references : List Nat) (descriptor : RS) :
    authoritativeOccurrenceRule6FamilyDescriptor? mol state fuel roots parity references =
        some descriptor ↔
      CommonRule6Descriptor
        (authoritativeOccurrenceRule6RankingBackend mol state fuel roots)
        parity references descriptor := by
  let backend := authoritativeOccurrenceRule6RankingBackend mol state fuel roots
  constructor
  · intro emitted
    unfold authoritativeOccurrenceRule6FamilyDescriptor? at emitted
    change (do
        let ranking ← rankProductionRule6EquivalentReferencesWithBackend?
          backend parity references
        some (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions))) = some descriptor at emitted
    cases acceptedEq : rankProductionRule6EquivalentReferencesWithBackend?
        backend parity references with
    | none => simp [acceptedEq] at emitted
    | some first =>
        have descriptorEq : RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven first.positions) = descriptor := by
          simpa [acceptedEq] using emitted
        rcases rankProductionRule6EquivalentReferencesWithBackend?_sound
            backend parity references first acceptedEq with ⟨certificate⟩
        have referencesNonempty : references ≠ [] := by
          intro referencesEq
          simpa [referencesEq] using certificate.reference_head
        refine ⟨referencesNonempty, ?_⟩
        intro reference member
        rcases certificate.all_references reference member with
          ⟨ranking, rankingEq, unique, sameAsFirst⟩
        exact ⟨ranking, rankingEq, unique, sameAsFirst.trans descriptorEq⟩
  · intro common
    have commonExists : ∃ candidate,
        CommonRule6Descriptor backend parity references candidate :=
      ⟨descriptor, common⟩
    rcases
        (rankProductionRule6EquivalentReferencesWithBackend?_success_iff_commonDescriptor
          backend parity references).2 commonExists with ⟨first, acceptedEq⟩
    rcases rankProductionRule6EquivalentReferencesWithBackend?_sound
        backend parity references first acceptedEq with ⟨certificate⟩
    have firstMember : certificate.firstReferencePosition ∈ references := by
      cases references with
      | nil => exact False.elim (common.1 rfl)
      | cons head tail =>
          have headEq : certificate.firstReferencePosition = head := by
            simpa using certificate.reference_head.symm
          simp [headEq]
    rcases common.2 certificate.firstReferencePosition firstMember with
      ⟨ranking, rankingEq, _unique, rankingDescriptor⟩
    have rankingEqFirst : ranking = first :=
      Option.some.inj (rankingEq.symm.trans certificate.first_ranking)
    subst ranking
    unfold authoritativeOccurrenceRule6FamilyDescriptor?
    simp [backend, acceptedEq, rankingDescriptor]

theorem authoritativeOccurrenceRule6RankingBackend_total_of_chemical_applicability
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence) :
    ∀ reference,
      ∃ ranking,
        authoritativeOccurrenceRule6RankingBackend mol state (2 * mol.atomCount + 1)
            (occurrenceLigandCursors mol occurrence) reference = some ranking := by
  intro reference
  apply rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?_exists
  intro left right leftMember rightMember
  exact promoted_occurrence_ligand_comparison_exists_of_chemical_applicability centerBound
    wellFormed unique valence kekule reference occurrenceGenerated leftMember rightMember

theorem rankAuthoritativeOccurrenceEquivalentReferences_eq_none_iff_failureWitness
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    (parity : TetrahedralInputParity) (references : List Nat)
    (referencesNonempty : references ≠ []) :
    rankProductionRule6EquivalentReferencesWithBackend?
        (authoritativeOccurrenceRule6RankingBackend mol state (2 * mol.atomCount + 1)
          (occurrenceLigandCursors mol occurrence)) parity references = none ↔
      HasNonStrictRule6Reference
          (authoritativeOccurrenceRule6RankingBackend mol state (2 * mol.atomCount + 1)
            (occurrenceLigandCursors mol occurrence)) references ∨
        HasRule6ReferenceDescriptorConflict
          (authoritativeOccurrenceRule6RankingBackend mol state (2 * mol.atomCount + 1)
            (occurrenceLigandCursors mol occurrence)) parity references := by
  apply rankProductionRule6EquivalentReferencesWithBackend?_eq_none_iff_failureWitness
  · exact referencesNonempty
  · intro reference _member
    exact authoritativeOccurrenceRule6RankingBackend_total_of_chemical_applicability
      centerBound wellFormed unique valence kekule occurrenceGenerated reference

/-- On the chemically applicable occurrence domain, descriptor refusal has only the two semantic
Rule-6 causes: a non-strict reference ranking or a descriptor conflict between strict references.
Traversal, sorting, lookup, and finite-depth execution cannot be the cause. -/
theorem authoritativeOccurrenceRule6FamilyDescriptor?_eq_none_iff_failureWitness
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    (parity : TetrahedralInputParity) (references : List Nat)
    (referencesNonempty : references ≠ []) :
    authoritativeOccurrenceRule6FamilyDescriptor? mol state (2 * mol.atomCount + 1)
        (occurrenceLigandCursors mol occurrence) parity references = none ↔
      HasNonStrictRule6Reference
          (authoritativeOccurrenceRule6RankingBackend mol state (2 * mol.atomCount + 1)
            (occurrenceLigandCursors mol occurrence)) references ∨
        HasRule6ReferenceDescriptorConflict
          (authoritativeOccurrenceRule6RankingBackend mol state (2 * mol.atomCount + 1)
            (occurrenceLigandCursors mol occurrence)) parity references := by
  let backend := authoritativeOccurrenceRule6RankingBackend mol state (2 * mol.atomCount + 1)
    (occurrenceLigandCursors mol occurrence)
  have classification :=
    rankAuthoritativeOccurrenceEquivalentReferences_eq_none_iff_failureWitness
      (state := state) centerBound
      wellFormed unique valence kekule occurrenceGenerated parity references referencesNonempty
  constructor
  · intro descriptorNone
    unfold authoritativeOccurrenceRule6FamilyDescriptor? at descriptorNone
    change (do
        let ranking ← rankProductionRule6EquivalentReferencesWithBackend?
          backend parity references
        some (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions))) = none at descriptorNone
    have rankingNone : rankProductionRule6EquivalentReferencesWithBackend?
        backend parity references = none := by
      cases acceptedEq : rankProductionRule6EquivalentReferencesWithBackend?
          backend parity references with
      | none => rfl
      | some ranking => simp [acceptedEq] at descriptorNone
    exact classification.mp (by simpa [backend] using rankingNone)
  · intro failure
    have rankingNone := classification.mpr failure
    simp [authoritativeOccurrenceRule6FamilyDescriptor?, rankingNone]

end TetraStereo.OneCenter.AuthoritativeCIPRule6ReferenceFamily
