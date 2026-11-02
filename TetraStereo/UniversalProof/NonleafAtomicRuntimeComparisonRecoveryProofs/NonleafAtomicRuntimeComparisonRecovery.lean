import TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
import TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
















/-- Independent real provenance and an ACTUAL atom record; no topology, comparator or result field. -/
def ObservedReal (raw : RawMolecule) (cursor : CanonicalRerootCursor) : Prop :=
  cursor.node.provenance = CanonicalNodeProvenance.realAtom ∧
    ∃ spec, raw.atomAt? cursor.node.atom = some spec

theorem ObservedReal.bound (raw : RawMolecule) (cursor : CanonicalRerootCursor)
    (observed : ObservedReal raw cursor) : cursor.node.atom < raw.atomCount := by
  obtain ⟨spec, lookup⟩ := observed.2
  exact listGet?_eq_some_implies_lt raw.atoms cursor.node.atom spec lookup

/-- Unequal ACTUAL atomic ranks entail unequal elements, independent of deeper branch constitution. -/
theorem observed_elements_ne (raw : RawMolecule) (left right : Nat) (leftSpec rightSpec : AtomSpec)
    (leftLookup : raw.atomAt? left = some leftSpec) (rightLookup : raw.atomAt? right = some rightSpec)
    (different : raw.atomZAt left ≠ raw.atomZAt right) : leftSpec.element ≠ rightSpec.element := by
  intro same
  apply different
  rw [atomZAt_eq_of_atomAt? raw left leftSpec leftLookup,
    atomZAt_eq_of_atomAt? raw right rightSpec rightLookup, same]

theorem actual_same_constitution_false (raw : RawMolecule) (left right : Nat)
    (leftSpec rightSpec : AtomSpec) (leftLookup : raw.atomAt? left = some leftSpec)
    (rightLookup : raw.atomAt? right = some rightSpec)
    (different : raw.atomZAt left ≠ raw.atomZAt right) : raw.sameConstitutionAtom left right = false := by
  have elements := observed_elements_ne raw left right leftSpec rightSpec leftLookup rightLookup different
  simp [sameConstitutionAtom, leftLookup, rightLookup, elements]

/-- Real element disagreement closes the actual seeded-search guard before any graph search. -/
theorem actual_automorphism_false (raw : RawMolecule) (center left right : Nat)
    (leftSpec rightSpec : AtomSpec) (leftLookup : raw.atomAt? left = some leftSpec)
    (rightLookup : raw.atomAt? right = some rightSpec)
    (different : raw.atomZAt left ≠ raw.atomZAt right) :
    raw.hasConstitutionAutomorphismSwapping center left right = false := by
  have indices : left ≠ right := by
    intro same
    exact different (congrArg raw.atomZAt same)
  have atoms := actual_same_constitution_false raw left right leftSpec rightSpec leftLookup rightLookup different
  simp [hasConstitutionAutomorphismSwapping, indices, atoms]

/-- The ACTUAL cyclic migration-conflict gate is false on distinct observed atomic numbers. -/
theorem actual_occurrence_gate_false (raw : RawMolecule) (fuel : Nat)
    (left right : CanonicalRerootCursor) (compiled : Ordering)
    (leftObserved : ObservedReal raw left) (rightObserved : ObservedReal raw right)
    (different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom) :
    occurrenceRootsProvedAutomorphic raw fuel left right compiled = false := by
  obtain ⟨leftSpec, leftLookup⟩ := leftObserved.2
  obtain ⟨rightSpec, rightLookup⟩ := rightObserved.2
  have noAutomorphism : ∀ center,
      raw.hasConstitutionAutomorphismSwapping center left.node.atom right.node.atom = false :=
    fun center => actual_automorphism_false raw center left.node.atom right.node.atom
      leftSpec rightSpec leftLookup rightLookup different
  cases leftReference : left.previous? with
  | none => simp [occurrenceRootsProvedAutomorphic, leftReference]
  | some leftRoot =>
      cases rightReference : right.previous? with
      | none => simp [occurrenceRootsProvedAutomorphic, leftReference, rightReference]
      | some rightRoot =>
          simp [occurrenceRootsProvedAutomorphic, leftReference, rightReference, noAutomorphism]

theorem actual_fast_constitutional (raw : RawMolecule) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftObserved : ObservedReal raw left)
    (rightObserved : ObservedReal raw right)
    (different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom) :
    certifiedConstitutionalStage? raw fuel left right =
      some (compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom)) := by
  have compiled := compareCursorBranchAt_eq_of_rule1a raw left right
    leftObserved.1 rightObserved.1 different fuel CanonicalRuleStage.rule2
  have guard := actual_occurrence_gate_false raw fuel left right
    (compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom)) leftObserved rightObserved different
  simp [certifiedConstitutionalStage?, compiled, guard]

theorem actual_authoritative_constitutional (raw : RawMolecule) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftObserved : ObservedReal raw left)
    (rightObserved : ObservedReal raw right)
    (different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom) :
    certifiedConstitutionalStageAuthoritative? raw fuel left right =
      some (compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom)) := by
  have compiled := compareCursorBranchAtAuthoritative?_eq_of_rule1a raw left right
    leftObserved.1 rightObserved.1 different fuel CanonicalRuleStage.rule2
  have guard := actual_occurrence_gate_false raw fuel left right
    (compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom)) leftObserved rightObserved different
  simp [certifiedConstitutionalStageAuthoritative?, compiled, guard]

theorem actual_fast_comparison (raw : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftObserved : ObservedReal raw left)
    (rightObserved : ObservedReal raw right)
    (different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom) :
    compareOccurrenceBranches? raw state fuel left right =
      some { ordering := compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom),
             pseudo := false, rule4cCarrier? := none } := by
  have certified := actual_fast_constitutional raw fuel left right leftObserved rightObserved different
  cases decision : compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom) with
  | lt => rw [decision] at certified; simp [compareOccurrenceBranches?, certified]
  | gt => rw [decision] at certified; simp [compareOccurrenceBranches?, certified]
  | eq => exact False.elim (different (Nat.compare_eq_eq.mp decision))

theorem actual_authoritative_comparison (raw : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftObserved : ObservedReal raw left)
    (rightObserved : ObservedReal raw right)
    (different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom) :
    compareOccurrenceBranchesAuthoritative? raw state fuel left right =
      some { ordering := compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom),
             pseudo := false, rule4cCarrier? := none } := by
  have certified := actual_authoritative_constitutional raw fuel left right leftObserved rightObserved different
  cases decision : compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom) with
  | lt => rw [decision] at certified; simp [compareOccurrenceBranchesAuthoritative?, certified]
  | gt => rw [decision] at certified; simp [compareOccurrenceBranchesAuthoritative?, certified]
  | eq => exact False.elim (different (Nat.compare_eq_eq.mp decision))

theorem actual_complete_comparison (raw : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftObserved : ObservedReal raw left)
    (rightObserved : ObservedReal raw right)
    (different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom) :
    compareOccurrenceBranchesComplete? raw state fuel left right =
      some { ordering := compare (raw.atomZAt left.node.atom) (raw.atomZAt right.node.atom),
             pseudo := false, rule4cCarrier? := none } := by
  simp only [compareOccurrenceBranchesComplete?,
    actual_fast_comparison raw state fuel left right leftObserved rightObserved different]

/-- Actual source-spec restatement; neither atomZAt's out-of-bound fallback nor a desired key is used. -/
theorem actual_complete_comparison_observed (raw : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftSpec rightSpec : AtomSpec)
    (leftReal : left.node.provenance = CanonicalNodeProvenance.realAtom)
    (rightReal : right.node.provenance = CanonicalNodeProvenance.realAtom)
    (leftLookup : raw.atomAt? left.node.atom = some leftSpec)
    (rightLookup : raw.atomAt? right.node.atom = some rightSpec)
    (different : leftSpec.element.atomicNumber ≠ rightSpec.element.atomicNumber) :
    compareOccurrenceBranchesComplete? raw state fuel left right =
      some { ordering := compare leftSpec.element.atomicNumber rightSpec.element.atomicNumber,
             pseudo := false, rule4cCarrier? := none } := by
  have rankDifference : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom := by
    simpa only [atomZAt_eq_of_atomAt? raw left.node.atom leftSpec leftLookup,
      atomZAt_eq_of_atomAt? raw right.node.atom rightSpec rightLookup] using different
  rw [actual_complete_comparison raw state fuel left right
    ⟨leftReal, leftSpec, leftLookup⟩ ⟨rightReal, rightSpec, rightLookup⟩ rankDifference,
    atomZAt_eq_of_atomAt? raw left.node.atom leftSpec leftLookup,
    atomZAt_eq_of_atomAt? raw right.node.atom rightSpec rightLookup]

/-- ACTUAL insertion closure on observed real distinct ranks. Input sortedness belongs only
to this insertion lemma; the whole-sort theorem derives its output order internally. -/
theorem actual_insert_observed_rank (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (candidate : CanonicalRerootCursor) :
    ∀ existing : List CanonicalRerootCursor,
      (candidate :: existing).Nodup →
      (∀ c ∈ candidate :: existing, ObservedReal mol c) →
      (∀ a ∈ candidate :: existing, ∀ b ∈ candidate :: existing,
        mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b) →
      existing.Pairwise (AtomicDesc mol) →
      ∃ result,
        insertOccurrenceTrackedAuthoritative? mol state fuel candidate existing = some result ∧
        result.1.Perm (candidate :: existing) ∧
        result.1.Pairwise (AtomicDesc mol) ∧
        result.2 = 0 := by
  intro existing
  induction existing with
  | nil =>
      intro _ _ _ _
      exact ⟨([candidate], 0), rfl, List.Perm.refl _, by simp, rfl⟩
  | cons head tail inductionHypothesis =>
      intro hNodup hRestr hInj hSorted
      have hNodupParts := List.nodup_cons.mp hNodup
      have hCandidateNotHead : candidate ∉ head :: tail := hNodupParts.1
      have hTailNodup : tail.Nodup := (List.nodup_cons.mp hNodupParts.2).2
      have hCandidateNotTail : candidate ∉ tail :=
        fun member => hCandidateNotHead (List.mem_cons_of_mem head member)
      have hSortedHead : ∀ x ∈ tail, AtomicDesc mol head x := (List.pairwise_cons.mp hSorted).1
      have hSortedTail : tail.Pairwise (AtomicDesc mol) := (List.pairwise_cons.mp hSorted).2
      have hSubNodup : (candidate :: tail).Nodup :=
        List.nodup_cons.mpr ⟨hCandidateNotTail, hTailNodup⟩
      have hSubRestr : ∀ c ∈ candidate :: tail, ObservedReal mol c := by
        intro c hc
        exact hRestr c (by
          rcases List.mem_cons.mp hc with same | other
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr other))))
      have hSubInj : ∀ a ∈ candidate :: tail, ∀ b ∈ candidate :: tail,
          mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b := by
        intro a ha b hb equal
        exact hInj a (by
          rcases List.mem_cons.mp ha with same | other
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr other))))
          b (by
          rcases List.mem_cons.mp hb with same | other
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr other)))) equal
      obtain ⟨⟨insertedList, insertedCount⟩, hInsertedComputed, hInsertedPerm, hInsertedSorted,
        hInsertedZero⟩ :=
        inductionHypothesis hSubNodup hSubRestr hSubInj hSortedTail
      have hCandidateReal := hRestr candidate (by simp)
      have hHeadReal := hRestr head (by simp)
      have hDistinct : mol.atomZAt candidate.node.atom ≠ mol.atomZAt head.node.atom := by
        intro equal
        exact hCandidateNotHead (by
          have same : candidate = head := hInj candidate (by simp) head (by simp) equal
          rw [same]
          exact List.mem_cons_self)
      have hDecision := actual_complete_comparison mol state fuel candidate head
        hCandidateReal hHeadReal hDistinct
      cases hComp : compare (mol.atomZAt candidate.node.atom) (mol.atomZAt head.node.atom) with
      | lt =>
          have hDecision' : compareOccurrenceBranchesComplete? mol state fuel candidate head =
              some { ordering := Ordering.lt, pseudo := false } := by
            simpa [hComp] using hDecision
          refine ⟨(head :: insertedList, 0 + insertedCount), ?_, ?_, ?_, ?_⟩
          · simp [insertOccurrenceTrackedAuthoritative?, hDecision', hInsertedComputed]
          · exact (List.Perm.cons head hInsertedPerm).trans (List.Perm.swap candidate head tail)
          · refine List.pairwise_cons.mpr ⟨?_, hInsertedSorted⟩
            intro other hOther
            have hOtherMem := hInsertedPerm.mem_iff.mp hOther
            rcases List.mem_cons.mp hOtherMem with same | inTail
            · rw [same]; exact Nat.compare_eq_lt.mp hComp
            · exact hSortedHead other inTail
          · change 0 + insertedCount = 0
            exact (Nat.zero_add insertedCount).trans hInsertedZero
      | gt =>
          have hDecision' : compareOccurrenceBranchesComplete? mol state fuel candidate head =
              some { ordering := Ordering.gt, pseudo := false } := by
            simpa [hComp] using hDecision
          refine ⟨(candidate :: head :: tail, 0), ?_, List.Perm.refl _, ?_, rfl⟩
          · simp [insertOccurrenceTrackedAuthoritative?, hDecision']
          · refine List.pairwise_cons.mpr ⟨?_, hSorted⟩
            intro other hOther
            rcases List.mem_cons.mp hOther with same | inTail
            · rw [same]; exact Nat.compare_eq_gt.mp hComp
            · exact Nat.lt_trans (hSortedHead other inTail) (Nat.compare_eq_gt.mp hComp)
      | eq => exact absurd (Nat.compare_eq_eq.mp hComp) hDistinct

/-- The ACTUAL runtime tracked sorter succeeds on independent observed real, distinct-ranked
cursors, with no leaf/cycle-free premise. This does NOT construct the auxiliary environment. -/
theorem actual_sort_observed_rank (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) :
    ∀ cursors : List CanonicalRerootCursor,
      cursors.Nodup →
      (∀ c ∈ cursors, ObservedReal mol c) →
      (∀ a ∈ cursors, ∀ b ∈ cursors,
        mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b) →
      ∃ result,
        sortOccurrencesTrackedAuthoritative? mol state fuel cursors = some result ∧
        result.1.Perm cursors ∧
        result.1.Pairwise (AtomicDesc mol) ∧
        result.2 = 0 := by
  intro cursors
  induction cursors with
  | nil =>
      intro _ _ _
      exact ⟨([], 0), rfl, List.Perm.refl _, by simp, rfl⟩
  | cons cursor cursors inductionHypothesis =>
      intro hNodup hRestr hInj
      have hNodupParts := List.nodup_cons.mp hNodup
      have hCursorNotCursors : cursor ∉ cursors := hNodupParts.1
      have hCursorsNodup : cursors.Nodup := hNodupParts.2
      have hSubRestr : ∀ c ∈ cursors, ObservedReal mol c :=
        fun c member => hRestr c (List.mem_cons_of_mem cursor member)
      have hSubInj : ∀ a ∈ cursors, ∀ b ∈ cursors,
          mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b :=
        fun a ha b hb equal => hInj a (List.mem_cons_of_mem cursor ha)
          b (List.mem_cons_of_mem cursor hb) equal
      obtain ⟨⟨sortedList, sortedCount⟩, hSortedListComputed, hSortedListPerm, hSortedListSorted,
        hSortedListZero⟩ :=
        inductionHypothesis hCursorsNodup hSubRestr hSubInj
      have hCursorNotSorted : cursor ∉ sortedList :=
        fun member => hCursorNotCursors (hSortedListPerm.mem_iff.mp member)
      have hSortedListNodup : sortedList.Nodup := hSortedListPerm.nodup_iff.mpr hCursorsNodup
      have hInsertNodup : (cursor :: sortedList).Nodup :=
        List.nodup_cons.mpr ⟨hCursorNotSorted, hSortedListNodup⟩
      have hInsertRestr : ∀ c ∈ cursor :: sortedList, ObservedReal mol c := by
        intro c hc
        rcases List.mem_cons.mp hc with same | inSorted
        · exact hRestr c (List.mem_cons.mpr (Or.inl same))
        · exact hRestr c (List.mem_cons.mpr (Or.inr (hSortedListPerm.mem_iff.mp inSorted)))
      have hInsertInj : ∀ a ∈ cursor :: sortedList, ∀ b ∈ cursor :: sortedList,
          mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b := by
        intro a ha b hb equal
        exact hInj a (by
          rcases List.mem_cons.mp ha with same | inSorted
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (hSortedListPerm.mem_iff.mp inSorted)))
          b (by
          rcases List.mem_cons.mp hb with same | inSorted
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (hSortedListPerm.mem_iff.mp inSorted))) equal
      obtain ⟨⟨insertedList, insertedCount⟩, hInsertComputed, hInsertPerm, hInsertSorted,
        hInsertZero⟩ :=
        actual_insert_observed_rank mol state fuel cursor sortedList
          hInsertNodup hInsertRestr hInsertInj hSortedListSorted
      refine ⟨(insertedList, sortedCount + insertedCount), ?_, ?_, ?_, ?_⟩
      · simp [sortOccurrencesTrackedAuthoritative?, hSortedListComputed, hInsertComputed]
      · exact hInsertPerm.trans (List.Perm.cons cursor hSortedListPerm)
      · exact hInsertSorted
      · have sortedZero : sortedCount = 0 := hSortedListZero
        have insertedZero : insertedCount = 0 := hInsertZero
        change sortedCount + insertedCount = 0
        rw [sortedZero, insertedZero]

/-- Independent actual source observations and distinct actual first Z values derive the whole
production sorter outcome. The input need not be terminal, acyclic or Rule3-resolved. -/
theorem actual_sort_distinct_observed (raw : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (cursors : List CanonicalRerootCursor) (observed : ∀ cursor ∈ cursors, ObservedReal raw cursor)
    (distinct : (cursors.map (fun cursor => raw.atomZAt cursor.node.atom)).Nodup) :
    ∃ result, sortOccurrencesTrackedAuthoritative? raw state fuel cursors = some result ∧
      result.1.Perm cursors ∧ result.1.Pairwise (AtomicDesc raw) ∧ result.2 = 0 :=
  actual_sort_observed_rank raw state fuel cursors
    (List.Nodup.of_map (fun cursor => raw.atomZAt cursor.node.atom) distinct) observed
    (fun _ member _ retained equal => List.inj_on_of_nodup_map distinct member retained equal)

namespace TwoCyclicBranches



def raw : RawMolecule :=
  { atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .C, AtomSpec.aliphatic .C,
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .Si, AtomSpec.aliphatic .C,
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Br]
    bonds := [⟨0, 1, .single⟩, ⟨0, 4, .single⟩, ⟨0, 7, .single⟩, ⟨0, 8, .single⟩,
      ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 1, .single⟩,
      ⟨4, 5, .single⟩, ⟨5, 6, .single⟩, ⟨6, 4, .single⟩]
    neighborOrder := [[1, 4, 7, 8], [0, 2, 3], [1, 3], [2, 1], [0, 5, 6],
      [4, 6], [5, 4], [0], [0]] }

def root (atom : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

def roots : List CanonicalRerootCursor := [root 1, root 4, root 7, root 8]

theorem actual_admissible : raw.StereochemicalAdmissible := by
  apply (stereochemicalAdmissible?_eq_true_iff raw).mp
  decide +kernel

/-- The roots are REALLY generated by this source, not detached guesses of the desired order. -/
theorem actual_generated_roots : occurrenceLigandCursors raw (canonicalCenterRoot 0) = roots := by
  decide +kernel

theorem actual_four_frame : occurrenceLigandFrame? raw (canonicalCenterRoot 0) = some roots := by
  decide +kernel

theorem actual_both_cyclic : raw.atomLiesInCycle 5 1 = true ∧ raw.atomLiesInCycle 5 4 = true := by
  decide +kernel

theorem actual_nonleaf : (raw.incidentAtoms 1).length = 3 ∧ (raw.incidentAtoms 4).length = 3 := by
  decide +kernel

theorem actual_observed_roots : ∀ cursor ∈ roots, ObservedReal raw cursor := by
  intro cursor member
  change cursor ∈ [root 1, root 4, root 7, root 8] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨rfl, AtomSpec.aliphatic .C, rfl⟩
  · exact ⟨rfl, AtomSpec.aliphatic .Si, rfl⟩
  · exact ⟨rfl, AtomSpec.aliphatic .F, rfl⟩
  · exact ⟨rfl, AtomSpec.aliphatic .Br, rfl⟩

theorem actual_distinct_ranks : (roots.map (fun cursor => raw.atomZAt cursor.node.atom)).Nodup := by
  decide +kernel

/-- Both CYCLIC roots still have a false migration guard; no acyclicity assumption is supplied. -/
theorem actual_cyclic_gate_false (fuel : Nat) (compiled : Ordering) :
    occurrenceRootsProvedAutomorphic raw fuel (root 1) (root 4) compiled = false :=
  actual_occurrence_gate_false raw fuel (root 1) (root 4) compiled
    (actual_observed_roots _ (by simp [roots])) (actual_observed_roots _ (by simp [roots]))
    (by decide +kernel)

/-- Genuine actual both-cyclic/nonleaf comparison at all budgets and all comparison states. -/
theorem actual_cyclic_complete_comparison (state : OccurrenceAuxState) (fuel : Nat) :
    compareOccurrenceBranchesComplete? raw state fuel (root 1) (root 4) =
      some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  have computed := actual_complete_comparison raw state fuel (root 1) (root 4)
    (actual_observed_roots _ (by simp [roots])) (actual_observed_roots _ (by simp [roots]))
    (by decide +kernel)
  exact computed

theorem actual_cyclic_authoritative_comparison (state : OccurrenceAuxState) (fuel : Nat) :
    compareOccurrenceBranchesAuthoritative? raw state fuel (root 1) (root 4) =
      some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  have computed := actual_authoritative_comparison raw state fuel (root 1) (root 4)
    (actual_observed_roots _ (by simp [roots])) (actual_observed_roots _ (by simp [roots]))
    (by decide +kernel)
  exact computed

/-- ACTUAL source-generated four-root sorter success on cyclic/nonleaf branches. Its result is
derived; no expected sorted list or successful comparison is a premise. -/
theorem actual_generated_sort (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ result, sortOccurrencesTrackedAuthoritative? raw state fuel
        (occurrenceLigandCursors raw (canonicalCenterRoot 0)) = some result ∧
      result.1.Perm (occurrenceLigandCursors raw (canonicalCenterRoot 0)) ∧
      result.1.Pairwise (AtomicDesc raw) ∧ result.2 = 0 := by
  rw [actual_generated_roots]
  exact actual_sort_distinct_observed raw state fuel roots actual_observed_roots actual_distinct_ranks

/-- This ACTUAL generated frame cannot instantiate the older physical leaf domain. -/
theorem leaf_domain_impossible : ¬ NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.LeafNeighborDomain raw 0 := by
  intro domain
  have member : 1 ∈ NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.recordNeighbors raw 0 := by decide +kernel
  have degree := domain.leaf member
  rw [actual_nonleaf.1] at degree
  omega

end TwoCyclicBranches

end TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery
