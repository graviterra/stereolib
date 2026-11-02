import TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery
import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FramedAtomicDispatch

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery

/-! Dispatch preservation on independently observed, distinct first-atomic-number frames.
A successful profile supplies its complete generated inventory; callers do not supply cursor
validation, comparator success, a sorted result, or a desired whole fact equation. -/

private theorem generated_root_tail {mol : RawMolecule} {root : Nat}
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node.history.getLast? = some root := by
  induction generated with
  | root => rfl
  | @child parent child parentGenerated member ih =>
      rw [mol.canonicalChildren_history parent child member]
      cases stored : parent.history with
      | nil =>
          have head := parentGenerated.history_head
          simp [stored] at head
      | cons atom tail => simpa [stored] using ih

/-- Successful collection exhausts the frontier and is closed under actual child generation. -/
theorem collect_closed (mol : RawMolecule) (fuel : Nat) :
    ∀ cap frontier result,
    CanonicalTreeProfile.collect fuel cap mol frontier = some result →
      (∀ node ∈ frontier, node ∈ result) ∧
      (∀ node ∈ result, ∀ child ∈ mol.canonicalChildren node, child ∈ result) := by
  induction fuel with
  | zero =>
      intro cap frontier result computed
      cases frontier with
      | nil => simp [CanonicalTreeProfile.collect] at computed; subst result; simp
      | cons head tail => simp [CanonicalTreeProfile.collect] at computed
  | succ fuel ih =>
      intro cap frontier result computed
      cases frontier with
      | nil => simp [CanonicalTreeProfile.collect] at computed; subst result; simp
      | cons head tail =>
          rw [CanonicalTreeProfile.collect] at computed <;> try simp only [List.cons_ne_nil, imp_self]
          by_cases capExceeded : cap < (head :: tail).length
          · rw [if_pos capExceeded] at computed
            cases computed
          · rw [if_neg capExceeded] at computed
            cases restEq : CanonicalTreeProfile.collect fuel
                (cap - (head :: tail).length) mol ((head :: tail).flatMap mol.canonicalChildren) with
            | none =>
                rw [restEq] at computed
                cases computed
            | some rest =>
                have closed := ih _ _ _ restEq
                rw [restEq] at computed
                have resultEq : result = (head :: tail) ++ rest := (Option.some.inj computed).symm
                subst result
                refine ⟨fun node member => List.mem_append_left rest member, ?_⟩
                intro node member child childMember
                rcases List.mem_append.mp member with atFront | inRest
                · exact List.mem_append_right _ (closed.1 child
                    (List.mem_flatMap.mpr ⟨node, atFront, childMember⟩))
                · exact List.mem_append_right _ (closed.2 node inRest child childMember)

/-- All nodes generated from the actual original root belong to a successful shared profile,
and their real provenance is an observed profile guard. No global tree hypothesis is added. -/
theorem profile_generated {mol : RawMolecule} {root : Nat} {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) (profile : FrameRuntime.Profile)
    (available : FrameRuntime.profile? mol center = some profile) :
    ∀ node, CanonicalCenterTreeNode mol root node →
      node ∈ profile.generated ∧ node.provenance = CanonicalNodeProvenance.realAtom := by
  have rootTail := generated_root_tail centerGenerated
  unfold FrameRuntime.profile? CanonicalTreeProfile.profile? at available
  simp only [rootTail, Bind.bind, Option.bind] at available
  split at available
  · contradiction
  · change (do
      let generated ← CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol
        [canonicalCenterRoot root]
      if !generated.contains center then none else
      if !(generated.all fun node =>
          node.provenance == .realAtom && node.history.head? == some node.atom &&
          node.history.getLast? == some root && !node.history.isEmpty &&
          decide node.history.Nodup && node.history.all (fun atom => decide (atom < mol.atomCount)))
        then none else some ⟨center, ⟨center.history⟩, generated⟩) = some profile at available
    cases collected : CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol
        [canonicalCenterRoot root] with
    | none =>
        rw [collected] at available
        cases available
    | some inventory =>
        rw [collected] at available
        simp only [Bind.bind, Option.bind] at available
        split at available
        · contradiction
        · split at available
          · contradiction
          · rename_i checked
            have profileEq : profile = ⟨center, ⟨center.history⟩, inventory⟩ :=
              (Option.some.inj available).symm
            subst profile
            have closed := collect_closed mol (mol.atomCount + 1) _ _ _ collected
            have members : ∀ node, CanonicalCenterTreeNode mol root node → node ∈ inventory := by
              intro node generated
              induction generated with
              | root => exact closed.1 _ List.mem_cons_self
              | @child parent child generated member ih => exact closed.2 parent ih child member
            have checks : inventory.all (fun node =>
                node.provenance == .realAtom && node.history.head? == some node.atom &&
                node.history.getLast? == some root && !node.history.isEmpty &&
                decide node.history.Nodup && node.history.all (fun atom => decide (atom < mol.atomCount))) = true := by
              simpa [and_assoc] using checked
            intro node generated
            have member := members node generated
            have nodeChecks := (List.all_eq_true.mp checks) node member
            simp only [Bool.and_eq_true, beq_iff_eq] at nodeChecks
            exact ⟨member, nodeChecks.1.1.1.1.1⟩

/-- Genuine reroot cursors pass the actual profile membership and incoming-edge checks. -/
theorem generated_cursor_observed {mol : RawMolecule} {root : Nat} {center : CanonicalBranchNode}
    (centerGenerated : CanonicalCenterTreeNode mol root center) (profile : FrameRuntime.Profile)
    (available : FrameRuntime.profile? mol center = some profile)
    {cursor : CanonicalRerootCursor} (eligible : CanonicalCenterRerootCursor mol root cursor) :
    ∃ distance, FrameRuntime.cursor? mol profile (.actual cursor) = some distance := by
  have generated := profile_generated centerGenerated profile available
  cases eligible with
  | @descending parent node parentGenerated member =>
      have parentFacts := generated parent parentGenerated
      have nodeFacts := generated node (CanonicalCenterTreeNode.child parentGenerated member)
      have incoming := canonicalOriginalParent?_eq_some_of_child parentGenerated member
      exact ⟨profile.frame.realDistance node, by
        simp [FrameRuntime.cursor?, parentFacts.1, nodeFacts.1, nodeFacts.2,
          CanonicalRerootCursor.neighbors, incoming, CanonicalComparisonFrame.observeNode]⟩
  | @ascending node child nodeGenerated member =>
      have nodeFacts := generated node nodeGenerated
      have childFacts := generated child (CanonicalCenterTreeNode.child nodeGenerated member)
      exact ⟨profile.frame.realDistance node, by
        simp [FrameRuntime.cursor?, nodeFacts.1, childFacts.1, nodeFacts.2,
          CanonicalRerootCursor.neighbors, member, CanonicalComparisonFrame.observeNode]⟩

/-- Strict first-Z decisions in the framed backend, for any supplied state and fuel. -/
theorem strict_atomic_decision (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftObserved : ObservedReal mol left) (rightObserved : ObservedReal mol right)
    (leftValid : ∃ d, FrameRuntime.cursor? mol profile (.actual left) = some d)
    (rightValid : ∃ d, FrameRuntime.cursor? mol profile (.actual right) = some d)
    (different : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom) :
    FrameRuntime.decisionComplete? mol profile true state fuel left right =
      some { ordering := compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) } := by
  obtain ⟨ld, hl⟩ := leftValid
  obtain ⟨rd, hr⟩ := rightValid
  have atomic : FrameRuntime.label? mol profile true .rule1a (.actual left) (.actual right) =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
    simpa [FrameRuntime.label?, hl, hr, FrameRuntime.Cursor.original] using
      NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom
        mol left.node right.node leftObserved.1 rightObserved.1
  have strict : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) ≠ Ordering.eq :=
    fun equal => different (Nat.compare_eq_eq.mp equal)
  have rule (before : FrameRuntime.Cursor → FrameRuntime.Cursor → Option Ordering) (n : Nat) :
      FrameRuntime.compareRule? mol profile true before .rule1a n [(.actual left, .actual right)] =
        some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
    rw [FrameRuntime.compareRule?]
    simp [FrameRuntime.pairLabels?, atomic, strict]
  have branch : FrameRuntime.compareBranch? mol profile true fuel .rule2 (.actual left) (.actual right) =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
    cases fuel with
    | zero => rw [FrameRuntime.compareBranch?]; simp [FrameRuntime.throughLabels?, atomic, strict]
    | succ n => rw [FrameRuntime.compareBranch?]; simp [rule, strict]
  simp [FrameRuntime.decisionComplete?, branch, strict]

private theorem decision_eq_legacy (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (fuel : Nat) (left right : CanonicalRerootCursor)
    (leftObserved : ObservedReal mol left) (rightObserved : ObservedReal mol right)
    (leftValid : ∃ d, FrameRuntime.cursor? mol profile (.actual left) = some d)
    (rightValid : ∃ d, FrameRuntime.cursor? mol profile (.actual right) = some d)
    (different : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom) :
    FrameRuntime.decisionComplete? mol profile true state fuel left right =
      compareOccurrenceBranchesComplete? mol state fuel left right := by
  rw [strict_atomic_decision mol profile state fuel left right leftObserved rightObserved leftValid rightValid different,
    actual_complete_comparison mol state fuel left right leftObserved rightObserved different]

private theorem insert_eq_legacy (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (fuel : Nat) (candidate : CanonicalRerootCursor) :
    ∀ existing,
    (∀ c ∈ candidate :: existing, ObservedReal mol c) →
    (∀ c ∈ candidate :: existing, ∃ d, FrameRuntime.cursor? mol profile (.actual c) = some d) →
    ((candidate :: existing).map (fun c => mol.atomZAt c.node.atom)).Nodup →
    FramedCompleteRuntime.trackedInsertComplete? mol profile true state fuel candidate existing =
      insertOccurrenceTrackedAuthoritative? mol state fuel candidate existing := by
  intro existing
  induction existing with
  | nil =>
      intro observed valid distinct
      obtain ⟨d, computed⟩ := valid candidate List.mem_cons_self
      simp [FramedCompleteRuntime.trackedInsertComplete?, insertOccurrenceTrackedAuthoritative?, computed]
  | cons head tail ih =>
      intro observed valid distinct
      have subset : ∀ c ∈ candidate :: tail, c ∈ candidate :: head :: tail := by
        intro c member
        rcases List.mem_cons.mp member with same | retained
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem candidate (List.mem_cons_of_mem head retained)
      have smallerDistinct : ((candidate :: tail).map (fun c => mol.atomZAt c.node.atom)).Nodup := by
        refine List.nodup_cons.mpr ⟨?_, (List.nodup_cons.mp (List.nodup_cons.mp distinct).2).2⟩
        intro member
        exact (List.nodup_cons.mp distinct).1 (List.mem_cons_of_mem _ member)
      have smaller := ih
        (fun c member => observed c (subset c member))
        (fun c member => valid c (subset c member)) smallerDistinct
      have different : mol.atomZAt candidate.node.atom ≠ mol.atomZAt head.node.atom := by
        have fresh := (List.nodup_cons.mp distinct).1
        intro equal
        apply fresh
        simp [equal]
      have decision := decision_eq_legacy mol profile state fuel candidate head
        (observed candidate (by simp)) (observed head (by simp))
        (valid candidate (by simp)) (valid head (by simp)) different
      simp only [FramedCompleteRuntime.trackedInsertComplete?, insertOccurrenceTrackedAuthoritative?,
        decision, smaller]

/-- Equality of the actual tracked sorters on an independently distinct atomic frame. -/
theorem sort_eq_legacy (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (fuel : Nat) : ∀ cursors,
    (∀ c ∈ cursors, ObservedReal mol c) →
    (∀ c ∈ cursors, ∃ d, FrameRuntime.cursor? mol profile (.actual c) = some d) →
    (cursors.map (fun c => mol.atomZAt c.node.atom)).Nodup →
    FramedCompleteRuntime.trackedSortComplete? mol profile true state fuel cursors =
      sortOccurrencesTrackedAuthoritative? mol state fuel cursors := by
  intro cursors
  induction cursors with
  | nil => intro _ _ _; rfl
  | cons head tail ih =>
      intro observed valid distinct
      have tailObserved := fun c member => observed c (List.mem_cons_of_mem head member)
      have tailValid := fun c member => valid c (List.mem_cons_of_mem head member)
      have tailDistinct := (List.nodup_cons.mp distinct).2
      have tailEq := ih tailObserved tailValid tailDistinct
      obtain ⟨result, computed, permutation, _, _⟩ :=
        actual_sort_distinct_observed mol state fuel tail tailObserved tailDistinct
      have lifted := List.Perm.cons head permutation
      have insertEq := insert_eq_legacy mol profile state fuel head result.1
        (fun c member => observed c (lifted.mem_iff.mp member))
        (fun c member => valid c (lifted.mem_iff.mp member))
        ((lifted.map _).nodup_iff.mpr distinct)
      simp [FramedCompleteRuntime.trackedSortComplete?, sortOccurrencesTrackedAuthoritative?,
        tailEq, computed, insertEq]

/-- Exact adjacency decisions, including all protocol fields, on distinct atomic frames. -/
theorem adjacent_projection_eq_legacy (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (fuel : Nat) : ∀ cursors,
    (∀ c ∈ cursors, ObservedReal mol c) →
    (∀ c ∈ cursors, ∃ d, FrameRuntime.cursor? mol profile (.actual c) = some d) →
    (cursors.map (fun c => mol.atomZAt c.node.atom)).Nodup →
    (FramedCompleteRuntime.adjacentComplete? mol profile true state fuel cursors).map
        (fun pairs => pairs.map OccurrenceComparedPair.decision) =
      compareOccurrenceAdjacentPairsAuthoritative? mol state fuel cursors := by
  intro cursors
  induction cursors with
  | nil => intro _ _ _; rfl
  | cons left tail ih =>
      intro observed valid distinct
      cases tail with
      | nil => rfl
      | cons right rest =>
          have tailEq := ih
            (fun c member => observed c (List.mem_cons_of_mem left member))
            (fun c member => valid c (List.mem_cons_of_mem left member))
            ((List.nodup_cons.mp distinct).2)
          have different : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom := by
            have fresh := (List.nodup_cons.mp distinct).1
            intro equal
            apply fresh
            simp [equal]
          have decision := decision_eq_legacy mol profile state fuel left right
            (observed left (by simp)) (observed right (by simp))
            (valid left (by simp)) (valid right (by simp)) different
          simp only [FramedCompleteRuntime.adjacentComplete?, compareOccurrenceAdjacentPairsAuthoritative?, decision]
          rw [← tailEq]
          cases compareOccurrenceBranchesComplete? mol state fuel left right <;>
            cases FramedCompleteRuntime.adjacentComplete? mol profile true state fuel (right :: rest) <;>
            rfl




theorem authoritative_fact_eq_legacy (mol : RawMolecule) (root fuel : Nat)
    (state : OccurrenceAuxState) (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) (roots : List CanonicalRerootCursor)
    (physical : occurrenceLigandCursors mol node = roots)
    (frame : occurrenceLigandFrame? mol node = some roots)
    (observed : ∀ c ∈ roots, ObservedReal mol c)
    (distinct : (roots.map (fun c => mol.atomZAt c.node.atom)).Nodup) :
    occurrenceFactAuthoritative? mol fuel state node = legacyOccurrenceFactAuthoritative? mol fuel state node := by
  cases available : FrameRuntime.profile? mol node with
  | none => exact occurrenceFactAuthoritative?_eq_legacy_of_profile_none mol fuel state node available
  | some profile =>
      have valid : ∀ c ∈ roots, ∃ d, FrameRuntime.cursor? mol profile (.actual c) = some d := by
        intro c member
        exact generated_cursor_observed generated profile available
          (occurrenceLigandCursor_eligible generated (by rw [physical]; exact member))
      have sortEq := sort_eq_legacy mol profile state fuel roots observed valid distinct
      obtain ⟨result, sorted, permutation, _, _⟩ :=
        actual_sort_distinct_observed mol state fuel roots observed distinct
      have adjacentEq := adjacent_projection_eq_legacy mol profile state fuel result.1
        (fun c member => observed c (permutation.mem_iff.mp member))
        (fun c member => valid c (permutation.mem_iff.mp member))
        ((permutation.map _).nodup_iff.mpr distinct)
      simp only [occurrenceFactAuthoritative?, available]
      simp only [framedOccurrenceFactAuthoritative?, legacyOccurrenceFactAuthoritative?,
        available, Bind.bind, Option.bind, frame, FrameRuntime.trackedSort?, sortEq, sorted,
        FrameRuntime.adjacent?, adjacentEq]

end TetraStereo.UniversalProof.FramedAtomicDispatch
