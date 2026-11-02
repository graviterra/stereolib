import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupport
import TetraStereo.UniversalProof.NativeRawRecordBounds

set_option autoImplicit false

namespace TetraStereo.UniversalProof.TerminalStarCycleGuard

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery

/-! Proposed general production cycle exclusion. Independent raw records only;
no global forest, desired cycle/traversal result, cursor output or auxiliary state premise.
The methyl carbon of the second-sphere family has this shape once its physical rows are derived.
Kernel validation, family instantiation, HUMAN and EXTERNAL remain OPEN. -/

private theorem eraseDups_loop_not_mem (relation : Nat → Nat → Bool) (target : Nat)
    (values accumulator : List Nat) (valuesAbsent : target ∉ values)
    (accumulatorAbsent : target ∉ accumulator) :
    target ∉ List.eraseDupsBy.loop relation values accumulator := by
  induction values generalizing accumulator with
  | nil => simpa only [List.eraseDupsBy.loop, List.mem_reverse] using accumulatorAbsent
  | cons head tail ih =>
      have headDifferent : target ≠ head := by
        intro equal
        exact valuesAbsent (List.mem_cons.mpr (Or.inl equal))
      have tailAbsent : target ∉ tail := by
        intro member
        exact valuesAbsent (List.mem_cons_of_mem head member)
      simp only [List.eraseDupsBy.loop]
      cases observed : accumulator.any (relation head) with
      | false =>
          exact ih (head :: accumulator) tailAbsent
            (by simpa only [List.mem_cons, not_or] using And.intro headDifferent accumulatorAbsent)
      | true => exact ih accumulator tailAbsent accumulatorAbsent

theorem eraseDups_not_mem (target : Nat) (values : List Nat) (absent : target ∉ values) :
    target ∉ values.eraseDups := by
  unfold List.eraseDups List.eraseDupsBy
  exact eraseDups_loop_not_mem (· == ·) target values [] absent (by simp)

theorem eraseDups_eq_self_of_nodup (values : List Nat) (distinct : values.Nodup) :
    values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have separate := List.nodup_cons.mp distinct
      have filtered : tail.filter (fun value => !(value == head)) = tail := by
        apply List.filter_eq_self.mpr
        intro value member
        have different : value ≠ head := by
          intro equal
          exact separate.1 (equal ▸ member)
        simpa using different
      rw [List.eraseDups_cons, filtered, ih separate.2]

/-- Exactly the edge filter used by production reachableAvoiding. -/
def blockedNeighbors (raw : RawMolecule) (blocked atom : Nat) : List Nat :=
  raw.bonds.filterMap fun bond =>
    if bond.source == atom && bond.target != blocked then some bond.target
    else if bond.target == atom && bond.source != blocked then some bond.source else none

theorem blockedNeighbors_member (raw : RawMolecule) (blocked atom next : Nat)
    (member : next ∈ blockedNeighbors raw blocked atom) :
    next ∈ recordNeighbors raw atom ∧ next ≠ blocked := by
  obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
  split at observed
  · rename_i condition
    have source : bond.source = atom := beq_iff_eq.mp (Bool.and_eq_true_iff.mp condition).1
    have unblocked : bond.target ≠ blocked := by
      simpa using (Bool.and_eq_true_iff.mp condition).2
    have target : bond.target = next := Option.some.inj observed
    refine ⟨List.mem_filterMap.mpr ⟨bond, retained, ?_⟩, ?_⟩
    · simp only [recordNeighbor?, source, beq_self_eq_true, ↓reduceIte]
      exact congrArg some target
    · exact target ▸ unblocked
  · split at observed
    · rename_i condition
      have target : bond.target = atom := beq_iff_eq.mp (Bool.and_eq_true_iff.mp condition).1
      have unblocked : bond.source ≠ blocked := by
        simpa using (Bool.and_eq_true_iff.mp condition).2
      have source : bond.source = next := Option.some.inj observed
      refine ⟨List.mem_filterMap.mpr ⟨bond, retained, ?_⟩, source ▸ unblocked⟩
      by_cases same : next = atom
      · simp [recordNeighbor?, source, target, same]
      · simp [recordNeighbor?, source, target, same]
    · cases observed

theorem blockedNeighbors_excludes_terminal (raw : RawMolecule) (well : raw.WellFormed)
    (blocked leaf atom : Nat) (leafRow : recordNeighbors raw leaf = [blocked])
    (atomDifferent : atom ≠ blocked) : leaf ∉ blockedNeighbors raw blocked atom := by
  intro member
  have reverse := record_neighbors_symmetric raw well
    (blockedNeighbors_member raw blocked atom leaf member).1
  rw [leafRow] at reverse
  exact atomDifferent (List.mem_singleton.mp reverse)

/-- A terminal attached only to the blocked atom cannot enter any production frontier. -/
theorem reachableAvoiding_excludes_terminal (raw : RawMolecule) (well : raw.WellFormed)
    (blocked leaf fuel : Nat) (leafRow : recordNeighbors raw leaf = [blocked])
    (frontier seen : List Nat) (frontierBlocked : blocked ∉ frontier)
    (seenLeaf : leaf ∉ seen) :
    leaf ∉ raw.reachableAvoiding fuel blocked frontier seen := by
  induction fuel generalizing frontier seen with
  | zero => exact seenLeaf
  | succ fuel ih =>
      cases frontier with
      | nil => exact seenLeaf
      | cons head tail =>
          let next := ((head :: tail).flatMap (blockedNeighbors raw blocked)).filter
            (fun atom => !(seen.contains atom))
          let fresh := next.eraseDups
          have freshLeaf : leaf ∉ fresh := by
            apply eraseDups_not_mem
            intro member
            have selected := (List.mem_filter.mp member).1
            obtain ⟨atom, inFrontier, edge⟩ := List.mem_flatMap.mp selected
            exact blockedNeighbors_excludes_terminal raw well blocked leaf atom leafRow
              (by intro equal; exact frontierBlocked (equal ▸ inFrontier)) edge
          have freshBlocked : blocked ∉ fresh := by
            apply eraseDups_not_mem
            intro member
            have selected := (List.mem_filter.mp member).1
            obtain ⟨atom, _, edge⟩ := List.mem_flatMap.mp selected
            exact (blockedNeighbors_member raw blocked atom blocked edge).2 rfl
          change leaf ∉ raw.reachableAvoiding fuel blocked fresh (seen ++ fresh)
          exact ih fresh (seen ++ fresh) freshBlocked
            (by simpa only [List.mem_append, not_or] using And.intro seenLeaf freshLeaf)

theorem reachableAvoiding_singleton_contains_terminal_false (raw : RawMolecule)
    (well : raw.WellFormed) (blocked leaf start fuel : Nat)
    (leafRow : recordNeighbors raw leaf = [blocked]) (startLeaf : start ≠ leaf)
    (startBlocked : start ≠ blocked) :
    (raw.reachableAvoiding fuel blocked [start] [start]).contains leaf = false := by
  have leafAbsent : leaf ∉ [start] := by simpa only [List.mem_singleton] using Ne.symm startLeaf
  have blockedAbsent : blocked ∉ [start] := by simpa only [List.mem_singleton] using Ne.symm startBlocked
  have excluded := reachableAvoiding_excludes_terminal raw well blocked leaf fuel leafRow
    [start] [start] blockedAbsent leafAbsent
  simp only [List.contains_eq_mem, excluded, decide_false]

structure TerminalStar (raw : RawMolecule) (center parent h1 h2 h3 : Nat) : Prop where
  well : raw.WellFormed
  centerRow : recordNeighbors raw center = [parent, h1, h2, h3]
  distinct : [parent, h1, h2, h3].Nodup
  h1Row : recordNeighbors raw h1 = [center]
  h2Row : recordNeighbors raw h2 = [center]
  h3Row : recordNeighbors raw h3 = [center]

theorem incidentAtoms_eq_recordNeighbors_eraseDups (raw : RawMolecule) (center : Nat) :
    raw.incidentAtoms center = (recordNeighbors raw center).eraseDups := rfl

/-- The fourth neighbor may lead to an arbitrary graph; the other three are actual leaves. -/
theorem terminalStar_atomLiesInCycle_false (raw : RawMolecule)
    (center parent h1 h2 h3 fuel : Nat) (star : TerminalStar raw center parent h1 h2 h3) :
    raw.atomLiesInCycle fuel center = false := by
  have distinctions : (parent ≠ h1 ∧ parent ≠ h2 ∧ parent ≠ h3) ∧
      (h1 ≠ h2 ∧ h1 ≠ h3) ∧ h2 ≠ h3 := by
    simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      List.nodup_nil, not_false_eq_true, and_true] using star.distinct
  have parentDifferent : parent ≠ center :=
    (recordNeighbor_bounds star.well (by rw [star.centerRow]; simp)).2
  have h1Different : h1 ≠ center :=
    (recordNeighbor_bounds star.well (by rw [star.centerRow]; simp)).2
  have h2Different : h2 ≠ center :=
    (recordNeighbor_bounds star.well (by rw [star.centerRow]; simp)).2
  have ph1 := reachableAvoiding_singleton_contains_terminal_false raw star.well
    center h1 parent fuel star.h1Row distinctions.1.1 parentDifferent
  have ph2 := reachableAvoiding_singleton_contains_terminal_false raw star.well
    center h2 parent fuel star.h2Row distinctions.1.2.1 parentDifferent
  have ph3 := reachableAvoiding_singleton_contains_terminal_false raw star.well
    center h3 parent fuel star.h3Row distinctions.1.2.2 parentDifferent
  have h1h2 := reachableAvoiding_singleton_contains_terminal_false raw star.well
    center h2 h1 fuel star.h2Row distinctions.2.1.1 h1Different
  have h1h3 := reachableAvoiding_singleton_contains_terminal_false raw star.well
    center h3 h1 fuel star.h3Row distinctions.2.1.2 h1Different
  have h2h3 := reachableAvoiding_singleton_contains_terminal_false raw star.well
    center h3 h2 fuel star.h3Row distinctions.2.2 h2Different
  have incident : raw.incidentAtoms center = [parent, h1, h2, h3] := by
    rw [incidentAtoms_eq_recordNeighbors_eraseDups, star.centerRow]
    exact eraseDups_eq_self_of_nodup _ star.distinct
  simp [atomLiesInCycle, incident, ringPairCount, List.range_succ]
  refine ⟨?_, ?_, ?_⟩
  · intro index _ selected
    rcases selected with rfl | rfl | rfl
    · simpa using ph1
    · simpa using ph2
    · simpa using ph3
  · intro index _ selected
    rcases selected with rfl | rfl
    · simpa using h1h2
    · simpa using h1h3
  · simpa using h2h3

theorem automorphismGuard_false_of_right_terminalStar (raw : RawMolecule)
    (center parent h1 h2 h3 fuel : Nat) (star : TerminalStar raw center parent h1 h2 h3)
    (left right : CanonicalRerootCursor) (rightAtom : right.node.atom = center)
    (constitutional : Ordering) :
    occurrenceRootsProvedAutomorphic raw fuel left right constitutional = false := by
  have excluded := terminalStar_atomLiesInCycle_false raw center parent h1 h2 h3 fuel star
  simp [occurrenceRootsProvedAutomorphic, rightAtom, excluded]

end TetraStereo.UniversalProof.TerminalStarCycleGuard
