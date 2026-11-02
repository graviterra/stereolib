import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRootComparison

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

-- Sorting uses the proved callbacks without reducing the physical hydrogen expansion.
attribute [local irreducible] expanded

def orderedRootCursors (n : Nat) : List CanonicalRerootCursor :=
  [nitrileRootCursor 1, nitrileCursor, aminoCursor, nitrileRootCursor (n + 7)]

-- Abstract cursors keep the finite sorting calculation independent of molecular reduction.
private theorem strict_four_fast_sort (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (items : List CanonicalRerootCursor) (a b c d : CanonicalRerootCursor)
    (permutation : items.Perm [a, b, c, d])
    (ab : compareOccurrenceBranches? mol state fuel a b = some { ordering := .gt })
    (ba : compareOccurrenceBranches? mol state fuel b a = some { ordering := .lt })
    (ac : compareOccurrenceBranches? mol state fuel a c = some { ordering := .gt })
    (ca : compareOccurrenceBranches? mol state fuel c a = some { ordering := .lt })
    (ad : compareOccurrenceBranches? mol state fuel a d = some { ordering := .gt })
    (da : compareOccurrenceBranches? mol state fuel d a = some { ordering := .lt })
    (bc : compareOccurrenceBranches? mol state fuel b c = some { ordering := .gt })
    (cb : compareOccurrenceBranches? mol state fuel c b = some { ordering := .lt })
    (bd : compareOccurrenceBranches? mol state fuel b d = some { ordering := .gt })
    (db : compareOccurrenceBranches? mol state fuel d b = some { ordering := .lt })
    (cd : compareOccurrenceBranches? mol state fuel c d = some { ordering := .gt })
    (dc : compareOccurrenceBranches? mol state fuel d c = some { ordering := .lt }) :
    sortOccurrencesTracked? mol state fuel items = some ([a, b, c, d], 0) := by
  have member := List.mem_permutations'.mpr permutation
  simp only [List.permutations', List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [sortOccurrencesTracked?, insertOccurrenceTracked]

private theorem strict_four_authoritative_sort (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (items : List CanonicalRerootCursor) (a b c d : CanonicalRerootCursor)
    (permutation : items.Perm [a, b, c, d])
    (ab : compareOccurrenceBranchesComplete? mol state fuel a b = some { ordering := .gt })
    (ba : compareOccurrenceBranchesComplete? mol state fuel b a = some { ordering := .lt })
    (ac : compareOccurrenceBranchesComplete? mol state fuel a c = some { ordering := .gt })
    (ca : compareOccurrenceBranchesComplete? mol state fuel c a = some { ordering := .lt })
    (ad : compareOccurrenceBranchesComplete? mol state fuel a d = some { ordering := .gt })
    (da : compareOccurrenceBranchesComplete? mol state fuel d a = some { ordering := .lt })
    (bc : compareOccurrenceBranchesComplete? mol state fuel b c = some { ordering := .gt })
    (cb : compareOccurrenceBranchesComplete? mol state fuel c b = some { ordering := .lt })
    (bd : compareOccurrenceBranchesComplete? mol state fuel b d = some { ordering := .gt })
    (db : compareOccurrenceBranchesComplete? mol state fuel d b = some { ordering := .lt })
    (cd : compareOccurrenceBranchesComplete? mol state fuel c d = some { ordering := .gt })
    (dc : compareOccurrenceBranchesComplete? mol state fuel d c = some { ordering := .lt }) :
    sortOccurrencesTrackedAuthoritative? mol state fuel items = some ([a, b, c, d], 0) := by
  have member := List.mem_permutations'.mpr permutation
  simp only [List.permutations', List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [sortOccurrencesTrackedAuthoritative?, insertOccurrenceTrackedAuthoritative?]

/-- Both actual tracked sorters return the independently derived priority order, with zero
pseudo history. Only the 24 permutations of a four-slot input are exhausted; n is arbitrary. -/
theorem actual_root_tracked_sort (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) :
    sortOccurrencesTracked? (expanded parity n) state (fuel + 2)
        (occurrenceLigandCursors (expanded parity n) (canonicalCenterRoot 0)) =
        some (orderedRootCursors n, 0) ∧
      sortOccurrencesTrackedAuthoritative? (expanded parity n) state (fuel + 2)
        (occurrenceLigandCursors (expanded parity n) (canonicalCenterRoot 0)) =
        some (orderedRootCursors n, 0) := by
  have permutation := (actual_center_cursors_permutation parity n).trans
    (List.perm_append_comm (l₁ := [nitrileRootCursor (n + 7)])
      (l₂ := [nitrileRootCursor 1, nitrileCursor, aminoCursor]))
  have ab := actual_root_priority_callbacks parity n fuel state 0 1 (by decide)
  have ba := actual_root_priority_callbacks parity n fuel state 1 0 (by decide)
  have ac := actual_root_priority_callbacks parity n fuel state 0 2 (by decide)
  have ca := actual_root_priority_callbacks parity n fuel state 2 0 (by decide)
  have ad := actual_root_priority_callbacks parity n fuel state 0 3 (by decide)
  have da := actual_root_priority_callbacks parity n fuel state 3 0 (by decide)
  have bc := actual_root_priority_callbacks parity n fuel state 1 2 (by decide)
  have cb := actual_root_priority_callbacks parity n fuel state 2 1 (by decide)
  have bd := actual_root_priority_callbacks parity n fuel state 1 3 (by decide)
  have db := actual_root_priority_callbacks parity n fuel state 3 1 (by decide)
  have cd := actual_root_priority_callbacks parity n fuel state 2 3 (by decide)
  have dc := actual_root_priority_callbacks parity n fuel state 3 2 (by decide)
  dsimp only [priorityCursor] at ab ba ac ca ad da bc cb bd db cd dc
  change ActualRootCallback _ _ _ _ _ .gt at ab
  change ActualRootCallback _ _ _ _ _ .gt at ac
  change ActualRootCallback _ _ _ _ _ .gt at ad
  change ActualRootCallback _ _ _ _ _ .gt at bc
  change ActualRootCallback _ _ _ _ _ .gt at bd
  change ActualRootCallback _ _ _ _ _ .gt at cd
  change ActualRootCallback _ _ _ _ _ .lt at ba
  change ActualRootCallback _ _ _ _ _ .lt at ca
  change ActualRootCallback _ _ _ _ _ .lt at da
  change ActualRootCallback _ _ _ _ _ .lt at cb
  change ActualRootCallback _ _ _ _ _ .lt at db
  change ActualRootCallback _ _ _ _ _ .lt at dc
  constructor
  · exact strict_four_fast_sort _ _ _ _ _ _ _ _ permutation
      ab.1 ba.1 ac.1 ca.1 ad.1 da.1 bc.1 cb.1 bd.1 db.1 cd.1 dc.1
  · exact strict_four_authoritative_sort _ _ _ _ _ _ _ _ permutation
      ab.2.2 ba.2.2 ac.2.2 ca.2.2 ad.2.2 da.2.2 bc.2.2 cb.2.2 bd.2.2 db.2.2 cd.2.2 dc.2.2

theorem actual_root_authoritative_adjacent (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) :
    compareOccurrenceAdjacentPairsAuthoritative? (expanded parity n) state (fuel + 2)
      (orderedRootCursors n) =
        some [{ ordering := Ordering.gt }, { ordering := Ordering.gt },
          { ordering := Ordering.gt }] := by
  have first := (actual_root_priority_callbacks parity n fuel state 0 1 (by decide)).2.2
  have middle := (actual_root_priority_callbacks parity n fuel state 1 2 (by decide)).2.2
  have last := (actual_root_priority_callbacks parity n fuel state 2 3 (by decide)).2.2
  dsimp only [priorityCursor] at first middle last
  simp [orderedRootCursors, compareOccurrenceAdjacentPairsAuthoritative?, first, middle, last]
  decide

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
