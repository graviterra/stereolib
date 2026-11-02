import TetraStereo.OneCenter.ProductionCIPRule1aPathMatching
import TetraStereo.OneCenter.ProductionCIPRule1aSimpleCycleExact

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace RawMolecule

private theorem firstSome_eq_some_mem {α β : Type*} {f : α → Option β}
    {xs : List α} {y : β} (h : firstSome f xs = some y) :
    ∃ x ∈ xs, f x = some y := by
  induction xs with
  | nil => simp [firstSome] at h
  | cons x xs ih =>
      cases hx : f x with
      | none =>
          rcases ih (by simpa [firstSome, hx] using h) with ⟨x', hxmem, hx'⟩
          exact ⟨x', by simp [hxmem], hx'⟩
      | some value =>
          have hvalue : value = y := by simpa [firstSome, hx] using h
          exact ⟨x, by simp, by simpa [hvalue] using hx⟩

/-- Every recovered alternating path begins at the requested current atom and ends at the target.
This is a structural property of the recursive search, independent of which successful neighbor is
selected by list order. -/
theorem alternatingPath?_head_last (mol : RawMolecule) (blocked target expectedOrder : ℕ) :
    ∀ (fuel current : ℕ) (visited path : List ℕ),
      mol.alternatingPath? blocked target expectedOrder fuel current visited = some path →
        path.head? = some current ∧ path.getLast? = some target
  | 0, current, visited, path, h => by
      simp only [alternatingPath?] at h
      split at h
      · cases Option.some.inj h
        simp_all
      · contradiction
  | fuel + 1, current, visited, path, h => by
      simp only [alternatingPath?] at h
      split at h
      · cases Option.some.inj h
        simp_all
      · rename_i hcurrent
        rcases firstSome_eq_some_mem h with ⟨next, hnextMem, hnext⟩
        split at hnext
        · rename_i hadmissible
          simp only [Option.map_eq_some_iff] at hnext
          rcases hnext with ⟨tail, hrecursive, hpath⟩
          rw [← hpath]
          have ih := alternatingPath?_head_last mol blocked target
            (if expectedOrder == 1 then 2 else 1) fuel next (current :: visited) tail hrecursive
          constructor
          · simp
          · cases tail with
            | nil => simp at ih
            | cons first rest => simpa using ih.2
        · contradiction

private theorem filter_eq_self_of_length_eq {α : Type*} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length = xs.length → xs.filter p = xs
  | [], _ => rfl
  | x :: xs, h => by
      cases hp : p x with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true, if_false,
            List.length_cons] at h
          have hle := List.length_filter_le p xs
          omega
      | true =>
          have htail : (xs.filter p).length = xs.length := by
            simp only [List.filter_cons, hp, if_true, List.length_cons] at h
            omega
          simp [hp, filter_eq_self_of_length_eq p xs htail]

private theorem eraseDups_length_le : ∀ xs : List ℕ, xs.eraseDups.length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      exact Nat.succ_le_succ
        ((eraseDups_length_le (xs.filter fun y => !y == x)).trans
          (List.length_filter_le (fun y => !y == x) xs))
termination_by xs => xs.length
decreasing_by
  exact lt_of_le_of_lt (List.length_filter_le (fun y => !y == x) xs)
    (Nat.lt_succ_self xs.length)

/-- The recognizer's length-preserving `eraseDups` check is exactly a no-repeated-vertex
certificate; it is not merely a heuristic cardinality guard. -/
theorem nodup_of_eraseDups_length_eq (xs : List ℕ)
    (h : xs.eraseDups.length = xs.length) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.eraseDups_cons] at h
      simp only [List.length_cons] at h
      have hfilterLength : (xs.filter fun y => !y == x).length = xs.length := by
        have hleft := eraseDups_length_le (xs.filter fun y => !y == x)
        have hright := List.length_filter_le (fun y => !y == x) xs
        omega
      have hfilter := filter_eq_self_of_length_eq (fun y => !y == x) xs hfilterLength
      rw [List.nodup_cons]
      constructor
      · intro hx
        have hmem : x ∈ xs.filter (fun y => !y == x) := by
          rw [hfilter]
          exact hx
        simp at hmem
      · apply ih
        simpa [hfilter] using h

/-- Successful simple-cycle detection exposes the exact ordered cycle needed by the closed matching
formula: the attached atom first, the reported alternate second, and the written double-bond
partner last, with no repeated vertex. -/
structure SimpleMancudeCycleCertificate (mol : RawMolecule) (attached duplicated : ℕ)
    (cycle : List ℕ) (alternate : ℕ) : Prop where
  exactComponent : mol.SimpleCycleExactComponent attached cycle
  shape : ∃ rest, cycle = attached :: duplicated :: (rest ++ [alternate])
  nodup : cycle.Nodup

/-- The detector's candidate list, factored out so its successful entries can be analyzed without
changing the production recognizer. -/
def simpleCycleAlternatives (mol : RawMolecule) (attached duplicated : ℕ) :
    List (List ℕ × ℕ) :=
  (mol.incidentAtoms attached).filterMap fun candidate =>
    if candidate != duplicated && mol.bondOrder attached candidate == 1 then
      (mol.alternatingPath? attached candidate 1 (mol.atomCount + 1) duplicated
        [attached, duplicated]).map fun path => (path, candidate)
    else none

private theorem mem_simpleCycleAlternatives_path
    (mol : RawMolecule) (attached duplicated candidate : ℕ) (path : List ℕ)
    (hmem : (path, candidate) ∈ mol.simpleCycleAlternatives attached duplicated) :
    mol.alternatingPath? attached candidate 1 (mol.atomCount + 1) duplicated
      [attached, duplicated] = some path := by
  simp only [simpleCycleAlternatives, List.mem_filterMap] at hmem
  rcases hmem with ⟨source, hsource, hresult⟩
  split at hresult
  · simp only [Option.map_eq_some_iff] at hresult
    rcases hresult with ⟨found, hfound, hpairs⟩
    have hcandidate : source = candidate := congrArg Prod.snd hpairs
    have hpath : found = path := congrArg Prod.fst hpairs
    simpa [hcandidate, hpath] using hfound
  · contradiction

/-- Successful recognition supplies an occurrence-precise ordered simple-cycle certificate.  In
particular, the written double-bond partner is the second cycle vertex and the independently found
single-bond alternate is the final vertex. -/
theorem simpleMancudeCycle?_certificate (mol : RawMolecule)
    (attached duplicated : ℕ) (cycle : List ℕ) (alternate : ℕ)
    (hresult : mol.simpleMancudeCycle? attached duplicated = some (cycle, alternate)) :
    mol.SimpleMancudeCycleCertificate attached duplicated cycle alternate := by
  have hexact := mol.simpleMancudeCycle?_exactComponent attached duplicated cycle alternate hresult
  unfold simpleMancudeCycle? at hresult
  split at hresult
  · contradiction
  · rename_i hdouble
    let alternatives := mol.simpleCycleAlternatives attached duplicated
    change (match alternatives with
      | [(path, candidate)] =>
          let foundCycle := attached :: path
          let reportedEdges := cycleEdges foundCycle
          let localizedVertices := mol.localizedMancudeComponentVertices attached
          let localizedEdges := mol.localizedMancudeComponentEdges attached
          let exactComponent :=
            foundCycle.all localizedVertices.contains &&
              localizedVertices.all foundCycle.contains &&
              reportedEdges.all (fun edge =>
                containsUndirectedEdge localizedEdges edge.1 edge.2) &&
              localizedEdges.all (fun edge =>
                containsUndirectedEdge reportedEdges edge.1 edge.2)
          if 3 ≤ foundCycle.length &&
              foundCycle.eraseDups.length == foundCycle.length &&
              mol.cycleIsMancude foundCycle && exactComponent then
            some (foundCycle, candidate)
          else none
      | _ => none) = some (cycle, alternate) at hresult
    cases halternatives : alternatives with
    | nil => simp [halternatives] at hresult
    | cons first tail =>
        cases tail with
        | cons second rest => simp [halternatives] at hresult
        | nil =>
            rcases first with ⟨path, candidate⟩
            simp only [halternatives] at hresult
            split at hresult
            · rename_i haccepted
              have hpairs : attached :: path = cycle ∧ candidate = alternate :=
                Prod.mk.inj (Option.some.inj hresult)
              have hpath := mem_simpleCycleAlternatives_path mol attached duplicated
                candidate path (by simp [alternatives, halternatives])
              have hendpoints := mol.alternatingPath?_head_last attached candidate 1
                (mol.atomCount + 1) duplicated [attached, duplicated] path hpath
              obtain ⟨middle, hpathEq⟩ : ∃ middle, path = duplicated :: (middle ++ [candidate]) := by
                cases path with
                | nil => simp at hendpoints
                | cons first rest =>
                    have hfirst : first = duplicated := by simpa using hendpoints.1
                    subst first
                    cases rest using List.reverseRecOn with
                    | nil =>
                        have hminimum : 3 ≤ (attached :: [duplicated]).length := by
                          simp only [Bool.and_eq_true, decide_eq_true_eq] at haccepted
                          tauto
                        simp at hminimum
                    | append_singleton middle last =>
                        have hlast : last = candidate := by
                          have hlastEq := hendpoints.2
                          change ((duplicated :: middle) ++ [last]).getLast? =
                            some candidate at hlastEq
                          rw [List.getLast?_append] at hlastEq
                          simpa using hlastEq
                        subst last
                        exact ⟨middle, rfl⟩
              have hlength : cycle.eraseDups.length = cycle.length := by
                simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at haccepted
                rw [← hpairs.1]
                tauto
              refine
                { exactComponent := hexact
                  shape := ⟨middle, ?_⟩
                  nodup := nodup_of_eraseDups_length_eq cycle hlength }
              rw [← hpairs.1, hpathEq, hpairs.2]
            · contradiction

end RawMolecule

end
end OneCenter
end TetraStereo
