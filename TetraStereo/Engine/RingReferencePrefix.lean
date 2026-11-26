import TetraStereo.Engine.RingFullPathPairs

set_option autoImplicit false

namespace TetraStereo.Engine.RingReferencePrefix
open OneCenter CertifiedLocalizedCIPInput

/-- A complete highest-priority chiral block precedes an unrestricted suffix.
Counts are taken from the actual retained reference population. -/
structure Prefix (population : List RS) (word : RS → List Bool) where
  rightSuffix : List Bool
  leftSuffix : List Bool
  right : word .R = List.replicate (population.count .R) true ++
    List.replicate (population.count .S) false ++ rightSuffix
  left : word .S = List.replicate (population.count .S) true ++
    List.replicate (population.count .R) false ++ leftSuffix

/-- A larger initial run of likes wins at its first extra like, independently
of everything after the highest-priority block. -/
theorem block_lt {a b c d : Nat} (less : a < c) (positive : 0 < b)
    (xs ys : List Bool) :
    List.replicate a true ++ List.replicate b false ++ xs <
      List.replicate c true ++ List.replicate d false ++ ys := by
  apply (List.lt_iff_lex_lt _ _).mpr
  induction a generalizing c with
  | zero =>
    cases b with
    | zero => omega
    | succ b =>
      cases c with
      | zero => omega
      | succ c => exact List.Lex.rel (by decide)
  | succ a ih =>
    cases c with
    | zero => omega
    | succ c => exact List.Lex.cons (ih (by omega))

theorem majority_right {p : List RS} {w : RS → List Bool} (h : Prefix p w)
    (majority : p.count .S < p.count .R) (minority : 0 < p.count .R) : w .S < w .R := by
  rw [h.right,h.left]
  exact block_lt majority minority _ _

theorem majority_left {p : List RS} {w : RS → List Bool} (h : Prefix p w)
    (majority : p.count .R < p.count .S) (minority : 0 < p.count .S) : w .R < w .S := by
  rw [h.right,h.left]
  exact block_lt majority minority _ _

/-- Actual selected reference functions count the same retained population. -/
theorem selected (hits : List RingRetainedReferenceGroup.Hit) (rev : Bool) :
    RingRetainedReferenceGroup.references hits rev =
      localizedRule4bReferencesFromPopulation (RingRetainedReferenceGroup.hands hits rev) := rfl

/-- Both-dual contests are exactly Hanson's comparison of the two maxima. -/
theorem dual (x y : RS → List Bool) :
    RingFullPathPairs.contest x y [.R,.S] [.R,.S] =
      some (match RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S) with
        | .lt => -1 | .eq => 0 | .gt => 1) := by
  rw [RingOccurrenceStereo.fourLists_order]
  rfl

/-- The first extra like proves the single-reference advantage at equal block
width; all later chiral blocks remain unrestricted. -/
theorem single_over_balanced {p q : List RS} {x y : RS → List Bool}
    (hx : Prefix p x) (hy : Prefix q y)
    (majority : p.count .S < p.count .R)
    (balanced : q.count .R = q.count .S)
    (width : p.count .R + p.count .S = q.count .R + q.count .S) :
    max (y .R) (y .S) < x .R := by
  have likes : q.count .R < p.count .R := by omega
  have unlikes : 0 < q.count .S := by omega
  apply max_lt
  · rw [hy.right,hx.right]
    exact block_lt likes unlikes _ _
  · rw [hy.left,hx.right]
    exact block_lt (by omega) (by omega) _ _

/-- The majority reference realizes the maximum of the two full words. -/
theorem majority_right_max {p : List RS} {w : RS → List Bool} (h : Prefix p w)
    (majority : p.count .S < p.count .R) : max (w .R) (w .S) = w .R :=
  max_eq_left (le_of_lt (majority_right h majority (by omega)))

theorem majority_left_max {p : List RS} {w : RS → List Bool} (h : Prefix p w)
    (majority : p.count .R < p.count .S) : max (w .R) (w .S) = w .S :=
  max_eq_right (le_of_lt (majority_left h majority (by omega)))

/-- Reference selection itself selects precisely the word maximizing the
Hanson contest whenever the retained block has a strict majority. -/
theorem selected_right {p : List RS} {w : RS → List Bool} (h : Prefix p w)
    (occupied : p ≠ []) (majority : p.count .S < p.count .R) :
    localizedRule4bReferencesFromPopulation p = [.R] ∧
      max (w .R) (w .S) = w .R := by
  refine ⟨?_,majority_right_max h majority⟩
  cases p with
  | nil => contradiction
  | cons a p =>
    simp only [localizedRule4bReferencesFromPopulation,List.isEmpty_cons,
      Bool.false_eq_true,ite_false,← List.count_eq_length_filter,if_pos majority]

theorem selected_left {p : List RS} {w : RS → List Bool} (h : Prefix p w)
    (occupied : p ≠ []) (majority : p.count .R < p.count .S) :
    localizedRule4bReferencesFromPopulation p = [.S] ∧
      max (w .R) (w .S) = w .S := by
  refine ⟨?_,majority_left_max h majority⟩
  cases p with
  | nil => contradiction
  | cons a p =>
    simp only [localizedRule4bReferencesFromPopulation,List.isEmpty_cons,
      Bool.false_eq_true,ite_false,← List.count_eq_length_filter,
      if_neg (Nat.not_lt.mpr (Nat.le_of_lt majority)),if_pos majority]

/-- The unequal reference-count branch of the actual contest agrees with
Hanson under the equal-width block hypothesis. -/
theorem single_dual_agrees {p q : List RS} {x y : RS → List Bool}
    (hx : Prefix p x) (hy : Prefix q y)
    (majority : p.count .S < p.count .R)
    (balanced : q.count .R = q.count .S)
    (width : p.count .R + p.count .S = q.count .R + q.count .S) :
    RingFullPathPairs.contest x y [.R] [.R,.S] =
      some (match RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S) with
        | .lt => -1 | .eq => 0 | .gt => 1) := by
  have win := single_over_balanced hx hy majority balanced width
  have law (a b : List Bool) : compare a b = .lt ↔ a < b :=
    DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => by decide +revert)
      (fun _ _ => Std.compare_eq_eq_iff_eq) a b
  have gt : compare (x .R) (max (y .R) (y .S)) = .gt := by
    have lt := (law _ _).mpr win
    have swap := Std.OrientedCmp.eq_swap (cmp := compare) (a := x .R) (b := max (y .R) (y .S))
    rw [lt] at swap
    exact swap
  rw [RingOccurrenceStereo.fourLists_order,majority_right_max hx majority,gt]
  rfl

/-- The left-majority case has the same strict advantage over a balanced
block, including arbitrary suffixes on all four words. -/
theorem left_over_balanced {p q : List RS} {x y : RS → List Bool}
    (hx : Prefix p x) (hy : Prefix q y)
    (majority : p.count .R < p.count .S)
    (balanced : q.count .R = q.count .S)
    (width : p.count .R + p.count .S = q.count .R + q.count .S) :
    max (y .R) (y .S) < x .S := by
  apply max_lt
  · rw [hy.right,hx.left]
    exact block_lt (by omega) (by omega) _ _
  · rw [hy.left,hx.left]
    exact block_lt (by omega) (by omega) _ _

/-- Once the selected reference realizes each arm's maximum, the actual
single/single contest is precisely the Hanson procedure. -/
theorem single_single_agrees (x y : RS → List Bool) (s t : RS)
    (left : max (x .R) (x .S) = x s) (right : max (y .R) (y .S) = y t) :
    RingFullPathPairs.contest x y [s] [t] =
      some (match RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S) with
        | .lt => -1 | .eq => 0 | .gt => 1) := by
  rw [RingOccurrenceStereo.fourLists_order,left,right]
  rfl

/-- A strict population majority constructs the selected reference and
proves its maximality, rather than postulating a preferred word. -/
theorem strict_majority_selects_max {p : List RS} {x : RS → List Bool}
    (h : Prefix p x) (occupied : p ≠ []) (strict : p.count .R ≠ p.count .S) :
    ∃ s, localizedRule4bReferencesFromPopulation p = [s] ∧
      max (x .R) (x .S) = x s := by
  rcases lt_or_gt_of_ne strict with less | greater
  · exact ⟨.S,selected_left h occupied less⟩
  · exact ⟨.R,selected_right h occupied greater⟩

/-- For two unbalanced retained populations the selected-reference contest
and Hanson agree, with the selected words derived from their block counts. -/
theorem two_strict_majorities {p q : List RS} {x y : RS → List Bool}
    (hx : Prefix p x) (hy : Prefix q y) (hp : p ≠ []) (hq : q ≠ [])
    (sp : p.count .R ≠ p.count .S) (sq : q.count .R ≠ q.count .S) :
    RingFullPathPairs.contest x y (localizedRule4bReferencesFromPopulation p)
      (localizedRule4bReferencesFromPopulation q) =
      some (match RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S) with
        | .lt => -1 | .eq => 0 | .gt => 1) := by
  obtain ⟨s,hs,mx⟩ := strict_majority_selects_max hx hp sp
  obtain ⟨t,ht,my⟩ := strict_majority_selects_max hy hq sq
  rw [hs,ht]
  exact single_single_agrees x y s t mx my

theorem selected_balanced {p : List RS} (occupied : p ≠ [])
    (balanced : p.count .R = p.count .S) :
    localizedRule4bReferencesFromPopulation p = [.R,.S] := by
  cases p with
  | nil => contradiction
  | cons a p =>
    simp only [localizedRule4bReferencesFromPopulation,List.isEmpty_cons,
      Bool.false_eq_true,ite_false,← List.count_eq_length_filter]
    rw [balanced]
    simp

theorem two_balanced {p q : List RS} (x y : RS → List Bool)
    (hp : p ≠ []) (hq : q ≠ [])
    (bp : p.count .R = p.count .S) (bq : q.count .R = q.count .S) :
    RingFullPathPairs.contest x y (localizedRule4bReferencesFromPopulation p)
      (localizedRule4bReferencesFromPopulation q) =
      some (match RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S) with
        | .lt => -1 | .eq => 0 | .gt => 1) := by
  rw [selected_balanced hp bp,selected_balanced hq bq]
  exact dual x y

def score (o : Ordering) : Int := match o with
  | .lt => -1 | .eq => 0 | .gt => 1

private theorem compare_lt {x y : List Bool} (h : x < y) : compare x y = .lt :=
  (DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => by decide +revert)
      (fun _ _ => Std.compare_eq_eq_iff_eq) x y).mpr h

private theorem compare_gt {x y : List Bool} (h : y < x) : compare x y = .gt := by
  have swap := Std.OrientedCmp.eq_swap (cmp := compare) (a := x) (b := y)
  rw [compare_lt h] at swap
  exact swap

private theorem unbalanced_over_balanced {p q : List RS} {x y : RS → List Bool}
    (hx : Prefix p x) (hy : Prefix q y) (sp : p.count .R ≠ p.count .S)
    (bq : q.count .R = q.count .S)
    (width : p.count .R + p.count .S = q.count .R + q.count .S) :
    max (y .R) (y .S) < max (x .R) (x .S) := by
  rcases lt_or_gt_of_ne sp with h | h
  · rw [majority_left_max hx h]
    exact left_over_balanced hx hy h bq width
  · rw [majority_right_max hx h]
    exact single_over_balanced hx hy h bq width

/-- Equal-size highest-priority blocks make the Blue Book majority/dual
policy coincide with Hanson's best-of-both policy. No suffix is constrained. -/
theorem policy_equivalence {p q : List RS} {x y : RS → List Bool}
    (hx : Prefix p x) (hy : Prefix q y) (hp : p ≠ []) (hq : q ≠ [])
    (width : p.count .R + p.count .S = q.count .R + q.count .S) :
    RingFullPathPairs.contest x y (localizedRule4bReferencesFromPopulation p)
      (localizedRule4bReferencesFromPopulation q) =
      some (score (RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S))) := by
  by_cases bp : p.count .R = p.count .S
  · by_cases bq : q.count .R = q.count .S
    · exact two_balanced x y hp hq bp bq
    · obtain ⟨t,ht,_⟩ := strict_majority_selects_max hy hq bq
      have win := unbalanced_over_balanced hy hx bq bp width.symm
      rw [selected_balanced hp bp,ht,RingOccurrenceStereo.fourLists_order,compare_lt win]
      rfl
  · by_cases bq : q.count .R = q.count .S
    · obtain ⟨s,hs,_⟩ := strict_majority_selects_max hx hp bp
      have win := unbalanced_over_balanced hx hy bp bq width
      rw [hs,selected_balanced hq bq,RingOccurrenceStereo.fourLists_order,compare_gt win]
      rfl
    · exact two_strict_majorities hx hy hp hq bp bq

/-- Instantiation uses the actual molecularly retained populations and the
actual reference selector, with only the structural block property supplied. -/
theorem retained_policy_equivalence
    (a b : List RingRetainedReferenceGroup.Hit) (rev : Bool) (x y : RS → List Bool)
    (hx : Prefix (RingRetainedReferenceGroup.hands a rev) x)
    (hy : Prefix (RingRetainedReferenceGroup.hands b rev) y)
    (ha : RingRetainedReferenceGroup.hands a rev ≠ [])
    (hb : RingRetainedReferenceGroup.hands b rev ≠ [])
    (width : (RingRetainedReferenceGroup.hands a rev).count .R +
        (RingRetainedReferenceGroup.hands a rev).count .S =
      (RingRetainedReferenceGroup.hands b rev).count .R +
        (RingRetainedReferenceGroup.hands b rev).count .S) :
    RingFullPathPairs.contest x y (RingRetainedReferenceGroup.references a rev)
      (RingRetainedReferenceGroup.references b rev) =
      some (score (RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S))) :=
  policy_equivalence hx hy ha hb width

/-- Without any chiral occurrence both words are empty, so the actual contest
and the maximum-word procedure tie. -/
theorem no_chiral (x y : RS → List Bool) (hx : ∀ s, x s = []) (hy : ∀ s, y s = []) :
    RingFullPathPairs.contest x y [] [] = some 0 ∧
    RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S) = .eq := by
  simp [RingFullPathPairs.contest,hx,hy,RingOccurrenceStereo.fourLists]

/-- A descending Boolean row is its run of likes followed by unlikes. -/
theorem boolean_runs (bits : List Bool)
    (sorted : bits.Pairwise (fun a b => b ≤ a)) :
    bits = List.replicate (bits.count true) true ++ List.replicate (bits.count false) false := by
  induction bits with
  | nil => simp
  | cons a bits ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
    have rest := ih tail
    cases a with
    | true => simpa [List.replicate_succ] using congrArg (List.cons true) rest
    | false =>
      have noTrue : true ∉ bits := by
        intro mem
        have bad := head true mem
        contradiction
      have zero : bits.count true = 0 := List.count_eq_zero.mpr noTrue
      simpa [zero,List.replicate_succ] using congrArg (List.cons false) rest

/-- Descending lexicographic path/bit order, written without committing to
an encoding of pairs into traversal keys. -/
def Descending {α : Type} [LinearOrder α] (a b : α × Bool) : Prop :=
  b.1 ≤ a.1 ∧ (a.1 = b.1 → b.2 ≤ a.2)

private theorem top_partition {α : Type} [LinearOrder α] (top : α)
    (xs : List (α × Bool)) (sorted : xs.Pairwise Descending)
    (bounded : ∀ x ∈ xs, x.1 ≤ top) :
    xs = xs.filter (fun x => x.1 == top) ++ xs.filter (fun x => !(x.1 == top)) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp sorted
    by_cases eqn : a.1 = top
    · simp only [List.filter_cons,eqn,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,
        ite_false,ite_true,List.cons_append]
      exact congrArg (List.cons a) (ih tail (fun x hx => bounded x (List.mem_cons_of_mem _ hx)))
    · have none : ∀ x ∈ xs, x.1 ≠ top := by
        intro x hx same
        have h := (head x hx).1
        rw [same] at h
        exact eqn (le_antisymm (bounded a List.mem_cons_self) h)
      have empty : xs.filter (fun x => x.1 == top) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp [none x hx]
      have full : xs.filter (fun x => !(x.1 == top)) = xs := by
        apply List.filter_eq_self.mpr
        intro x hx
        simp [none x hx]
      simp [eqn,empty,full]

/-- In one sorted sphere, all observations of the maximal path form the
initial block. Their bits are sorted with true before false. A population
permutation fixes the two run lengths; the remainder and later spheres are
unrestricted. -/
theorem sorted_sphere_prefix {α : Type} [LinearOrder α] (top : α)
    (xs : List (α × Bool)) (population later : List Bool)
    (sorted : xs.Pairwise Descending)
    (bounded : ∀ x ∈ xs, x.1 ≤ top)
    (same : ((xs.filter (fun x => x.1 == top)).map Prod.snd).Perm population) :
    ∃ suffix, xs.map Prod.snd ++ later =
      List.replicate (population.count true) true ++
        List.replicate (population.count false) false ++ suffix := by
  let group := xs.filter (fun x => x.1 == top)
  have ordered : (group.map Prod.snd).Pairwise (fun a b => b ≤ a) := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem ?_ (sorted.filter _)
    intro a b ha hb order
    have ea : a.1 = top := by simpa using (List.mem_filter.mp ha).2
    have eb : b.1 = top := by simpa using (List.mem_filter.mp hb).2
    exact order.2 (ea.trans eb.symm)
  have runs := boolean_runs (group.map Prod.snd) ordered
  have ct := same.count_eq true
  have cf := same.count_eq false
  rw [ct,cf] at runs
  refine ⟨(xs.filter (fun x => !(x.1 == top))).map Prod.snd ++ later,?_⟩
  conv_lhs => rw [top_partition top xs sorted bounded]
  rw [List.map_append,← List.append_assoc,runs]

theorem like_counts (p : List RS) (seed : RS) :
    (p.map (fun h => h == seed)).count true = p.count seed ∧
      (p.map (fun h => h == seed)).count false = p.count seed.swap := by
  induction p with
  | nil => simp
  | cons h p ih => cases h <;> cases seed <;> simp_all [RS.swap,show (RS.R == RS.S) = false from rfl,show (RS.S == RS.R) = false from rfl]

/-- Two independently sorted seed-specific spheres yield the precise
structural hypothesis consumed by the policy theorem. -/
theorem prefix_of_sorted_spheres {α : Type} [LinearOrder α] (top : α)
    (p : List RS) (rows : RS → List (α × Bool)) (later : RS → List Bool)
    (sorted : ∀ seed, (rows seed).Pairwise Descending)
    (bounded : ∀ seed x, x ∈ rows seed → x.1 ≤ top)
    (same : ∀ seed, (((rows seed).filter (fun x => x.1 == top)).map Prod.snd).Perm
      (p.map (fun h => h == seed))) :
    Nonempty (Prefix p (fun seed => (rows seed).map Prod.snd ++ later seed)) := by
  obtain ⟨r,hr⟩ := sorted_sphere_prefix top (rows .R) (p.map (fun h => h == .R))
    (later .R) (sorted .R) (bounded .R) (same .R)
  obtain ⟨s,hs⟩ := sorted_sphere_prefix top (rows .S) (p.map (fun h => h == .S))
    (later .S) (sorted .S) (bounded .S) (same .S)
  refine ⟨⟨r,s,?_,?_⟩⟩
  · simpa only [(like_counts p .R).1,(like_counts p .R).2,RS.swap] using hr
  · simpa only [(like_counts p .S).1,(like_counts p .S).2,RS.swap] using hs

open RingRetainedReferenceGroup (Hit group hands)

private theorem group_perm {xs ys : List Hit} (same : xs.Perm ys) :
    (group xs).Perm (group ys) := by
  have predicate (h : Hit) : xs.any (fun x => RingRetainedReferenceGroup.senior x.path h.path) =
      ys.any (fun x => RingRetainedReferenceGroup.senior x.path h.path) :=
    Bool.eq_iff_iff.mpr (by simp only [List.any_eq_true,same.mem_iff])
  unfold group
  simp_rw [predicate]
  exact same.filter _

private theorem group_geometry (hits : List Hit) (rev : Bool) :
    group (hits.map (fun h => h.geometry rev)) = (group hits).map (fun h => h.geometry rev) := by
  simp [group,List.filter_map,List.any_map,Function.comp_def,Hit.geometry]

private theorem first_group (head : Hit) (tail later : List Hit)
    (depth : ∀ h ∈ head :: tail, h.path.length = head.path.length)
    (bound : ∀ h ∈ head :: tail, h.path ≤ head.path)
    (far : ∀ h ∈ later, head.path.length < h.path.length) :
    group ((head :: tail) ++ later) = (head :: tail).filter (fun h => h.path == head.path) := by
  have equality : group ((head :: tail) ++ later) =
      ((head :: tail) ++ later).filter (fun h => h.path == head.path) := by
    apply List.filter_congr
    intro h mem
    apply Bool.eq_iff_iff.mpr
    have crit := RingRetainedReferenceGroup.mem_group (h := h) (hits := (head :: tail) ++ later)
    simp only [group,List.mem_filter] at crit
    have criterion : (∀ x ∈ (head :: tail) ++ later,
        h.path.length ≤ x.path.length ∧ (x.path.length = h.path.length → x.path ≤ h.path)) ↔
        h.path = head.path := by
      constructor
      · intro all
        have best := all head (List.mem_append_left _ List.mem_cons_self)
        rcases List.mem_append.mp mem with first | last
        · exact le_antisymm (bound h first) (best.2 (depth h first).symm)
        · have := far h last; omega
      · intro eqn x hx
        rw [eqn]
        rcases List.mem_append.mp hx with first | last
        · exact ⟨(depth x first).symm.le,fun _ => bound x first⟩
        · exact ⟨(far x last).le,fun same => by have := far x last; omega⟩
    simpa only [mem,true_and,beq_iff_eq] using crit.trans (and_congr_right fun _ => criterion)
  rw [equality,List.filter_append]
  have empty : later.filter (fun h => h.path == head.path) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro h hh
    have lt := far h hh
    simp only [beq_iff_eq]
    intro eqn
    rw [eqn] at lt
    omega
  rw [empty,List.append_nil]

/-- A first occupied sphere identifies the actual highest-priority retained
population. Reflection changes hands and preserves all path priorities. -/
theorem first_sphere_population (hits : List Hit) (rev : Bool) (head : Hit) (tail later : List Hit)
    (same : (hits.map (fun h => h.geometry rev)).Perm ((head :: tail) ++ later))
    (depth : ∀ h ∈ head :: tail, h.path.length = head.path.length)
    (bound : ∀ h ∈ head :: tail, h.path ≤ head.path)
    (far : ∀ h ∈ later, head.path.length < h.path.length) (seed : RS) :
    (((head :: tail).filter (fun h => h.path == head.path)).map (fun h => h.hand == seed)).Perm
      ((hands hits rev).map (fun h => h == seed)) := by
  have perm := (group_perm same).symm
  rw [first_group head tail later depth bound far,group_geometry] at perm
  have result := perm.map (fun h => h.hand == seed)
  simpa only [hands,List.map_map,Function.comp_def,Hit.geometry] using result

end TetraStereo.Engine.RingReferencePrefix

assert_kernel_only TetraStereo.Engine.RingReferencePrefix.block_lt
assert_kernel_only TetraStereo.Engine.RingReferencePrefix.single_over_balanced

assert_kernel_only TetraStereo.Engine.RingReferencePrefix.policy_equivalence
assert_kernel_only TetraStereo.Engine.RingReferencePrefix.retained_policy_equivalence
assert_kernel_only TetraStereo.Engine.RingReferencePrefix.sorted_sphere_prefix
assert_kernel_only TetraStereo.Engine.RingReferencePrefix.prefix_of_sorted_spheres
assert_kernel_only TetraStereo.Engine.RingReferencePrefix.like_counts
assert_kernel_only TetraStereo.Engine.RingReferencePrefix.first_sphere_population
