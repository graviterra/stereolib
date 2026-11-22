import TetraStereo.Engine.RingFrozenWordDiagnosis
import TetraStereo.Engine.RingActiveMagnitude

set_option autoImplicit false

namespace TetraStereo.Engine.RingProximalPair
open OneCenter LocalizedChemicalRing RingActivePairs
open RingClosedPairGroup (FIFO upperAt)
open RingNestedActivePair (Reader)
open RingSeededPairs (listSign? localSign? compareBits like fromVisits?)

private theorem strict_bits {a b : List Bool} (strict : compareBits a b ≠ 0) (x y : List Bool) :
    compareBits (a ++ x) (b ++ y) = compareBits a b := by
  induction a generalizing b with
  | nil => exact False.elim (strict (by cases b <;> rfl))
  | cons h a ih =>
    cases b with
    | nil => exact False.elim (strict rfl)
    | cons k b =>
      by_cases same : h = k
      · simp [compareBits,same] at strict ⊢
        exact ih strict
      · simp [compareBits,same]

/-- Once the aligned prefixes strictly decide the single-reference Rule 4b
branch, arbitrary later visits, publications and Rule 5 passes preserve it.
The two inspected prefixes already contain their respective reference hands. -/
theorem strict_prefix {a b : List (Option RS)} {v : Int}
    (won : localSign? a b = some v) (strict : v ≠ 0)
    (x y ar br as' bs : List (Option RS)) :
    fromVisits? (a ++ x) (b ++ y) ar br as' bs = some ⟨v,none⟩ := by
  cases ha : a.findSome? id with
  | none =>
    cases hb : b.findSome? id <;> simp [localSign?,ha,hb] at won
    simp_all
  | some h =>
    cases hb : b.findSome? id with
    | none => simp [localSign?,ha,hb] at won
    | some k =>
      have eqn : compareBits (a.map (like h)) (b.map (like k)) = v := by
        simpa [localSign?,ha,hb] using won
      have nz : compareBits (a.map (like h)) (b.map (like k)) ≠ 0 := fun tie => strict (eqn.symm.trans tie)
      simp [fromVisits?,localSign?,List.findSome?_append,ha,hb,List.map_append,strict_bits nz,eqn,strict]

/-- Reflection exchanges the two reference passes. Their two scores fit the
physical signed alphabet exactly when both passes agree on whether there is
a tie. Their strict signs and their sibling orders can differ. -/
theorem mirror_values_iff (r s : Int) :
    (CentresRing.PairList.combine r s,CentresRing.PairList.combine s r) ∈ molecularValues ↔
    (r = 0 ↔ s = 0) := by
  rcases lt_trichotomy r 0 with hr | hr | hr <;> rcases lt_trichotomy s 0 with hs | hs | hs <;>
    simp (disch := omega) [CentresRing.PairList.combine,molecularValues,hr,hs] <;> omega

def seededScore? (ar br as' bs : List (Option RS)) : Option Int := do
  let r ← listSign? .R ar br
  let s ← listSign? .S as' bs
  return CentresRing.PairList.combine r s

/-- The reflected R walk follows the reflected S traversal of the original
and conversely. The two original seeds may follow different traversals.
Under this physical transport the only remaining condition on magnitudes is
agreement of the two original equality judgments. -/
theorem seed_transport {ar br as' bs : List (Option RS)} {r s : Int}
    (pos : listSign? .R ar br = some r) (neg : listSign? .S as' bs = some s) :
    seededScore? ar br as' bs = some (CentresRing.PairList.combine r s) ∧
    seededScore? (swapWalk as') (swapWalk bs) (swapWalk ar) (swapWalk br) =
      some (CentresRing.PairList.combine s r) ∧
    ((CentresRing.PairList.combine r s,CentresRing.PairList.combine s r) ∈ molecularValues ↔
      (r = 0 ↔ s = 0)) := by
  refine ⟨by simp [seededScore?,pos,neg],?_,mirror_values_iff r s⟩
  simp [seededScore?,fixed_swap,RS.swap,pos,neg]

/-- Equal populations alone permit a one-seed tie. This is a list-level
control for the additional molecular equality obligation. -/
theorem population_control :
    let a : List (Option RS) := [some .R,some .S]
    let b : List (Option RS) := [some .S,some .R]
    a.Perm b ∧ seededScore? a a a b = some 0 ∧
      seededScore? (swapWalk a) (swapWalk b) (swapWalk a) (swapWalk a) = some (-2) := by
  exact ⟨List.Perm.swap ..,by decide +kernel,by decide +kernel⟩

/-- A FIFO traversal visits the proximal occurrence first. An uppercase hand
there decides the first accepted bit for either reference. -/
private theorem starts {i : Input} {a : Arm i} {order xs} {read : Reader i} {rev hand}
    (walk : FIFO i order [a] xs) (first : upperAt read rev a = some hand) :
    ∃ tail, xs.filterMap (upperAt read rev) = hand :: tail := by
  cases walk with
  | @step _ _ _ out _ _ _ => exact ⟨out.filterMap (upperAt read rev),by simp [first]⟩

/-- If the two proximal occurrences publish opposite uppercase hands, any
one pair of complete traversals suffices to check the length precondition.
The remaining publications can contain either hand in any legal order. -/
theorem fixed_sign {i : Input} {a b : Arm i} (read : Reader i) (rev : Bool)
    {leftOrder rightOrder seedLeft seedRight x y u v h k}
    (left : FIFO i leftOrder [a] x) (right : FIFO i rightOrder [b] y)
    (size : (x.filterMap (upperAt read rev)).length = (y.filterMap (upperAt read rev)).length)
    (ah : upperAt read rev a = some h) (bk : upperAt read rev b = some k) (opp : h ≠ k)
    (seed : RS) (lw : FIFO i seedLeft [a] u) (rw' : FIFO i seedRight [b] v) :
    listSign? seed (u.map (upperAt read rev)) (v.map (upperAt read rev)) =
      some (CentresRing.PairList.pairSign seed h k) := by
  have lengths := ((RingFIFOPopulation.accepted_perm read rev (List.Perm.refl [a]) lw left).length_eq).trans
    (size.trans (RingFIFOPopulation.accepted_perm read rev (List.Perm.refl [b]) right rw').length_eq)
  obtain ⟨us,hu⟩ := starts lw ah
  obtain ⟨vs,hv⟩ := starts rw' bk
  simp only [listSign?,List.filterMap_map,Function.comp_def,id_eq,hu,hv,List.map_cons]
  cases seed <;> cases h <;> cases k <;> simp_all [RingSeededPairs.compareBits,CentresRing.PairList.pairSign]

/-- Exact signed Rule 5 magnitude for two independent seed passes. The
four sibling sorts may differ from each other and from both count witnesses. -/
theorem magnitude {i : Input} {a b : Arm i} (read : Reader i) (rev : Bool)
    {leftOrder rightOrder rL rR sL sR x y xr yr xs ys h k}
    (left : FIFO i leftOrder [a] x) (right : FIFO i rightOrder [b] y)
    (size : (x.filterMap (upperAt read rev)).length = (y.filterMap (upperAt read rev)).length)
    (ah : upperAt read rev a = some h) (bk : upperAt read rev b = some k) (opp : h ≠ k)
    (ar : FIFO i rL [a] xr) (br : FIFO i rR [b] yr)
    (as' : FIFO i sL [a] xs) (bs : FIFO i sR [b] ys) :
    (do let r ← listSign? .R (xr.map (upperAt read rev)) (yr.map (upperAt read rev))
        let s ← listSign? .S (xs.map (upperAt read rev)) (ys.map (upperAt read rev))
        return CentresRing.PairList.combine r s) = some (if h = .R then (2 : Int) else -2) := by
  rw [fixed_sign read rev left right size ah bk opp .R ar br,
      fixed_sign read rev left right size ah bk opp .S as' bs]
  cases h <;> cases k <;> simp_all [CentresRing.PairList.combine,CentresRing.PairList.pairSign]

private def labelAt {i : Input} (read : Reader i) (rev : Bool) (q : Arm i) :=
  ((read q.occurrence).join).map fun p => if rev then p.2 else p.1

/-- A Rule 4a observation records only the unit class of an occurrence. -/
def unitClasses {i : Input} (read : Reader i) (rev : Bool) (xs : List (Arm i)) :=
  xs.map fun q => RingNestedActivePair.unit (labelAt read rev q)

private theorem count_upper {i : Input} (read : Reader i) (rev : Bool) (xs : List (Arm i)) :
    (xs.filterMap (upperAt read rev)).length = (unitClasses read rev xs).count 2 := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    change (List.filterMap (upperAt read rev) (q :: qs)).length =
      (RingNestedActivePair.unit (labelAt read rev q) :: unitClasses read rev qs).count 2
    have atQ : upperAt read rev q = RingNestedActivePair.upper (labelAt read rev q) := rfl
    cases h : labelAt read rev q with
    | none => simp [atQ,h,RingNestedActivePair.upper,RingNestedActivePair.unit,ih]
    | some d =>
      cases d <;> simp [atQ,h,RingNestedActivePair.upper,RingNestedActivePair.unit,ih]

/-- The cardinality required by Rule 5 is already forced by matching Rule 4a
unit populations on the nonterminal walks. This applies to every joint
completion of unknown hands respecting those classes and the proximal readings. -/
theorem magnitude_of_unit_match {i : Input} {a b : Arm i} (read : Reader i) (rev : Bool)
    {leftOrder rightOrder rL rR sL sR x y xr yr xs ys h k}
    (left : FIFO i leftOrder [a] x) (right : FIFO i rightOrder [b] y)
    (units : (unitClasses read rev x).Perm (unitClasses read rev y))
    (ah : upperAt read rev a = some h) (bk : upperAt read rev b = some k) (opp : h ≠ k)
    (ar : FIFO i rL [a] xr) (br : FIFO i rR [b] yr)
    (as' : FIFO i sL [a] xs) (bs : FIFO i sR [b] ys) :
    (do let r ← listSign? .R (xr.map (upperAt read rev)) (yr.map (upperAt read rev))
        let s ← listSign? .S (xs.map (upperAt read rev)) (ys.map (upperAt read rev))
        return CentresRing.PairList.combine r s) = some (if h = .R then (2 : Int) else -2) :=
  magnitude read rev left right (by rw [count_upper,count_upper]; exact units.count_eq 2)
    ah bk opp ar br as' bs

private def inventory {i : Input} : Nat → List (Arm i) → List (Arm i)
  | 0,_ => []
  | n+1,row => row ++ inventory n (row.flatMap (RingClosedPairGroup.projected i))

private theorem prepend {i : Input} (row pending out : List (Arm i))
    (below : FIFO i (fun _ _ => True) (pending ++ row.flatMap (RingClosedPairGroup.projected i)) out) :
    FIFO i (fun _ _ => True) (row ++ pending) (row ++ out) := by
  induction row generalizing pending with
  | nil => simpa using below
  | cons a rest ih =>
    apply FIFO.step (List.Perm.refl _) trivial
    change FIFO i _ ((rest ++ pending) ++ RingClosedPairGroup.projected i a) (rest ++ out)
    simpa only [List.append_assoc] using ih (pending ++ RingClosedPairGroup.projected i a)
      (by simpa only [List.flatMap_cons,List.append_assoc] using below)

private theorem inventory_complete {i : Input} (n : Nat) (row : List (Arm i))
    (bound : ∀ a ∈ row, i.certified.LocalizedRerootCursorValid a ∧ i.certified.localizedRerootCursorBudget a < n) :
    FIFO i (fun _ _ => True) row (inventory n row) := by
  induction n generalizing row with
  | zero =>
    cases row with
    | nil => exact .stop
    | cons a _ => exact False.elim (Nat.not_lt_zero _ (bound a List.mem_cons_self).2)
  | succ n ih =>
    let below := row.flatMap (RingClosedPairGroup.projected i)
    have next := ih below (by
      intro c hc
      obtain ⟨a,ha,child⟩ := List.mem_flatMap.mp hc
      have child' := List.mem_of_mem_filter child
      have frame := i.certified.executableLocalizedRerootChildren_declarative a
      have lt' := i.certified.localizedRerootChild_budget_lt a c _ (bound a ha).1 frame child'
      exact ⟨i.certified.localizedRerootChild_valid a c _ frame child',
        lt_of_lt_of_le lt' (Nat.le_of_lt_succ (bound a ha).2)⟩)
    exact (by simpa [inventory,below] using prepend row [] _ (by simpa [below] using next))

open RingRetainedChemicalPreorder (Direction)
open RingFrozenWordDiagnosis (reader)

private abbrev arm {i : Input} {f : Site i} (d : Direction i f) : Arm i := ⟨d.val,some f⟩

private def visits {i : Input} {f : Site i} (d : Direction i f) :=
  inventory (i.certified.localizedRerootCursorBudget (arm d) + 1) [arm d]

private theorem visits_complete {i : Input} {f : Site i} (d : Direction i f) :
    FIFO i (fun _ _ => True) [arm d] (visits d) :=
  inventory_complete _ _ (by
    intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨(i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨d.val.property,d.property⟩,
      Nat.lt_succ_self _⟩)

/-- Compute the fixed-seed Rule 5 contribution at two actual ligand incidences.
One breadth-first inventory per arm checks that every required cell is issued
and that the two accepted populations have equal cardinality. -/
def score? {i : Input} (f : Site i) (a b : Direction i f) (rev : Bool) : Option Int := do
  let read := reader f
  let h ← upperAt read rev (arm a)
  let k ← upperAt read rev (arm b)
  guard (h ≠ k)
  let x := visits a
  let y := visits b
  guard ((x ++ y).all (fun q => (read q.occurrence).isSome))
  guard ((x.filterMap (upperAt read rev)).length = (y.filterMap (upperAt read rev)).length)
  return if h = .R then 2 else -2

/-- Every independently refined walk has issued molecular cells, and all four
walks compute the certified signed magnitude. This is the Rule 5 comparison
stage, reached only when the preceding rules tie. -/
theorem score_source {i : Input} {f : Site i} {a b : Direction i f} {rev value}
    (found : score? f a b rev = some value) {rL rR sL sR xr yr xs ys}
    (ar : FIFO i rL [arm a] xr) (br : FIFO i rR [arm b] yr)
    (as' : FIFO i sL [arm a] xs) (bs : FIFO i sR [arm b] ys) :
    (∀ q ∈ xr ++ yr ++ xs ++ ys, (reader f q.occurrence).isSome = true) ∧
    (do let r ← listSign? .R (xr.map (upperAt (reader f) rev)) (yr.map (upperAt (reader f) rev))
        let s ← listSign? .S (xs.map (upperAt (reader f) rev)) (ys.map (upperAt (reader f) rev))
        return CentresRing.PairList.combine r s) = some value := by
  unfold score? at found
  obtain ⟨h,ah,rest⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨k,bk,next⟩ := Option.bind_eq_some_iff.mp rest
  by_cases opp : h ≠ k
  · by_cases published : ((visits a ++ visits b).all fun q => (reader f q.occurrence).isSome) = true
    · by_cases size : ((visits a).filterMap (upperAt (reader f) rev)).length =
          ((visits b).filterMap (upperAt (reader f) rev)).length
      · have result : (if h = .R then (2 : Int) else -2) = value := by simpa [opp,published,size] using next
        have all := List.all_eq_true.mp published
        have left := fun q (hq : q ∈ visits a) => all q (List.mem_append_left _ hq)
        have right := fun q (hq : q ∈ visits b) => all q (List.mem_append_right _ hq)
        constructor
        · simp only [List.mem_append]
          intro q mem
          rcases mem with ((l | r) | s) | t
          · exact RingHomogeneousPairPopulation.known_all _ (visits_complete a) ar left q l
          · exact RingHomogeneousPairPopulation.known_all _ (visits_complete b) br right q r
          · exact RingHomogeneousPairPopulation.known_all _ (visits_complete a) as' left q s
          · exact RingHomogeneousPairPopulation.known_all _ (visits_complete b) bs right q t
        · rw [← result]
          exact magnitude _ rev (visits_complete a) (visits_complete b) size ah bk opp ar br as' bs
      · simp [opp,published,size] at next
    · simp [opp,published] at next
  · simp [opp] at next

end TetraStereo.Engine.RingProximalPair

namespace TetraStereo.Engine
abbrev ringProximalRule5Score? := @RingProximalPair.score?
end TetraStereo.Engine

assert_kernel_only TetraStereo.Engine.RingProximalPair.strict_prefix
assert_kernel_only TetraStereo.Engine.RingProximalPair.mirror_values_iff
assert_kernel_only TetraStereo.Engine.RingProximalPair.seed_transport
assert_kernel_only TetraStereo.Engine.RingProximalPair.population_control
assert_kernel_only TetraStereo.Engine.RingProximalPair.fixed_sign
assert_kernel_only TetraStereo.Engine.RingProximalPair.magnitude
assert_kernel_only TetraStereo.Engine.RingProximalPair.magnitude_of_unit_match
assert_kernel_only TetraStereo.Engine.RingProximalPair.score_source
assert_kernel_only TetraStereo.Engine.ringProximalRule5Score?
