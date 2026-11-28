import TetraStereo.Engine.RingFullPathReferencePolicy
import TetraStereo.Engine.RingSingleDonorComparison

/-! Recover the complete Rule 4b word when no uppercase occurrence is a
proper ancestor of another uppercase occurrence in this directed ligand. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAntichainDonors
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingSpherePopulation (AtDistance children)
open RingRetainedReferenceGroup (Hit Listing Path)
open RingFullPathPairs (FullVisit Oracle handAt likeAt stage priorities)
open RingFullPathInventory (UnmarkedBefore)
open private clean_start clean_next from TetraStereo.Engine.RingFullPathInventory
open private hit? seen bits_seen emitted compared scored from TetraStereo.Engine.RingFullPathReferencePolicy
open private reflected from TetraStereo.Engine.RingSingleDonorComparison
attribute [local instance] lexOrd

/-- This criterion only reads original hands and actual directed edges. Two
distinct occurrences of the same atom are tested at their respective cursors. -/
def Antichain {i : Input} (r : Reader i) (q : Arm i) : Prop :=
  ∀ (n : Nat) (p : Arm i), AtDistance i n q p → handAt i r false p ≠ none →
    ∀ (m : Nat) (t : Arm i), AtDistance i (m+1) p t → handAt i r false t = none

/-- Ascending sphere, descending unsigned through-4a priority path, and
descending like bit. Sorting these keys retains repeated identical hits. -/
abbrev Rank := Nat ×ₗ (Path ×ₗ Bool)ᵒᵈ

def rank (seed : RS) (h : Hit) : Rank :=
  toLex (h.path.length,OrderDual.toDual (toLex (h.path,h.hand == seed)))

def word (hits : List Hit) (rev : Bool) (seed : RS) : List Bool :=
  let keys := hits.map (fun h => rank seed (h.geometry rev))
  (keys.mergeSort (fun a b => decide (a ≤ b))).map (fun k => (ofLex (OrderDual.ofDual (ofLex k).2)).2)

private theorem snoc {i : Input} {n : Nat} {a b c : Arm i} (h : AtDistance i n a b)
    (edge : c ∈ children i b) : AtDistance i (n+1) a c := by
  induction h with
  | here => exact .descend edge .here
  | descend first _ ih => exact .descend first (ih edge)

private def Dormant {i : Input} (r : Reader i) (v : Arm i) :=
  ∀ (n : Nat) (t : Arm i), AtDistance i n v t → handAt i r false t = none

private def Layer {i : Input} (r : Reader i) (q : Arm i) (rev : Bool) (s : RS)
    (n : Nat) (v : FullVisit i) : Prop :=
  AtDistance i n q v.cursor ∧ v.path.length = n+1 ∧
    (UnmarkedBefore (likeAt i r rev s) n v ∨ Dormant r v.cursor)

private theorem next_layer {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (ac : Antichain r q) {rev : Bool} {s : RS} {n} {v w : FullVisit i} {c : Arm i}
    (prev : Layer r q rev s n v) (mem : c ∈ children i v.cursor)
    (edge : (stage i r rev []).Child (likeAt i r rev s) v c w) : Layer r q rev s (n+1) w := by
  obtain ⟨reach,size,alt⟩ := prev
  obtain ⟨k,hk,rfl⟩ := edge
  refine ⟨snoc reach mem,by simp [size],?_⟩
  rcases alt with clean|dead
  · by_cases h : handAt i r false v.cursor = none
    · have hh : likeAt i r rev s v.cursor = none := by
        rw [likeAt,reflected ready _ ((reach.root_and_budget valid).1.trans on) rev,h]
        rfl
      exact Or.inl (clean_next clean hh ⟨k,hk,rfl⟩)
    · exact Or.inr (fun m t down => ac n v.cursor reach h m t (.descend mem down))
  · exact Or.inr (fun m t down => dead (m+1) t (.descend mem down))

private theorem every_next {i : Input} {o : Oracle i} {bit : Arm i → Option Bool}
    {row next : List (FullVisit i)} {groups} {P Q : FullVisit i → Prop}
    (parents : ∀ v ∈ row, P v)
    (step : ∀ v c w, P v → c ∈ children i v.cursor → o.Child bit v c w → Q w)
    (ex : List.Forall₂ (o.Expansion bit) row groups) (perm : next.Perm groups.flatten) :
    ∀ w ∈ next, Q w := by
  intro w hw
  obtain ⟨vs,hvs,mem⟩ := List.mem_flatten.mp (perm.mem_iff.mp hw)
  obtain ⟨a,rfl⟩ := List.mem_iff_get.mp hvs
  have parent := ex.get (ex.length_eq.symm ▸ a.isLt) a.isLt
  obtain ⟨b,rfl⟩ := List.mem_iff_get.mp mem
  exact step _ _ _ (parents _ (List.get_mem _ _)) (List.get_mem _ _) (parent.get (parent.length_eq.symm ▸ b.isLt) b.isLt)

private theorem row_facts {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    {rev : Bool} {s : RS} {n : Nat} {row : List (FullVisit i)}
    (current : ∀ v ∈ row, Layer r q rev s n v)
    (ordered : (row.map FullVisit.path).Pairwise (· ≥ ·)) :
    (∀ h ∈ seen r rev row, h.path.length = n) ∧
    ((seen r rev row).map (rank s)).Pairwise (· ≤ ·) := by
  have depth (v : FullVisit i) (mem : v ∈ row) (h : Hit) (hit : hit? r rev v = some h) :
      h.path.length = n := by
    obtain ⟨hand,_,rfl⟩ := Option.map_eq_some_iff.mp hit
    have len := (current v mem).2.1
    simp [priorities,len]
  have live (v : FullVisit i) (mem : v ∈ row) (h : Hit) (hit : hit? r rev v = some h) :
      UnmarkedBefore (likeAt i r rev s) n v := by
    obtain ⟨reach,_,clean|dead⟩ := current v mem
    · exact clean
    · have hh := reflected ready v.cursor ((reach.root_and_budget valid).1.trans on) rev
      rw [dead 0 v.cursor .here] at hh
      simp [hit?,hh] at hit
  constructor
  · intro h mem
    obtain ⟨v,hv,hit⟩ := List.mem_filterMap.mp mem
    exact depth v hv h hit
  · apply List.pairwise_map.mpr
    apply List.pairwise_filterMap.mpr
    apply List.Pairwise.imp_of_mem _ (List.pairwise_map.mp ordered)
    intro a b ha hb order x hx y hy
    have cmp := compared (live a ha x hx) (live b hb y hy) order hx hy
    apply Prod.Lex.toLex_le_toLex.mpr
    refine Or.inr ⟨(depth a ha x hx).trans (depth b hb y hy).symm,?_⟩
    apply Prod.Lex.toLex_le_toLex'.mpr
    exact ⟨cmp.1,fun eq => cmp.2 eq.symm⟩

private theorem ordered_walk {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (ac : Antichain r q) {rev : Bool} {s : RS} {xs out : List (FullVisit i)}
    (walk : RingFullPathPairs.FullWalk i r rev s xs out) (n : Nat)
    (current : ∀ v ∈ xs, Layer r q rev s n v) (sorted : (xs.map FullVisit.path).Pairwise (· ≥ ·)) :
    (∀ h ∈ seen r rev out, n ≤ h.path.length) ∧ ((seen r rev out).map (rank s)).Pairwise (· ≤ ·) := by
  induction walk generalizing n with
  | stop => simp [seen]
  | @sphere v vs groups next tail ex legal _ ih =>
    have child := every_next current (fun _ _ _ hv mem edge => next_layer ready valid on ac hv mem edge) ex legal.perm
    obtain ⟨after,orderTail⟩ := ih (n+1) child legal.descending
    obtain ⟨size,orderRow⟩ := row_facts ready valid on current sorted
    simp only [seen,List.filterMap_append,List.map_append,List.mem_append,List.pairwise_append]
    refine ⟨?_,orderRow,orderTail,?_⟩
    · intro h mem
      rcases mem with near|far
      · exact (size h near).ge
      · exact Nat.le_trans (Nat.le_succ n) (after h far)
    · intro a ha b hb
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
      apply Prod.Lex.toLex_le_toLex.mpr
      exact Or.inl ((size x hx).symm ▸ after y hy)

theorem source_word {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (ac : Antichain r q) {hits : List Hit} (listed : Listing i r q hits) (rev : Bool) (s : RS)
    {bits : List Bool} (source : RingFullPathPairs.FullSource i r rev s q bits) :
    bits = word hits rev s := by
  obtain ⟨out,walk,rfl⟩ := source
  have perm := RingFullPathInventory.listing_perm listed walk
  rw [emitted] at perm
  have start (v : FullVisit i) (hv : v ∈ [RingFullPathPairs.rootVisit i r rev s q]) :
      Layer r q rev s 0 v := by
    obtain rfl := List.mem_singleton.mp hv
    exact ⟨.here,rfl,Or.inl (clean_start _ _)⟩
  have sorted := (ordered_walk ready valid on ac walk 0 start (by simp)).2
  let ks := hits.map fun h => rank s (h.geometry rev)
  let sort := ks.mergeSort fun a b => decide (a ≤ b)
  have sortOrd : sort.Pairwise (· ≤ ·) :=
    (List.pairwise_mergeSort (le := fun a b : Rank => decide (a ≤ b))
      (fun _ _ _ p t => decide_eq_true (le_trans (of_decide_eq_true p) (of_decide_eq_true t)))
      (fun a b => by simpa using le_total a b) ks).imp (fun h => of_decide_eq_true h)
  have mapped := perm.map (rank s)
  have native : ((seen r rev out).map (rank s)).Perm ks := by
    simpa only [ks,List.map_map,Function.comp_def] using mapped.symm
  have eq := List.Perm.eq_of_pairwise (fun _ _ _ _ p t => le_antisymm p t) sorted sortOrd
    (native.trans (List.mergeSort_perm ks _).symm)
  rw [bits_seen]
  have issued := congrArg (List.map (fun k : Rank => (ofLex (OrderDual.ofDual (ofLex k).2)).2)) eq
  simpa only [List.map_map,Function.comp_def,rank,word,sort,ks] using issued

theorem rule4b_word {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (ac : Antichain r q) {hits : List Hit} (listed : Listing i r q hits) (rev : Bool) (s : RS) :
    RingFullPathPairs.pairs? i r rev s q = some (word hits rev s) := by
  obtain ⟨w,hit,exactWord⟩ := RingFullPathPairs.source_exact ready rev s q valid on
  exact hit.trans (congrArg some (source_word ready valid on ac listed rev s ((exactWord w).mpr rfl)))

open private rank_of mapM_correspond from TetraStereo.Engine.RingOccurrenceStereo

theorem enumerate_eq {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {q : Arm i} {hs : List Hit} (listed : Listing i r q hs)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (n : Nat) (bound : i.certified.localizedRerootCursorBudget q < n) :
    RingRetainedReferenceGroup.enumerate i r n q = some hs := by
  induction listed generalizing n with
  | @node q v parts seen _ lookup complete rank below ih =>
    cases n with
    | zero => omega
    | succ n =>
      let fetch (c : Arm i) := do
        let k ← RingRetainedUnitPass.atArm i r c
        return (k,← RingRetainedReferenceGroup.enumerate i r n c)
      have frame := i.certified.executableLocalizedRerootChildren_declarative q
      obtain ⟨blocks,found,p⟩ := mapM_correspond (newRead := fetch) id complete (by
        rintro c mem ⟨k,hits⟩ get
        have vc := i.certified.localizedRerootChild_valid q c _ frame mem
        have oc := (i.certified.localizedRerootChildren_root_eq q c _ frame mem).trans on
        have read := rank_of (rev := false) (os := []) ready vc oc (rank c mem get)
        change RingRetainedUnitPass.atArm i r c = some k at read
        have count := ih c mem get vc oc n (by
          have lt := i.certified.localizedRerootChild_budget_lt q c _ valid frame mem; omega)
        exact ⟨(k,hits),by simp [fetch,read,count],rfl⟩)
      have eq : blocks = parts := by simpa using p
      simp only [RingRetainedReferenceGroup.enumerate,seen,Option.bind_eq_bind,Option.bind_some]
      change ((children i q).mapM fetch).bind _ = _
      change (children i q).mapM fetch = some blocks at found
      rw [found,eq]
      rfl

/-- Every valid arm of a ready reader has a successful unseeded listing,
whether or not any two listed donors are comparable in the tree. -/
theorem listing_exists {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root) :
    ∃ hs, RingRetainedReferenceGroup.hits? i r q = some hs ∧ Listing i r q hs := by
  obtain ⟨p,hp⟩ := RingGroupedStereo.arm_ready ready q valid on
  have listed := (RingGroupedStereo.arm_source hp).hits
  exact ⟨p.hits,enumerate_eq ready listed valid on _ (Nat.lt_succ_self _),listed⟩

/-- The complete seed-independent listing is available to the algorithm.
No precomputed paths or native seed words are needed as input. -/
theorem public_word {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
    Antichain r q → ∃ hs, RingRetainedReferenceGroup.hits? i r q = some hs ∧
      ∀ (rev : Bool) (s : RS), RingFullPathPairs.pairs? i r rev s q = some (word hs rev s) := by
  dsimp only
  intro ac
  have ready := RingChemicalGraphProof.ready geom f
  obtain ⟨hs,hit,listed⟩ := listing_exists ready q valid on
  exact ⟨hs,hit,fun rev s => rule4b_word ready valid on ac listed rev s⟩

end TetraStereo.Engine.RingAntichainDonors

assert_kernel_only TetraStereo.Engine.RingAntichainDonors.rule4b_word
assert_kernel_only TetraStereo.Engine.RingAntichainDonors.public_word
assert_kernel_only TetraStereo.Engine.RingAntichainDonors.enumerate_eq
