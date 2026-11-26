import TetraStereo.Engine.RingFirstChiralSphere
import TetraStereo.Engine.RingFullPathInventory
import TetraStereo.Engine.RingReferenceGroupTransport
import TetraStereo.Engine.RingReferencePrefix

/-! The highest-priority population in the molecular full-path Rule 4b reading. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFullPathReferencePolicy
open OneCenter RingFullPathPairs RingFullPathInventory RingFirstChiralSphere RingReferencePrefix
open RingRetainedReferenceGroup
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)

private def hit? {i : Input} (r : Reader i) (rev : Bool) (v : FullVisit i) : Option Hit :=
  (handAt i r rev v.cursor).map (Hit.mk (priorities v.path))

private def seen {i : Input} (r : Reader i) (rev : Bool) (vs : List (FullVisit i)) :=
  vs.filterMap (hit? r rev)

private theorem emitted {i : Input} (r : Reader i) (rev : Bool) (vs : List (FullVisit i)) :
    vs.flatMap (emission r rev) = seen r rev vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases hh : handAt i r rev v.cursor <;>
      simp [emission,seen,hit?,hh,List.flatMap_cons,ih]

private def scored (s : RS) (h : Hit) : Path × Bool := (h.path,h.hand == s)

private theorem bits_seen {i : Input} (r : Reader i) (rev : Bool) (s : RS) (vs : List (FullVisit i)) :
    vs.filterMap (fun v => likeAt i r rev s v.cursor) =
      (seen r rev vs).map (fun h => h.hand == s) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases hh : handAt i r rev v.cursor <;> simp [seen,hit?,likeAt,hh] at ih ⊢ <;> exact ih

private theorem no_hits {i : Input} {r : Reader i} {rev : Bool} {s : RS} {vs : List (FullVisit i)}
    (quiet : ∀ v ∈ vs, likeAt i r rev s v.cursor = none) : seen r rev vs = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro v hv
  cases h : handAt i r rev v.cursor with
  | none => simp [hit?,h]
  | some k => simpa [likeAt,h] using quiet v hv

private theorem compared {i : Input} {r : Reader i} {rev : Bool} {s : RS} {n : Nat}
    {v w : FullVisit i} (left : UnmarkedBefore (likeAt i r rev s) n v)
    (right : UnmarkedBefore (likeAt i r rev s) n w) (ordered : w.path ≤ v.path)
    {a b : Hit} (ha : hit? r rev v = some a) (hb : hit? r rev w = some b) :
    Descending (scored s a) (scored s b) := by
  obtain ⟨u,hu,rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨t,ht,rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨as,k,la,shape,pa⟩ := left
  obtain ⟨bs,l,lb,shape',pb⟩ := right
  rcases shape with ⟨rfl,rfl⟩ | ⟨ds,rfl,wd,wk⟩
  · rcases shape' with ⟨rfl,rfl⟩ | ⟨es,rfl,_,_⟩
    · simp [likeAt,hu,ht] at pa pb
      rw [pa,pb] at ordered
      simp [Descending,scored,priorities,pa,pb]
      cases a' : (u == s) <;> cases b' : (t == s) <;> try decide
      rw [a',b'] at ordered
      exact (False.elim ((by decide : ¬ ([stepKey [] (some true)] : Path) ≤ [stepKey [] (some false)]) ordered))
    · simp at la lb
      omega
  · rcases shape' with ⟨rfl,rfl⟩ | ⟨es,rfl,we,wl⟩
    · simp at la lb
      omega
    · have actual : v.path = stepKey [] none :: firstKey ds k (u == s) := by
        simpa [firstKey,neutral,likeAt,hu] using pa
      have other : w.path = stepKey [] none :: firstKey es l (t == s) := by
        simpa [firstKey,neutral,likeAt,ht] using pb
      have order' : firstKey es l (t == s) ≤ firstKey ds k (u == s) := by
        rw [actual,other] at ordered
        exact le_of_not_gt (fun h => (not_lt_of_ge ordered) (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl,h⟩)))
      have same : ds.length = es.length := by simpa using la.trans lb.symm
      obtain ⟨prio,bit⟩ := firstKey_descending same wd we wk wl order'
      have project (as : Path) (v : List RingRetainedChemicalTrace.Word) (bit : Bool) :
          priorities (stepKey [] none :: firstKey as v bit) = as ++ [v] := by
        simp [priorities,firstKey,neutral,List.map_map,Function.comp_def,stripBit_step]
      simp only [Descending,scored,actual,other,project]
      exact ⟨prio,fun eqn => by
        cases x : (u == s) <;> cases y : (t == s) <;> simp_all⟩

private theorem sorted_hits {i : Input} {r : Reader i} {rev : Bool} {s : RS} {n : Nat}
    {sphere : List (FullVisit i)} (desc : (sphere.map FullVisit.path).Pairwise (· ≥ ·))
    (clean : ∀ v ∈ sphere, UnmarkedBefore (likeAt i r rev s) n v) :
    ((seen r rev sphere).map (scored s)).Pairwise Descending := by
  apply List.pairwise_map.mpr
  apply List.pairwise_filterMap.mpr
  apply List.Pairwise.imp_of_mem _ (List.pairwise_map.mp desc)
  intro a b ha hb order x hx y hy
  exact compared (clean a ha) (clean b hb) order hx hy

private theorem seen_mem {i : Input} {r : Reader i} {rev : Bool} {vs : List (FullVisit i)}
    {h : Hit} (mem : h ∈ seen r rev vs) : ∃ v ∈ vs, h.path = priorities v.path := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp mem
  obtain ⟨hand,_,rfl⟩ := Option.map_eq_some_iff.mp hh
  exact ⟨v,hv,rfl⟩

private theorem visible_hit {i : Input} {r : Reader i} {rev : Bool} {s : RS} {vs : List (FullVisit i)}
    (someHit : ∃ v ∈ vs, likeAt i r rev s v.cursor ≠ none) : seen r rev vs ≠ [] := by
  obtain ⟨v,hv,chiral⟩ := someHit
  cases hh : handAt i r rev v.cursor with
  | none => exact (chiral (by simp [likeAt,hh])).elim
  | some hand =>
    have mem : Hit.mk (priorities v.path) hand ∈ seen r rev vs :=
      List.mem_filterMap.mpr ⟨v,hv,by simp [hit?,hh]⟩
    exact fun empty => by simp [empty] at mem

/-- The independently selected population supplies the initial like and unlike
runs in every complete molecular word, on either geometry and for either seed. -/
theorem word_prefix {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : FullSource i r rev s q bits) :
    ∃ suffix, bits = List.replicate ((hands hits rev).count s) true ++
      List.replicate ((hands hits rev).count s.swap) false ++ suffix := by
  obtain ⟨out,walk,rfl⟩ := source
  have all := listing_perm listed walk
  rw [emitted] at all
  rw [bits_seen]
  rcases first_emitting_sphere walk with silent | ⟨n,before,sphere,after,rfl,quiet,occupied,desc,clean,deep⟩
  · rw [no_hits silent] at all ⊢
    have empty : hits = [] := List.map_eq_nil_iff.mp all.eq_nil
    exact ⟨[],by simp [empty,hands,group]⟩
  · have splitHits : seen r rev (before ++ sphere ++ after) = seen r rev sphere ++ seen r rev after := by
      simp only [seen,List.filterMap_append]
      rw [show before.filterMap (hit? r rev) = [] from no_hits quiet,List.nil_append]
    rw [splitHits] at all ⊢
    have sorted := sorted_hits desc clean
    obtain ⟨head,tail,first⟩ := List.exists_cons_of_ne_nil (visible_hit occupied)
    rw [first] at all sorted ⊢
    have size : ∀ h ∈ head :: tail, h.path.length = n := by
      intro h hh
      obtain ⟨v,hv,eqn⟩ := seen_mem (first.symm ▸ hh)
      obtain ⟨as,k,len,_,path⟩ := clean v hv
      simp [eqn,priorities,path,len]
    have far : ∀ h ∈ seen r rev after, head.path.length < h.path.length := by
      intro h hh
      obtain ⟨v,hv,eqn⟩ := seen_mem hh
      have larger := deep v hv
      rw [size head List.mem_cons_self,eqn]
      simp only [priorities,List.length_map,List.length_drop]
      omega
    have bound : ∀ h ∈ head :: tail, h.path ≤ head.path := by
      intro h hh
      rcases List.mem_cons.mp hh with rfl | ht
      · exact le_rfl
      · exact ((List.pairwise_cons.mp sorted).1 _ (List.mem_map.mpr ⟨h,ht,rfl⟩)).1
    have pop := first_sphere_population hits rev head tail _ all
      (fun h hh => (size h hh).trans (size head List.mem_cons_self).symm) bound far s
    let row := (head :: tail).map (scored s)
    have bounded : ∀ x ∈ row, x.1 ≤ head.path := by
      intro x hx
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hx
      exact bound h hh
    have pop' : ((row.filter (fun x => x.1 == head.path)).map Prod.snd).Perm
        ((hands hits rev).map (fun h => h == s)) := by
      simpa only [row,List.filter_map,List.map_map,Function.comp_def,scored] using pop
    obtain ⟨suffix,eqn⟩ := sorted_sphere_prefix head.path row ((hands hits rev).map (fun h => h == s))
      ((seen r rev after).map (fun h => h.hand == s)) sorted bounded (by
        simpa only [Bool.beq_eq_decide_eq] using pop')
    exact ⟨suffix,by simpa only [row,List.map_append,List.map_map,Function.comp_def,scored,
      (like_counts _ s).1,(like_counts _ s).2] using eqn⟩

theorem word_empty {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    (listed : Listing i r q []) {bits : List Bool} (source : FullSource i r rev s q bits) :
    bits = [] := by
  obtain ⟨out,walk,rfl⟩ := source
  have all := listing_perm listed walk
  rw [emitted] at all
  rw [bits_seen,all.symm.eq_nil]
  rfl

theorem arm_prefix {i : Input} {r : Reader i} {rev : Bool} {q : Arm i} {hits : List Hit}
    (listed : Listing i r q hits) {w : RS → List Bool}
    (derived : ∀ s, FullSource i r rev s q (w s)) : Nonempty (Prefix (hands hits rev) w) := by
  obtain ⟨x,hx⟩ := word_prefix listed (derived .R)
  obtain ⟨y,hy⟩ := word_prefix listed (derived .S)
  exact ⟨⟨x,y,hx,hy⟩⟩

private theorem population_size (xs : List RS) : xs.count .R + xs.count .S = xs.length := by
  induction xs with
  | nil => rfl
  | cons s xs ih => cases s <;> simp_all <;> omega

private theorem unit_false {i r rev} (a : RingRetainedSeedFrames.State i r rev) :
    RingRetainedUnitPass.Reading i r false a.q a.profile.unit := by
  cases rev with
  | false => exact a.source.unit
  | true => exact RingRetainedStereoRefinement.mirror [] _ _ a.source.unit

/-- Actual retained-reference and best-of-both executables agree whenever
molecular branches tie through 4a. The structural population size is derived. -/
theorem decision_eq_hanson {i : Input} {f : Site i} {r : Reader i} {rev : Bool}
    (ready : RingGroupedStereo.Ready f r)
    (a b : RingRetainedSeedFrames.State i r rev)
    (oa : a.q.occurrence.val.root = f.val.root)
    (ob : b.q.occurrence.val.root = f.val.root)
    (tie : a.profile.unit.deep = b.profile.unit.deep) :
    RingFullPathPairs.decision? i r rev a.q b.q = RingFullPathPairs.hanson? i r rev a.q b.q := by
  obtain ⟨rs,x,hx⟩ := RingFullPathPairs.armReading_exists ready a oa
  obtain ⟨ts,y,hy⟩ := RingFullPathPairs.armReading_exists ready b ob
  have ex := (RingFullPathPairs.armReading_exact ready a oa rs x).mp hx
  have ey := (RingFullPathPairs.armReading_exact ready b ob ts y).mp hy
  have selectedA : rs = RingRetainedReferenceGroup.references a.profile.hits rev := by
    exact Option.some.inj (ex.1.symm.trans (RingOccurrenceStereo.seeds_exact ready a oa))
  have selectedB : ts = RingRetainedReferenceGroup.references b.profile.hits rev := by
    exact Option.some.inj (ey.1.symm.trans (RingOccurrenceStereo.seeds_exact ready b ob))
  rw [RingFullPathPairs.decision_of_readings ready a b oa ob hx hy,selectedA,selectedB]
  have hanson : RingFullPathPairs.hanson? i r rev a.q b.q =
      some (RingReferencePrefix.score (RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S))) := by
    simp only [RingFullPathPairs.hanson?,ex.2,ey.2,Option.bind_some,Option.bind_eq_bind,Option.pure_def]
    cases RingOccurrenceStereo.fourLists (x .R) (x .S) (y .R) (y .S) <;> rfl
  rw [hanson]
  have paths := RingReferenceGroupTransport.Listing.paths_perm a.source.hits b.source.hits
    (unit_false a) (unit_false b) tie
  by_cases empty : a.profile.hits = []
  · have emptyB : b.profile.hits = [] := by
      have e := paths.length_eq
      simpa [empty] using e.symm
    have xa : ∀ s, x s = [] := fun s => word_empty (empty ▸ a.source.hits) (hx.readings s)
    have yb : ∀ s, y s = [] := fun s => word_empty (emptyB ▸ b.source.hits) (hy.readings s)
    simp [empty,emptyB,RingRetainedReferenceGroup.references,RingRetainedReferenceGroup.hands,
      RingRetainedReferenceGroup.group,RingFullPathPairs.contest,xa,yb,
      RingOccurrenceStereo.fourLists,RingReferencePrefix.score,CertifiedLocalizedCIPInput.localizedRule4bReferencesFromPopulation]
  · have occupiedA : RingRetainedReferenceGroup.hands a.profile.hits rev ≠ [] := by
      simpa [RingRetainedReferenceGroup.hands,RingRetainedReferenceGroup.group_empty] using empty
    have occupiedB : RingRetainedReferenceGroup.hands b.profile.hits rev ≠ [] := by
      intro e
      have size := RingReferenceGroupTransport.group_length_eq paths
      have : (RingRetainedReferenceGroup.group b.profile.hits).length = 0 := by
        simpa [RingRetainedReferenceGroup.hands] using congrArg List.length e
      have : RingRetainedReferenceGroup.group a.profile.hits = [] := List.length_eq_zero_iff.mp (size.trans this)
      exact empty ((RingRetainedReferenceGroup.group_empty _).mp this)
    obtain ⟨px⟩ := arm_prefix a.source.hits hx.readings
    obtain ⟨py⟩ := arm_prefix b.source.hits hy.readings
    apply RingReferencePrefix.retained_policy_equivalence _ _ rev x y px py occupiedA occupiedB
    rw [population_size,population_size]
    simpa [RingRetainedReferenceGroup.hands] using RingReferenceGroupTransport.group_length_eq paths

/-- The molecular comparison needs only valid incident arms and their
through-4a tie. It constructs all reference populations on the ready reader. -/
theorem ready_eq_hanson {i : Input} {f : Site i} {r : Reader i} {rev : Bool} (ready : RingGroupedStereo.Ready f r)
    (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (oa : a.occurrence.val.root = f.val.root) (ob : b.occurrence.val.root = f.val.root)
    {u v} (hu : RingRetainedUnitPass.Reading i r rev a u) (hv : RingRetainedUnitPass.Reading i r rev b v)
    (tie : u.deep = v.deep) : decision? i r rev a b = hanson? i r rev a b := by
  have mk (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
      (onRoot : q.occurrence.val.root = f.val.root) : ∃ st : RingRetainedSeedFrames.State i r rev, st.q = q := by
    obtain ⟨p,hp⟩ := RingGroupedStereo.arm_ready ready q valid onRoot
    have src := RingGroupedStereo.arm_source hp
    cases rev with
    | false => exact ⟨⟨q,valid,p,src⟩,rfl⟩
    | true => exact ⟨⟨q,valid,p.reflect,src.reflect⟩,rfl⟩
  obtain ⟨sa,rfl⟩ := mk a va oa
  obtain ⟨sb,rfl⟩ := mk b vb ob
  exact decision_eq_hanson ready sa sb oa ob (by rwa [← hu.unique sa.source.unit,← hv.unique sb.source.unit])

end TetraStereo.Engine.RingFullPathReferencePolicy
assert_kernel_only TetraStereo.Engine.RingFullPathReferencePolicy.arm_prefix
assert_kernel_only TetraStereo.Engine.RingFullPathReferencePolicy.decision_eq_hanson
