import TetraStereo.Engine.RingFullPathInventory
import TetraStereo.Engine.RingReferencePrefix
import TetraStereo.Engine.RingFullPathRule5

/-! Every legal complete Rule 4b word retains the entire independent chiral
listing, including repeated occurrences and hits beyond the reference group. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPairWordPopulation
open OneCenter RingFullPathPairs RingFullPathInventory RingRetainedReferenceGroup
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)

private theorem emitted_bits {i : Input} (r : Reader i) (rev : Bool) (s : RS)
    (out : List (FullVisit i)) :
    (out.flatMap (emission r rev)).map (fun h => h.hand == s) =
      out.filterMap (fun v => likeAt i r rev s v.cursor) := by
  induction out with
  | nil => rfl
  | cons v vs ih =>
    cases hh : handAt i r rev v.cursor <;>
      simp [emission,likeAt,hh,List.flatMap_cons,ih]

/-- All emitted bits, with multiplicity, agree with scoring every independent
listing hit against the chosen seed. No sorting choice or readiness hypothesis
is needed beyond the supplied legal complete trace. -/
theorem word_perm {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : FullSource i r rev s q bits) :
    bits.Perm ((hits.map (fun h => h.geometry rev)).map (fun h => h.hand == s)) := by
  obtain ⟨out,walk,rfl⟩ := source
  have p := (listing_perm listed walk).map (fun h => h.hand == s)
  rw [emitted_bits] at p
  exact p.symm

/-- The length counts all chiral sites of the listing, not only its highest
priority reference population. -/
theorem word_length {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : FullSource i r rev s q bits) : bits.length = hits.length := by
  simpa using (word_perm listed source).length_eq

/-- Each Boolean multiplicity is fixed independently of legal sphere sorting. -/
theorem word_count {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : FullSource i r rev s q bits) (b : Bool) :
    bits.count b = ((hits.map (fun h => h.geometry rev)).map (fun h => h.hand == s)).count b :=
  (word_perm listed source).count_eq b

/-- True and false occurrences count respectively all like and unlike hands
of the independent listing on the selected geometry. -/
theorem word_hand_counts {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : FullSource i r rev s q bits) :
    let population := (hits.map (fun h => h.geometry rev)).map Hit.hand
    bits.count true = population.count s ∧ bits.count false = population.count s.swap := by
  intro population
  have counts := RingReferencePrefix.like_counts population s
  constructor
  · rw [word_count listed source true]
    simpa only [population,List.map_map,Function.comp_def] using counts.1
  · rw [word_count listed source false]
    simpa only [population,List.map_map,Function.comp_def] using counts.2

private noncomputable def chosen {i : Input} (r : Reader i) (q : Arm i) : List Hit :=
  open Classical in if h : ∃ xs, Listing i r q xs then h.choose else []

private theorem chosen_eq {i : Input} {r : Reader i} {q : Arm i} {xs : List Hit}
    (h : Listing i r q xs) : chosen r q = xs := by
  have ex : ∃ ys, Listing i r q ys := ⟨_,h⟩
  rw [chosen,dif_pos ex]
  exact ex.choose_spec.unique h

private def score (rev : Bool) (s : RS) (hs : List Hit) : List Bool :=
  hs.map (fun h => (h.geometry rev).hand == s)

private theorem child_scores {i : Input} {r : Reader i} {rev : Bool} {s : RS}
    {o : Oracle i} {p : FullVisit i}
    {f : Arm i → Option (RingStereoSiblingPass.Branch × List Hit)}
    {cs : List (Arm i)} {parts vs}
    (reads : cs.mapM f = some parts)
    (lists : ∀ c ∈ cs, ∀ {k hs}, f c = some (k,hs) → Listing i r c hs)
    (edges : List.Forall₂ (o.Child (likeAt i r rev s) p) cs vs) :
    score rev s (parts.flatMap fun (k,hs) => hs.map (fun h => {h with path := k.deep :: h.path})) =
      vs.flatMap (fun v => score rev s (chosen r v.cursor)) ∧
    ∀ v ∈ vs, ∃ hs, Listing i r v.cursor hs := by
  induction edges generalizing parts with
  | nil => cases reads; exact ⟨rfl,by simp⟩
  | @cons c w cs ws edge tail ih =>
    rw [List.mapM_cons] at reads
    obtain ⟨⟨k,hs⟩,hk,rest⟩ := Option.bind_eq_some_iff.mp reads
    obtain ⟨ps,hps,last⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := Option.some.inj last
    obtain ⟨l,hl,rfl⟩ := edge
    have sub := lists c List.mem_cons_self hk
    obtain ⟨eqn,valid⟩ := ih hps (fun a ha => lists a (List.mem_cons_of_mem _ ha))
    constructor
    · simpa [score,List.flatMap_cons,List.map_append,List.map_map,Function.comp_def,
        Hit.geometry,chosen_eq sub] using eqn
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨_,sub⟩
      · exact valid v hv

/-- Changing the priority oracle changes order, but preserves the population
of Boolean emissions in every complete legal molecular walk. -/
theorem oracle_word_perm {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {o : Oracle i} {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : o.Source (likeAt i r rev s) q bits) :
    bits.Perm ((hits.map (fun h => h.geometry rev)).map (fun h => h.hand == s)) := by
  obtain ⟨out,walk,rfl⟩ := source
  let emit := fun v : FullVisit i => (likeAt i r rev s v.cursor).toList
  let below := fun v : FullVisit i => score rev s (chosen r v.cursor)
  let valid := fun v : FullVisit i => ∃ hs, Listing i r v.cursor hs
  have expand (p : FullVisit i) (vs : List (FullVisit i)) (hp : valid p)
      (ex : o.Expansion (likeAt i r rev s) p vs) :
      (below p).Perm (emit p ++ vs.flatMap below) ∧ ∀ v ∈ vs, valid v := by
    obtain ⟨xs,lst⟩ := hp
    change (score rev s (chosen r p.cursor)).Perm _ ∧ _
    rw [chosen_eq lst]
    cases lst with
    | @node q labs parts seen phys f found ranks child =>
      obtain ⟨eqn,all⟩ := child_scores found child ex
      refine ⟨?_,all⟩
      have root : score rev s (joinHits labs []) = emit p := by
        simp only [score,joinHits,List.flatMap_nil,List.append_nil]
        change (((RingNestedActivePair.upper (labs.map Prod.fst)).map (Hit.mk [])).toList.map
          (fun h => (h.geometry rev).hand == s)) = (likeAt i r rev s p.cursor).toList
        rcases labs with _ | ⟨(_|_),(_|_)⟩ <;> cases rev <;>
          simp_all [score,likeAt,handAt,RingNestedActivePair.consistent,
            RingNestedActivePair.upper,Hit.geometry]
      simpa only [score,joinHits,List.map_append,List.flatMap_nil,List.append_nil] using
        (show (score rev s (joinHits labs []) ++ score rev s
          (parts.flatMap fun (k,hs) => hs.map (fun h => {h with path := k.deep :: h.path}))).Perm
          (emit p ++ vs.flatMap below) from by rw [root,eqn])
  have result := conservation emit below (fun p vs hp ex => (expand p vs hp ex).1)
    (fun p vs hp ex => (expand p vs hp ex).2) walk
    (fun p hp => by obtain rfl := List.mem_singleton.mp hp; exact ⟨_,listed⟩)
  have flatten (vs : List (FullVisit i)) : vs.flatMap emit =
      vs.filterMap (fun v => likeAt i r rev s v.cursor) := by
    induction vs with
    | nil => rfl
    | cons v vs ih => cases h : likeAt i r rev s v.cursor <;> simp [emit,h,ih]
  rw [flatten] at result
  simpa [below,Oracle.root,chosen_eq listed,score,List.map_map,Function.comp_def] using result.symm

theorem oracle_word_length {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {o : Oracle i} {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : o.Source (likeAt i r rev s) q bits) : bits.length = hits.length := by
  simpa using (oracle_word_perm listed source).length_eq

theorem rule5_length {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {hits : List Hit} (listed : Listing i r q hits) {bits : List Bool}
    (source : RingFullPathRule5.Word i r rev s q bits) : bits.length = hits.length :=
  oracle_word_length listed source

end TetraStereo.Engine.RingPairWordPopulation
assert_kernel_only TetraStereo.Engine.RingPairWordPopulation.word_perm
assert_kernel_only TetraStereo.Engine.RingPairWordPopulation.word_length
assert_kernel_only TetraStereo.Engine.RingPairWordPopulation.word_count
assert_kernel_only TetraStereo.Engine.RingPairWordPopulation.word_hand_counts
assert_kernel_only TetraStereo.Engine.RingPairWordPopulation.oracle_word_perm
assert_kernel_only TetraStereo.Engine.RingPairWordPopulation.oracle_word_length
assert_kernel_only TetraStereo.Engine.RingPairWordPopulation.rule5_length
