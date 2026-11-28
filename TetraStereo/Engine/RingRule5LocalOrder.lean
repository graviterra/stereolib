import TetraStereo.Engine.RingRule5Shape

/-! Rule 5 paths can be compared using local sibling priority numbers at each
bond. Equal through-4c parents have the same child priority distribution.
The ordinal is computed again in each actual parent, including repeated children. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRule5LocalOrder
open OneCenter RingFullPathPairs RingPathRankTransport
open RingRule5Shape (kids Valid On key)
open RingActivePairs (Arm Site)
open LocalizedChemicalRing (Input)
open RingNestedActivePair (Reader)
open private cons_transport chars_lt chars_eq no_lt_nil nil_lt from TetraStereo.Engine.RingPathRankTransport
open private child_facts from TetraStereo.Engine.RingFullPathPairs

private def edge {i : Input} (r : Reader i) (rev : Bool) (s : RS) (p c : Arm i) : Edge :=
  let rank := key i r rev c
  ⟨rank,losses ((kids i p).map (key i r rev)) rank,likeAt i r rev s c⟩

inductive Descent {i : Input} (r : Reader i) (rev : Bool) (s : RS) :
    Arm i → List Edge → Arm i → Prop
  | stop {q} : Descent r rev s q [] q
  | step {q c rest e} (member : c ∈ kids i q) (below : Descent r rev s c rest e) :
      Descent r rev s q (edge r rev s q c :: rest) e

private theorem snoc {i r rev s q es p} (walk : @Descent i r rev s q es p)
    {c : Arm i} (hc : c ∈ kids i p) :
    Descent r rev s q (es ++ [edge r rev s p c]) c := by
  induction walk with
  | stop => exact .step hc .stop
  | step h _ ih => exact .step h (ih hc)

private theorem width {i : Input} {r : Reader i} {f : Site i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (c : Arm i) (v : Valid c) (o : On f c) : (key i r rev c).length = 5 := by
  obtain ⟨k,found⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] c v o
  change RingRetainedStereoRefinement.priority i r rev [.lowercase] c = some k at found
  have rank := RingRetainedStereoRefinement.source [.lowercase] c found
  have len := (RingRetainedSeedFrames.sizes [.lowercase] c k rank).2
  simpa [key,found] using len

private theorem transport {i : Input} {r : Reader i} {f : Site i} (ready : RingGroupedStereo.Ready f r)
    {rev s t q x as'} (a : @Descent i r rev s q as' x) :
    ∀ {p y bs}, Descent r rev t p bs y → Valid q → Valid p → On f q → On f p →
      key i r rev q = key i r rev p →
      (absolute as' < absolute bs ↔ Below (ordinals as') (ordinals bs)) ∧
      (absolute as' = absolute bs ↔ ordinals as' = ordinals bs) := by
  induction a with
  | stop =>
    intro p y bs b _ _ _ _ _
    cases b with
    | stop => exact ⟨iff_of_false (lt_irrefl _) Below.not_nil,iff_of_true rfl rfl⟩
    | step => exact ⟨iff_of_true (List.Lex.nil) (.short),iff_of_false (fun h => List.cons_ne_nil _ _ h.symm) (fun h => List.cons_ne_nil _ _ h.symm)⟩
  | @step q c rest e hc sub ih =>
    intro p y bs b vq vp oq op tie
    cases b with
    | stop => exact ⟨iff_of_false no_lt_nil Below.not_nil,iff_of_false (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)⟩
    | @step _ d _ _ hd tail =>
      obtain ⟨vc,oc,_⟩ := child_facts vq oq hc
      obtain ⟨vd,od,_⟩ := child_facts vp op hd
      have same := losses_perm (RingRule5Shape.same_children ready rev q p vq vp oq op tie).1
      exact cons_transport ((width ready rev c vc oc).trans (width ready rev d vd od).symm)
        (losses_lt_iff same (List.mem_map_of_mem hd))
        (losses_eq_iff same (List.mem_map_of_mem hc) (List.mem_map_of_mem hd))
        (fun eq => ih tail vc vd oc od eq)

private abbrev Reached {i : Input} (r : Reader i) (rev : Bool) (s : RS) (q : Arm i) :=
  (stage i r rev [.lowercase]).Reach (likeAt i r rev s) q

private theorem descent_of_reach {i : Input} {r : Reader i} {f : Site i}
    (ready : RingGroupedStereo.Ready f r) {rev s q x}
    (vq : Valid q) (oq : On f q) (hit : Reached r rev s q x) :
    Valid x.cursor ∧ On f x.cursor ∧ ∃ es, Descent r rev s q es x.cursor ∧
      x.path = absolute (rootEdge i r rev s q :: es) := by
  induction hit with
  | root => exact ⟨vq,oq,[],.stop,rfl⟩
  | @child p c k _ hc rank ih =>
    obtain ⟨vp,op,es,walk,eq⟩ := ih
    obtain ⟨vc,oc,_⟩ := child_facts vp op hc
    obtain ⟨l,get⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] c vc oc
    change RingRetainedStereoRefinement.priority i r rev [.lowercase] c = some l at get
    obtain rfl := (stage i r rev [.lowercase]).unique c k l rank
      (RingRetainedStereoRefinement.source [.lowercase] c get)
    refine ⟨vc,oc,es ++ [edge r rev s p.cursor c],snoc walk hc,?_⟩
    change p.path ++ [_] = _
    rw [eq]
    simp [absolute,Edge.absolute,edge,key,get]

/-- For every two actual visits at the same distance below through-4c-tied
roots on a ready store, the author's ascending local priority-character
comparison gives exactly the native descending order and exactly its ties. -/
theorem reached_characters {i : Input} {r : Reader i} {f : Site i} (ready : RingGroupedStereo.Ready f r)
    {rev s t q p x y} (vq : Valid q) (vp : Valid p) (oq : On f q) (op : On f p)
    (tie : key i r rev q = key i r rev p) (a : Reached r rev s q x) (b : Reached r rev t p y)
    (sphere : x.path.length = y.path.length) :
    ∃ ea eb, Descent r rev s q ea x.cursor ∧ Descent r rev t p eb y.cursor ∧
      x.path = absolute (rootEdge i r rev s q :: ea) ∧
      y.path = absolute (rootEdge i r rev t p :: eb) ∧
      let cx := (rootEdge i r rev s q :: ea).map Edge.charCode
      let cy := (rootEdge i r rev t p :: eb).map Edge.charCode
      (x.path < y.path ↔ cy < cx) ∧ (x.path = y.path ↔ cx = cy) := by
  obtain ⟨_,_,ea,wa,pa⟩ := descent_of_reach ready vq oq a
  obtain ⟨_,_,eb,wb,pb⟩ := descent_of_reach ready vp op b
  have tails := transport ready wa wb vq vp oq op tie
  have roots := cons_transport (d := []) (e := []) (la := 0) (lb := 0)
    (m := likeAt i r rev s q) (n := likeAt i r rev t p) rfl
    (iff_of_false (lt_irrefl _) (lt_irrefl _)) (iff_of_true rfl rfl) (fun _ => tails)
  refine ⟨ea,eb,wa,wb,pa,pb,?_⟩
  dsimp only
  rw [pa,pb] at sphere ⊢
  have len : (rootEdge i r rev s q :: ea).length = (rootEdge i r rev t p :: eb).length := by
    simpa only [absolute,List.length_map] using sphere
  exact ⟨roots.1.trans (chars_lt len),roots.2.trans (chars_eq ..).symm⟩

end TetraStereo.Engine.RingRule5LocalOrder
assert_kernel_only TetraStereo.Engine.RingRule5LocalOrder.reached_characters
