import TetraStereo.Engine.RingActivePairs

set_option autoImplicit false

namespace TetraStereo.Engine.RingActivePairs
open OneCenter CertifiedLocalizedCIPInput RingRetainedConstitution
open LocalizedChemicalRing (Input)
open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPhysicalSense (inputGeometry)

private theorem eachMap {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (got : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => obtain rfl : [] = ys := Option.some.inj got; exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at got
    cases h : f x <;> cases t : xs.mapM f <;> simp [h,t] at got
    subst ys
    exact .cons h (ih t)

private theorem origin {α β : Type} {rel : α → β → Prop} {xs : List α} {ys : List β}
    (r : List.Forall₂ rel xs ys) {y : β} (mem : y ∈ ys) : ∃ x ∈ xs, rel x y := by
  induction r with
  | nil => simp at mem
  | cons head tail ih =>
    rcases List.mem_cons.mp mem with rfl | rest
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨x,hx,v⟩ := ih rest
      exact ⟨x,List.mem_cons_of_mem _ hx,v⟩

/-- A legitimate sibling order uses every exposed outward edge exactly once and decreases
strictly in the observed real atomic number. This premise is independent of later seeds
and of the sorting function used in the collector. -/
structure AtomicOrder (i : Input) (q : Arm i) (qs : List (Arm i)) : Prop where
  complete : qs.Perm (i.certified.executableLocalizedRerootChildren q)
  present : ∀ child ∈ qs, (z? i child).isSome = true
  descending : qs.Pairwise fun a b => (z? i b).getD 0 < (z? i a).getD 0

theorem AtomicOrder.unique {i q a b} (x : AtomicOrder i q a) (y : AtomicOrder i q b) : a = b :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h k => False.elim (Nat.lt_asymm h k))
    x.descending y.descending (x.complete.trans y.complete.symm)

private theorem mapped_parents {i : Input} {xs : List (Arm i)} {ys : List (Edge i)}
    (actual : List.Forall₂ (fun a e => (z? i a).map (a,·) = some e) xs ys) :
    ys.map Prod.fst = xs := by
  induction actual with
  | nil => rfl
  | cons h _ ih =>
    obtain ⟨z,_,rfl⟩ := Option.map_eq_some_iff.mp h
    simp [ih]

theorem children_source {i q edges} (got : children? i q = some edges) :
    AtomicOrder i q (edges.map Prod.fst) := by
  unfold children? at got
  cases seen : (i.certified.executableLocalizedRerootChildren q).mapM (fun a => (z? i a).map (a,·)) with
  | none => simp [seen] at got
  | some unsorted =>
    let sorted := unsorted.mergeSort fun (a b : Edge i) => a.2 ≥ b.2
    by_cases valid : strictEdges i sorted
    · have es : sorted = edges := by simpa [seen,← show sorted = unsorted.mergeSort (fun (a b : Edge i) => a.2 ≥ b.2) from rfl,valid] using got
      subst edges
      have reading := eachMap seen
      have fst := mapped_parents reading
      have perm : sorted.Perm unsorted := List.mergeSort_perm ..
      have value (e : Edge i) (mem : e ∈ sorted) : z? i e.1 = some e.2 := by
        obtain ⟨a,_,h⟩ := origin reading (perm.mem_iff.mp mem)
        obtain ⟨n,actual,rfl⟩ := Option.map_eq_some_iff.mp h
        exact actual
      refine ⟨fst ▸ perm.map Prod.fst,?_,?_⟩
      · intro c hc
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc
        simp [value e he]
      · apply List.pairwise_map.mpr
        exact (show sorted.Pairwise (fun a b => b.2 < a.2) from valid).imp_of_mem
          (fun {a b} ha hb lt => by simpa [value a ha,value b hb] using lt)
    · simp [seen,show ¬ strictEdges i (unsorted.mergeSort fun (a b : Edge i) => a.2 ≥ b.2) from valid] at got

/-- Declarative observation for one visited node, with the original address and all
outgoing children. The only chemical data in this relation are the actual atomic number,
the frozen molecular publication and the legal atomic priorities. -/
structure AtNode (i : Input) (focus : Site i) (q : Arm i) (data : NodeRead × List (Arm i)) : Prop where
  address : data.1.address = q.occurrence.val.address
  number : z? i q = some data.1.atomicNumber
  auxiliary : active? i focus q.occurrence = some data.1.hand
  degree : data.1.children = data.2.length
  order : AtomicOrder i q data.2

inductive Observes (i : Input) (focus : Site i) : List (Arm i) → List (List NodeRead) → Prop where
  | empty : Observes i focus [] []
  | layer {q qs data tail}
      (nodes : List.Forall₂ (AtNode i focus) (q :: qs) data)
      (below : Observes i focus (data.flatMap Prod.snd) tail) :
      Observes i focus (q :: qs) (data.map Prod.fst :: tail)

theorem ordered_source (i : Input) (focus : Site i) : ∀ n qs out,
    orderedLevels? i focus n qs = some out → Observes i focus qs out
  | 0,[],_,got | _+1,[],_,got => by obtain rfl := Option.some.inj got; exact .empty
  | 0,_::_,_,got => by contradiction
  | n+1,q::qs,out,got => by
    let visit (a : Arm i) : Option (NodeRead × List (Arm i)) := do
      let es ← children? i a
      let z ← z? i a
      let hand ← active? i focus a.occurrence
      return (⟨a.occurrence.val.address,z,es.length,hand⟩,es.map Prod.fst)
    change ((q::qs).mapM visit >>= fun data =>
      (orderedLevels? i focus n (data.flatMap Prod.snd) >>= fun rest => some (data.map Prod.fst :: rest))) = some out at got
    obtain ⟨data,h,tail⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨rest,hr,r⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj r
    apply Observes.layer _ (ordered_source i focus n _ _ hr)
    apply (eachMap h).imp
    intro x y read
    dsimp [visit] at read
    obtain ⟨es,he,r⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨z,hz,r⟩ := Option.bind_eq_some_iff.mp r
    obtain ⟨hand,hh,r⟩ := Option.bind_eq_some_iff.mp r
    obtain rfl := Option.some.inj r
    exact ⟨rfl,hz,hh,(List.length_map ..).symm,children_source he⟩

theorem AtNode.positive {i f q data} (w : AtNode i f q data) {s}
    (recorded : data.1.hand = some s) :
    q.occurrence.val.root = f.val.root ∧ f.val.address.length < data.1.address.length ∧
      q.occurrence.val.node.current? ≠ some f.val.root ∧
      ∃ prep : RingRetainedAuxiliary.Prepared i q.occurrence,
        readback? (inputGeometry i.certified) prep.ids = some s ∧
        readback? (mirror (inputGeometry i.certified)) prep.ids = some s.swap := by
  have pub := (active_positive i f q.occurrence s).mp (w.auxiliary.trans (congrArg some recorded))
  obtain ⟨t,raw,rev,_⟩ := RingRetainedAuxiliary.read_source i _ s (RingRetainedAuxiliary.publication_iff.mp pub.2.2.2)
  exact ⟨pub.1,w.address ▸ pub.2.1,pub.2.2.1,t,raw,rev⟩

end TetraStereo.Engine.RingActivePairs

assert_kernel_only TetraStereo.Engine.RingActivePairs.AtomicOrder.unique
assert_kernel_only TetraStereo.Engine.RingActivePairs.ordered_source
assert_kernel_only TetraStereo.Engine.RingActivePairs.AtNode.positive
