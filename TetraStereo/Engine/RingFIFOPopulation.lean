import TetraStereo.Engine.RingSeededFIFOTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingFIFOPopulation
open OneCenter LocalizedChemicalRing RingActivePairs
open RingClosedPairGroup (FIFO projected upperAt)
open RingNestedActivePair (Reader)

/-- Drain exactly the current distance layer. Each queued child retains its
multiplicity, even if it occurs elsewhere in the forest. -/
private theorem drain {i : Input} {order : Arm i → List (Arm i) → Prop}
    (layer pending : List (Arm i)) {out} (w : FIFO i order (layer ++ pending) out) :
    ∃ below tail, below.Perm (layer.flatMap (projected i)) ∧
      FIFO i order (pending ++ below) tail ∧ out = layer ++ tail := by
  induction layer generalizing pending out with
  | nil => exact ⟨[],out,.refl _,by simpa using w,rfl⟩
  | cons a layer ih =>
    cases w with
    | @step _ _ row _ perm _ next =>
      change FIFO i _ ((layer ++ pending) ++ row) _ at next
      obtain ⟨below,tail,p,rest,rfl⟩ :=
        ih (pending ++ row) (by simpa only [List.append_assoc] using next)
      exact ⟨row ++ below,tail,perm.append p,by simpa only [List.append_assoc] using rest,rfl⟩

/-- A layer in a complete walk has the exact input population. Its successor
is a permutation of all the projected molecular children of this layer. -/
theorem next_layer {i : Input} {order : Arm i → List (Arm i) → Prop} {qs xs}
    (walk : FIFO i order qs xs) : ∃ cs tail, cs.Perm (qs.flatMap (projected i)) ∧
      FIFO i order cs tail ∧ xs = qs ++ tail := by
  simpa using drain qs [] (by simpa using walk : FIFO i order (qs ++ []) xs)

/-- Any two complete molecular walks from the same multiset of starting
occurrences visit exactly the same multiset of directed occurrences. The
sibling priorities on the two sides can be unrelated. -/
theorem visits_perm {i : Input} {lo ro : Arm i → List (Arm i) → Prop}
    {qs ts xs ys} (same : qs.Perm ts) (left : FIFO i lo qs xs) (right : FIFO i ro ts ys) :
    xs.Perm ys := by
  obtain ⟨n,bound⟩ : ∃ n, xs.length ≤ n := ⟨_,Nat.le_refl _⟩
  induction n generalizing qs ts xs ys with
  | zero =>
    have len : xs.length = 0 := Nat.eq_zero_of_le_zero bound
    cases xs with
    | nil =>
      cases left
      have empty := same.symm.eq_nil
      subst ts
      cases right
      exact .refl _
    | cons a xs => simp at len
  | succ n ih =>
    cases qs with
    | nil =>
      cases left
      have empty := same.symm.eq_nil
      subst ts
      cases right
      exact .refl _
    | cons q qs =>
      obtain ⟨cl,xt,pl,wl,rfl⟩ := next_layer left
      obtain ⟨cr,yt,pr,wr,rfl⟩ := next_layer right
      have lower : xt.length ≤ n := by simp only [List.length_append,List.length_cons] at bound; omega
      exact same.append (ih (pl.trans ((same.flatMap_right (projected i)).trans pr.symm)) wl wr lower)

/-- The accepted chiral population also agrees, including multiplicities
of the two hands. This holds for every frozen reader and either geometry. -/
theorem accepted_perm {i : Input} {lo ro : Arm i → List (Arm i) → Prop}
    {qs ts xs ys} (read : Reader i) (rev : Bool) (same : qs.Perm ts)
    (left : FIFO i lo qs xs) (right : FIFO i ro ts ys) :
    (xs.filterMap (upperAt read rev)).Perm (ys.filterMap (upperAt read rev)) :=
  (visits_perm same left right).filterMap _

/-- Independently chosen reference hands alter the bits but preserve the
length consumed by the source PairList comparator. -/
theorem accepted_length {i : Input} {lo ro : Arm i → List (Arm i) → Prop}
    {qs ts xs ys} (read : Reader i) (rev : Bool) (s t : RS) (same : qs.Perm ts)
    (left : FIFO i lo qs xs) (right : FIFO i ro ts ys) :
    ((xs.filterMap (upperAt read rev)).map (fun h => (h == s).toNat)).length =
      ((ys.filterMap (upperAt read rev)).map (fun h => (h == t).toNat)).length := by
  simpa only [List.length_map] using (accepted_perm read rev same left right).length_eq

open RingSeededFIFOTransport (Admissible chemicalKey)
open RingClosedPairGroup (Group word)

private theorem group_priority {i q read} (g : Group i q read) :
    chemicalKey i q g.pos = chemicalKey i q g.neg := by
  have pm := g.live.mem_iff.mpr (show g.pos ∈ [g.pos,g.neg] by simp)
  have nm := g.live.mem_iff.mpr (show g.neg ∈ [g.pos,g.neg] by simp)
  obtain ⟨t,hit,order⟩ := RingSeededFIFOTransport.chemical_priority q g.pos g.neg pm nm
  have frame := i.certified.executableLocalizedRerootChildren_declarative q
  have pc : (⟨g.pos.occurrence,some q.occurrence⟩ : Arm i) = g.pos :=
    CertifiedLocalizedCIPInput.LocalizedRerootCursor.ext _ rfl (frame.2 _ (List.mem_of_mem_filter pm)).symm
  have nc : (⟨g.neg.occurrence,some q.occurrence⟩ : Arm i) = g.neg :=
    CertifiedLocalizedCIPInput.LocalizedRerootCursor.ext _ rfl (frame.2 _ (List.mem_of_mem_filter nm)).symm
  have old := g.earlierRead
  have adj := (RingRetainedChemicalTrace.compareAt?_source old).1
  have agree : t = g.earlier := by
    simpa [RingRetainedChemicalTrace.compareAt?,adj,pc,nc,hit] using old
  apply Std.compare_eq_eq_iff_eq.mp
  rw [← order,agree,g.oneClass]

private theorem two_children {i : Input} {q a b : Arm i}
    (perm : [a,b].Perm (projected i q)) (tie : chemicalKey i q a = chemicalKey i q b)
    (ca : projected i a = []) (cb : projected i b = []) :
    FIFO i (Admissible (chemicalKey i)) [q] [q,a,b] := by
  apply FIFO.step perm (by simp [Admissible,tie])
  apply FIFO.step (row := []) (by rw [ca]) (by simp [Admissible])
  apply FIFO.step (row := []) (by rw [cb]) (by simp [Admissible])
  exact .stop

/-- In every closed mixed group the constitutional order alone admits two
complete molecular traversals with different accepted fixed-seed words.
The actual source's seed distinguishes these siblings. -/
theorem closed_group_ambiguity {i q read} (g : Group i q read) (rev : Bool) (seed : RS) :
    ∃ xs ys, FIFO i (Admissible (chemicalKey i)) [q] xs ∧
      FIFO i (Admissible (chemicalKey i)) [q] ys ∧ word read rev seed xs ≠ word read rev seed ys := by
  have tie := group_priority g
  have swapped : [g.neg,g.pos].Perm [g.pos,g.neg] := .swap ..
  refine ⟨_,_,two_children g.live.symm tie g.noLaterPos g.noLaterNeg,
    two_children (swapped.trans g.live.symm) tie.symm g.noLaterNeg g.noLaterPos,?_⟩
  cases rev <;> cases seed <;>
    simp [word,upperAt,g.rootRead,g.posRead,g.negRead,RingClosedPairGroup.chiral,
      RingClosedPairGroup.lower,RingNestedActivePair.upper,RS.swap]

end TetraStereo.Engine.RingFIFOPopulation
assert_kernel_only TetraStereo.Engine.RingFIFOPopulation.next_layer
assert_kernel_only TetraStereo.Engine.RingFIFOPopulation.visits_perm
assert_kernel_only TetraStereo.Engine.RingFIFOPopulation.accepted_perm
assert_kernel_only TetraStereo.Engine.RingFIFOPopulation.accepted_length
assert_kernel_only TetraStereo.Engine.RingFIFOPopulation.closed_group_ambiguity
