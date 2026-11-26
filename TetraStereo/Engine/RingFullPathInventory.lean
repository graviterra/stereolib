import TetraStereo.Engine.RingFullPathPairs

/-! Multiplicity of chiral occurrences in the global sphere traversal. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFullPathInventory
open OneCenter RingFullPathPairs RingRetainedReferenceGroup
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader upper consistent)

private theorem row_balance {α β : Type} {E : α → List α → Prop} {P : α → Prop}
    (emit below : α → List β)
    (step : ∀ v vs, P v → E v vs → (below v).Perm (emit v ++ vs.flatMap below))
    {row : List α} {blocks : List (List α)} (expansions : List.Forall₂ E row blocks)
    (valid : ∀ v ∈ row, P v) :
    (row.flatMap below).Perm (row.flatMap emit ++ blocks.flatten.flatMap below) := by
  induction expansions with
  | nil => exact .nil
  | @cons v vs row blocks head tail ih =>
    have one := step v vs (valid v List.mem_cons_self) head
    have more := ih (fun x hx => valid x (List.mem_cons_of_mem _ hx))
    have swap : ((vs.flatMap below) ++ row.flatMap emit).Perm
        (row.flatMap emit ++ vs.flatMap below) := List.perm_append_comm
    simpa only [List.flatMap_cons,List.flatten_cons,List.flatMap_append,List.append_assoc] using
      (one.append more).trans (by
        simpa only [List.append_assoc] using
          (swap.append_right (blocks.flatten.flatMap below)).append_left (emit v))

/-- Sorting a sphere preserves every occurrence and its multiplicity. The
frontier carries the contributions from the subtrees still to be visited. -/
theorem conservation {α β κ : Type} [LinearOrder κ] {key : α → κ} {E : α → List α → Prop}
    {P : α → Prop} (emit below : α → List β)
    (step : ∀ v vs, P v → E v vs → (below v).Perm (emit v ++ vs.flatMap below))
    (child : ∀ v vs, P v → E v vs → ∀ w ∈ vs, P w)
    {row out : List α} (trace : FullTrace key E row out) (valid : ∀ v ∈ row, P v) :
    (row.flatMap below).Perm (out.flatMap emit) := by
  induction trace with
  | stop => exact .nil
  | @sphere v row blocks next rest ex sort _ ih =>
    have flat : ∀ b ∈ blocks.flatten, P b := by
      intro b hb
      obtain ⟨block,hm,hin⟩ := List.mem_flatten.mp hb
      obtain ⟨idx,rfl⟩ := List.mem_iff_get.mp hm
      have bound : idx.val < (v::row).length := ex.length_eq.symm ▸ idx.isLt
      exact child _ _ (valid _ (List.get_mem _ _)) (ex.get bound idx.isLt) b hin
    have restEq := ih (fun x hx => flat x (sort.perm.mem_iff.mp hx))
    rw [List.flatMap_append]
    exact (row_balance emit below step ex valid).trans
      (((sort.perm.symm.flatMap_right below).trans restEq).append_left _)

private noncomputable def listing {i : Input} (r : Reader i) (q : Arm i) : List Hit :=
  open Classical in if h : ∃ xs, Listing i r q xs then h.choose else []

private theorem listing_eq {i : Input} {r : Reader i} {q : Arm i} {xs : List Hit}
    (h : Listing i r q xs) : listing r q = xs := by
  have ex : ∃ ys, Listing i r q ys := ⟨_,h⟩
  rw [listing,dif_pos ex]
  exact ex.choose_spec.unique h

private def tagged (p : Path) (rev : Bool) (h : Hit) : Hit :=
  ⟨p ++ h.path, (h.geometry rev).hand⟩

def emission {i : Input} (r : Reader i) (rev : Bool) (v : FullVisit i) : List Hit :=
  ((handAt i r rev v.cursor).map fun h => Hit.mk (priorities v.path) h).toList

private def ValidVisit {i : Input} (r : Reader i) (v : FullVisit i) : Prop :=
  v.path ≠ [] ∧ ∃ xs, Listing i r v.cursor xs

private noncomputable def inventory {i : Input} (r : Reader i) (rev : Bool) (v : FullVisit i) :=
  (listing r v.cursor).map (tagged (priorities v.path) rev)

private theorem root_hit {i : Input} {r : Reader i} {p : FullVisit i} {v}
    (seen : r p.cursor.occurrence = some v) (phys : v.all consistent = true) (rev : Bool) :
    (((upper (v.map Prod.fst)).map (Hit.mk [])).toList.map (tagged (priorities p.path) rev)) =
      emission r rev p := by
  rcases v with _ | ⟨(_|_),(_|_)⟩ <;> cases rev <;>
    simp_all [emission,handAt,consistent,upper,tagged,Hit.geometry]

private theorem child_path {i : Input} {p : FullVisit i} (ne : p.path ≠ [])
    (k : RingStereoSiblingPass.Branch) (b : Option Bool) :
    priorities (p.path ++ [stepKey k.deep b]) = priorities p.path ++ [k.deep] := by
  cases h : p.path with
  | nil => exact (ne h).elim
  | cons a as => simp [priorities,stripBit_step]

private theorem children_balance {i : Input} {r : Reader i} {rev : Bool} {bit : Arm i → Option Bool}
    {p : FullVisit i} (ne : p.path ≠ [])
    {f : Arm i → Option (RingStereoSiblingPass.Branch × List Hit)} {children : List (Arm i)}
    {parts visits} (reads : children.mapM f = some parts)
    (ranks : ∀ c ∈ children, ∀ {k hs}, f c = some (k,hs) → RingRetainedUnitPass.Reading i r false c k)
    (lists : ∀ c ∈ children, ∀ {k hs}, f c = some (k,hs) → Listing i r c hs)
    (edges : List.Forall₂ ((stage i r rev []).Child bit p) children visits) :
    ((parts.flatMap fun (k,hs) => hs.map (fun h => {h with path := k.deep :: h.path})).map
      (tagged (priorities p.path) rev)) = visits.flatMap (inventory r rev) ∧
      ∀ v ∈ visits, ValidVisit r v := by
  induction edges generalizing parts with
  | nil => cases reads; exact ⟨rfl,by simp⟩
  | @cons c w cs ws edge tail ih =>
    rw [List.mapM_cons] at reads
    obtain ⟨⟨k,hs⟩,hk,rest⟩ := Option.bind_eq_some_iff.mp reads
    obtain ⟨ps,hps,last⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := Option.some.inj last
    obtain ⟨l,hl,rfl⟩ := edge
    have rk := ranks c List.mem_cons_self hk
    have mirrored : RingRetainedUnitPass.Reading i r rev c k := by
      cases rev
      · exact rk
      · exact RingRetainedStereoRefinement.mirror [] c k rk
    obtain rfl := mirrored.unique hl
    have sub := lists c List.mem_cons_self hk
    obtain ⟨restEq,valid⟩ := ih hps
      (fun a ha => ranks a (List.mem_cons_of_mem _ ha))
      (fun a ha => lists a (List.mem_cons_of_mem _ ha))
    constructor
    · simp only [List.flatMap_cons,List.map_append,restEq,inventory,listing_eq sub,List.map_map]
      congr 1
      apply List.map_congr_left
      intro h _
      simp [tagged,Hit.geometry,child_path ne]
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | h
      · exact ⟨by simp,_,sub⟩
      · exact valid v h

/-- A legal complete molecular sphere walk emits precisely the ranked chiral
occurrences of the independent recursive listing, including repeated equal paths. -/
theorem listing_perm {i : Input} {r : Reader i} {rev : Bool} {seed : RS} {q : Arm i}
    {xs : List Hit} (listed : Listing i r q xs) {out}
    (walk : FullWalk i r rev seed [rootVisit i r rev seed q] out) :
    (xs.map (fun h => h.geometry rev)).Perm (out.flatMap (emission r rev)) := by
  have expand (p : FullVisit i) (vs : List (FullVisit i)) (hp : ValidVisit r p)
      (ex : (stage i r rev []).Expansion (likeAt i r rev seed) p vs) :
      (inventory r rev p).Perm (emission r rev p ++ vs.flatMap (inventory r rev)) ∧
      ∀ c ∈ vs, ValidVisit r c := by
    obtain ⟨ne,xs,lst⟩ := hp
    rw [inventory,listing_eq lst]
    cases lst with
    | node seen phys f found ranks below =>
      obtain ⟨eqn,all⟩ := children_balance ne found ranks below ex
      refine ⟨?_,all⟩
      unfold joinHits
      rw [List.map_append]
      rw [← eqn,← root_hit seen phys.1 rev]
      exact List.Perm.refl _
  have result := conservation (emission r rev) (inventory r rev)
    (fun p vs hp ex => (expand p vs hp ex).1) (fun p vs hp ex => (expand p vs hp ex).2)
    walk (fun p hp => by obtain rfl := List.mem_singleton.mp hp; exact ⟨by simp [rootVisit,Oracle.root],_,listed⟩)
  simpa [inventory,rootVisit,Oracle.root,priorities,listing_eq listed,tagged,Hit.geometry] using result


/-- Prior to the first chiral sphere all visited ancestors have a neutral bit.
The initial empty priority belongs to the root step of the full-path walk. -/
def UnmarkedBefore {i : Input} (bit : Arm i → Option Bool) (depth : Nat) (v : FullVisit i) : Prop :=
  ∃ (ancestors : Path) (last : List RingRetainedChemicalTrace.Word),
    ancestors.length = depth ∧
    (ancestors = [] ∧ last = [] ∨
      ∃ ds, ancestors = [] :: ds ∧ (∀ d ∈ ds, d.length = 4) ∧ last.length = 4) ∧
    v.path = ancestors.map (fun d => stepKey d none) ++ [stepKey last (bit v.cursor)]

private theorem clean_start {i : Input} (bit : Arm i → Option Bool) (q : Arm i) :
    UnmarkedBefore bit 0 (Oracle.root bit q) := ⟨[],[],rfl,Or.inl ⟨rfl,rfl⟩,rfl⟩

private theorem clean_next {i : Input} {r : Reader i} {rev : Bool} {bit : Arm i → Option Bool}
    {n} {v : FullVisit i} (clean : UnmarkedBefore bit n v) (silent : bit v.cursor = none)
    {c : Arm i} {w} (edge : (stage i r rev []).Child bit v c w) : UnmarkedBefore bit (n+1) w := by
  obtain ⟨ancestors,last,len,shape,path⟩ := clean
  obtain ⟨k,rank,rfl⟩ := edge
  refine ⟨ancestors ++ [last],k.deep,by simp [len],Or.inr ?_,?_⟩
  · have width : k.deep.length = 4 := (RingRetainedSeedFrames.sizes [] c k rank).2
    rcases shape with ⟨rfl,rfl⟩ | ⟨ds,rfl,ws,wl⟩
    · exact ⟨[],rfl,by simp,width⟩
    · exact ⟨ds ++ [last],rfl,fun d hd => by
        rcases List.mem_append.mp hd with h | h
        · exact ws d h
        · obtain rfl := List.mem_singleton.mp h
          exact wl,width⟩
  · simp [path,silent,List.append_assoc]

private theorem every_child {i : Input} {o : Oracle i} {bit : Arm i → Option Bool}
    {row next : List (FullVisit i)} {blocks} {P Q : FullVisit i → Prop}
    (parents : ∀ v ∈ row, P v)
    (step : ∀ v c w, P v → o.Child bit v c w → Q w)
    (ex : List.Forall₂ (o.Expansion bit) row blocks)
    (p : next.Perm blocks.flatten) : ∀ w ∈ next, Q w := by
  intro w hw
  obtain ⟨vs,hvs,mem⟩ := List.mem_flatten.mp (p.mem_iff.mp hw)
  obtain ⟨a,rfl⟩ := List.mem_iff_get.mp hvs
  have parent := ex.get (ex.length_eq.symm ▸ a.isLt) a.isLt
  obtain ⟨b,rfl⟩ := List.mem_iff_get.mp mem
  exact step _ _ _ (parents _ (List.get_mem _ _)) (parent.get (parent.length_eq.symm ▸ b.isLt) b.isLt)

/-- Either the entire molecular walk is silent, or its first emitting sphere
is globally sorted, every ancestor bit there is neutral, and all later visits
are strictly deeper. This includes the case of a chiral ligand root. -/
theorem first_emitting_sphere {i : Input} {r : Reader i} {rev : Bool} {s : RS} {q : Arm i}
    {out} (walk : FullWalk i r rev s [rootVisit i r rev s q] out) :
    let bit := likeAt i r rev s
    (∀ v ∈ out, bit v.cursor = none) ∨
    ∃ (n : Nat) (before sphere after : List (FullVisit i)),
      out = before ++ sphere ++ after ∧ (∀ v ∈ before, bit v.cursor = none) ∧
      (∃ v ∈ sphere, bit v.cursor ≠ none) ∧
      (sphere.map FullVisit.path).Pairwise (· ≥ ·) ∧ (∀ v ∈ sphere, UnmarkedBefore bit n v) ∧
      ∀ v ∈ after, n+1 < v.path.length := by
  let bit := likeAt i r rev s
  let o := stage i r rev []
  suffices ∀ {row out : List (FullVisit i)} (t : o.Walk bit row out) (n : Nat),
      (row.map FullVisit.path).Pairwise (· ≥ ·) → (∀ v ∈ row, UnmarkedBefore bit n v) →
      (∀ v ∈ out, bit v.cursor = none) ∨
      ∃ (m : Nat) (before sphere after : List (FullVisit i)),
        out = before ++ sphere ++ after ∧ (∀ v ∈ before, bit v.cursor = none) ∧
        (∃ v ∈ sphere, bit v.cursor ≠ none) ∧
        (sphere.map FullVisit.path).Pairwise (· ≥ ·) ∧ (∀ v ∈ sphere, UnmarkedBefore bit m v) ∧
        ∀ v ∈ after, m+1 < v.path.length by
    apply this walk 0 (by simp)
    intro v hv
    obtain rfl := List.mem_singleton.mp hv
    exact clean_start _ _
  intro row out t
  induction t with
  | stop => intro _ _ _; exact Or.inl (by simp)
  | @sphere x row blocks next rest ex sort tail ih =>
    intro n descending clean
    by_cases silent : ∀ v ∈ x::row, bit v.cursor = none
    · have clean' := every_child (P := fun v => UnmarkedBefore bit n v ∧ bit v.cursor = none)
          (fun v hv => ⟨clean v hv,silent v hv⟩)
          (fun _ _ _ h edge => clean_next h.1 h.2 edge) ex sort.perm
      rcases ih (n+1) sort.descending clean' with empty | ⟨m,beginning,sphere,after,eqn,quiet,hits,ds,cl,late⟩
      · exact Or.inl (fun v h => (List.mem_append.mp h).elim (silent v) (empty v))
      · exact Or.inr ⟨m,(x::row) ++ beginning,sphere,after,by simp [eqn,List.append_assoc],
          fun v h => (List.mem_append.mp h).elim (silent v) (quiet v),hits,ds,cl,late⟩
    · push_neg at silent
      refine Or.inr ⟨n,[],x::row,rest,rfl,by simp,silent,descending,clean,?_⟩
      have length (v) (hv : v ∈ x::row) : v.path.length = n+1 := by
        obtain ⟨anc,k,size,_,path⟩ := clean v hv
        simp [path,size]
      have deep := every_child (P := fun v => v.path.length = n+1) (Q := fun w => n+1 < w.path.length)
        length (fun v _ w h edge => by
          obtain ⟨k,_,rfl⟩ := edge
          show n+1 < (v.path ++ [stepKey k.deep _]).length
          simp [h]) ex sort.perm
      apply FullTrace.all (P := fun v : FullVisit i => n+1 < v.path.length) _ tail deep
      intro v vs hv grown w hw
      obtain ⟨idx,rfl⟩ := List.mem_iff_get.mp hw
      have edge := grown.get (grown.length_eq.symm ▸ idx.isLt) idx.isLt
      obtain ⟨k,_,eqn⟩ := edge
      rw [eqn]
      simpa using Nat.lt_succ_of_lt hv

end TetraStereo.Engine.RingFullPathInventory
assert_kernel_only TetraStereo.Engine.RingFullPathInventory.listing_perm
assert_kernel_only TetraStereo.Engine.RingFullPathInventory.first_emitting_sphere
