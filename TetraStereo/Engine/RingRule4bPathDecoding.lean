import TetraStereo.Engine.RingRule5SeedExchange
import TetraStereo.Engine.RingUnitTypeTransitions
import TetraStereo.Engine.RingTypedSphereDecoding

/-! Reconstruct the full sorted path list of every Rule 4b sphere from one
reference word, the root's through-4a key, and its unsigned type transitions.
The incoming reference hand is not needed by the decoder. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRule4bPathDecoding
open OneCenter RingStereoSiblingPass RingFullPathPairs RingRule5Shape RingRule5SeedExchange
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingStereoPriorityBlocks (Class paths word)
open RingTypedSphereDecoding (Shape shape decodeRow decodeRow_word)

private def slotKind (d : List Word) (n : Nat) (slot : Path) :=
  if n = 0 then d else slot.getLast?.getD []

private structure Good {i : Input} (f : Site i) (r : Reader i) (rev : Bool) (s : RS)
    (d : List Word) (n : Nat) (v : FullVisit i) : Prop where
  valid : Valid v.cursor
  onRoot : On f v.cursor
  edge : ∃ p k, p.length = n ∧ k.length = (if n = 0 then 0 else 4) ∧
    v.path = p ++ [stepKey k (likeAt i r rev s v.cursor)] ∧
    RingUnitTypeTransitions.key i r rev v.cursor = slotKind d n (p ++ [k])

private theorem good_child {i f r rev s d n v} (ready : @RingGroupedStereo.Ready i f r)
    (parent : Good f r rev s d n v) {c : Arm i} (hc : c ∈ kids i v.cursor) {u}
    (child : (stage i r rev []).Child (likeAt i r rev s) v c u) :
    Good f r rev s d (n+1) u := by
  obtain ⟨k,rank,rfl⟩ := child
  have frame := i.certified.executableLocalizedRerootChildren_declarative v.cursor
  have vc := i.certified.localizedRerootChild_valid _ _ _ frame hc
  have oc := (i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans parent.onRoot
  obtain ⟨b,hb⟩ := RingOccurrenceStereo.rank_total ready rev [] c vc oc
  change RingRetainedStereoRefinement.priority i r rev [] c = some b at hb
  obtain rfl := (stage i r rev []).unique c k b rank
    (RingRetainedStereoRefinement.source _ _ hb)
  obtain ⟨p,l,len,_,eqn,_⟩ := parent.edge
  exact ⟨vc,oc,v.path,k.deep,by simp [eqn,len],
    by simpa using (RingRetainedSeedFrames.sizes [] c k rank).2,rfl,by simp [slotKind,RingUnitTypeTransitions.key,hb]⟩

private theorem paired_member {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => contradiction
  | cons hd _ ih =>
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨_,List.mem_cons_self,hd⟩
    · obtain ⟨a,ha,h⟩ := ih hm
      exact ⟨a,List.mem_cons_of_mem _ ha,h⟩

private noncomputable def nextSlots {i : Input} (f : Site i) (r : Reader i) (rev : Bool) (d : List Word)
    (n : Nat) (path : Path) :=
  (RingUnitTypeTransitions.offspring f r rev (slotKind d n (eraseEndpoint path))).map (fun k => path ++ [k])

private theorem grow_row {i f r rev s d n row blocks next} (ready : @RingGroupedStereo.Ready i f r)
    (good : ∀ v ∈ row, Good f r rev s d n v)
    (grown : List.Forall₂ ((stage i r rev []).Expansion (likeAt i r rev s)) row blocks)
    (sorted : Legal FullVisit.path blocks.flatten next) :
    (∀ v ∈ next, Good f r rev s d (n+1) v) ∧
    (next.map (fun v => eraseEndpoint v.path)).Perm
      ((row.map FullVisit.path).flatMap (nextSlots f r rev d n)) := by
  constructor
  · intro v hv
    obtain ⟨block,hb,hu⟩ := List.mem_flatten.mp (sorted.perm.mem_iff.mp hv)
    obtain ⟨parent,hp,ex⟩ := paired_member grown hb
    obtain ⟨c,hc,child⟩ := paired_member ex hu
    exact good_child ready (good _ hp) hc child
  · apply (sorted.perm.map _).trans
    clear sorted
    induction grown with
    | nil => exact List.Perm.refl _
    | @cons v out _ _ ex _ ih =>
      have h := good v List.mem_cons_self
      obtain ⟨p,k,_,_,hv,hk⟩ := h.edge
      have shape := RingUnitTypeTransitions.expansion_slots ready rev s v h.valid h.onRoot out ex
      have eqn : RingUnitTypeTransitions.key i r rev v.cursor = slotKind d n (eraseEndpoint v.path) := by
        rw [hv,erase_snoc]; exact hk
      rw [eqn] at shape
      exact (by simpa only [List.flatten_cons,List.map_append,List.map_cons,List.flatMap_cons,nextSlots]
        using shape.append (ih (fun u hu => good u (.tail _ hu))))

private theorem slot_descending {i f r rev s d n} {row : List (FullVisit i)}
    (good : ∀ v ∈ row, Good f r rev s d n v)
    (desc : (row.map FullVisit.path).Pairwise (· ≥ ·)) :
    (row.map (fun v => eraseEndpoint v.path)).Pairwise (· ≥ ·) := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp desc).imp_of_mem
  intro a b ha hb hab
  obtain ⟨p,k,lp,lk,hp,_⟩ := (good a ha).edge
  obtain ⟨q,l,lq,ll,hq,_⟩ := (good b hb).edge
  change b.path ≤ a.path at hab
  change eraseEndpoint b.path ≤ eraseEndpoint a.path
  rw [hp,hq] at hab ⊢
  rw [erase_snoc,erase_snoc]
  exact erase_monotone (lq.trans lp.symm) (ll.trans lk.symm) hab

private def singletonClass (slot : Path) (bit : Option Bool) : Class :=
  ⟨slot.dropLast,slot.getLast?.getD [],if bit.isNone then 1 else 0,
    if bit = some true then 1 else 0,if bit = some false then 1 else 0⟩

private def slotShape (d : List Word) (n : Nat) (slot : Path) : Shape :=
  let visible := emits (slotKind d n slot)
  ⟨slot.dropLast,slot.getLast?.getD [],if visible then 0 else 1,if visible then 1 else 0⟩

private theorem shape_eq {slot : Path} {bit : Option Bool} {d n}
    (seen : bit.isSome = emits (slotKind d n slot)) :
    shape (singletonClass slot bit) = slotShape d n slot := by
  cases bit with
  | none => simp [shape,singletonClass,slotShape,← seen]
  | some b => cases b <;> simp [shape,singletonClass,slotShape,← seen]

private theorem paths_single (p : Path) (k : List Word) (bit : Option Bool) :
    (singletonClass (p ++ [k]) bit).paths = [p ++ [stepKey k bit]] := by
  rcases bit with _ | (_ | _) <;> simp [Class.paths,Class.key,singletonClass]

private theorem one_word (slot : Path) (bit : Option Bool) :
    (singletonClass slot bit).word = bit.toList := by
  rcases bit with _ | (_ | _) <;> rfl

private def classes {i : Input} (bit : Arm i → Option Bool) (row : List (FullVisit i)) :=
  row.map fun v => singletonClass (eraseEndpoint v.path) (bit v.cursor)

private theorem class_word {i : Input} (bit : Arm i → Option Bool) (row : List (FullVisit i)) :
    word (classes bit row) = row.filterMap (fun v => bit v.cursor) := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    change (singletonClass _ _).word ++ word (classes bit row) = _
    rw [one_word,ih]
    cases h : bit a.cursor <;> simp [h]

private theorem class_paths {i f r rev s d n} {row : List (FullVisit i)}
    (good : ∀ v ∈ row, Good f r rev s d n v) :
    paths (classes (likeAt i r rev s) row) = row.map FullVisit.path := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    obtain ⟨p,k,_,_,hp,_⟩ := (good a List.mem_cons_self).edge
    change (singletonClass _ _).paths ++ paths (classes _ row) = a.path :: _
    rw [ih (fun v h => good v (.tail _ h)),hp,erase_snoc,paths_single]
    rfl

private theorem class_shapes {i f r rev s d n} (ready : @RingGroupedStereo.Ready i f r)
    {row : List (FullVisit i)} (good : ∀ v ∈ row, Good f r rev s d n v) :
    (classes (likeAt i r rev s) row).map shape =
      (row.map (fun v => eraseEndpoint v.path)).map (slotShape d n) := by
  simp only [classes,List.map_map]
  apply List.map_congr_left
  intro v hv
  have g := good v hv
  obtain ⟨p,k,_,_,hp,hk⟩ := g.edge
  apply shape_eq
  have h := RingUnitTypeTransitions.emits_exact ready rev (⟨v.cursor,g.valid,g.onRoot⟩ : Carrier f) s
  change _ = emits (RingUnitTypeTransitions.key i r rev v.cursor) at h
  rwa [hp,erase_snoc,← hk]

/-- The transition table supplies only the child types with multiplicity.
An empty slot list terminates even if the fuel bound is larger than needed. -/
def replay (children : List Word → List (List Word)) (d : List Word) :
    Nat → Nat → List Path → List Bool → Option (List (List Path) × List Bool)
  | _, _, [], bits => some ([],bits)
  | 0, _, _::_, _ => none
  | fuel+1, n, a::slots, bits => do
    let (cs,rest) := decodeRow ((a::slots).map (slotShape d n)) bits
    let row := paths cs
    let next := order id (row.flatMap fun p =>
      (children (slotKind d n (eraseEndpoint p))).map (fun k => p ++ [k]))
    let (rows,tail) ← replay children d fuel (n+1) next rest
    return (row::rows,tail)

private theorem replay_walk {i f r rev s d row out rows} (ready : @RingGroupedStereo.Ready i f r)
    (walk : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s)) row out rows) :
    ∀ fuel, rows.length ≤ fuel → ∀ n, (∀ v ∈ row, Good f r rev s d n v) → ∀ tail : List Bool,
      replay (RingUnitTypeTransitions.offspring f r rev) d fuel n (row.map (fun v => eraseEndpoint v.path))
        (out.filterMap (fun v => likeAt i r rev s v.cursor) ++ tail) = some (rows,tail) := by
  induction walk with
  | stop => intro fuel _ n _ tail; cases fuel <;> rfl
  | @sphere a row blocks next rest layers grow sorted below ih =>
    intro fuel h n good tail
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      let xs := a::row
      let bit := likeAt i r rev s
      have sh := class_shapes ready good
      have ps := class_paths good
      obtain ⟨gn,perm⟩ := grow_row ready good grow sorted
      have sc := slot_descending gn sorted.descending
      have legal : Legal id ((xs.map FullVisit.path).flatMap (nextSlots f r rev d n))
          (next.map (fun v => eraseEndpoint v.path)) := ⟨perm,by simpa using sc⟩
      have ns : order id ((xs.map FullVisit.path).flatMap (nextSlots f r rev d n)) =
          next.map (fun v => eraseEndpoint v.path) := by
        simpa using ((legal_iff ..).mp legal).2.symm
      change (do
        let (cs,rest') := decodeRow ((xs.map (fun v : FullVisit i => eraseEndpoint v.path)).map (slotShape d n))
          (((xs ++ rest).filterMap (fun v : FullVisit i => bit v.cursor)) ++ tail)
        let (rows',tail') ← replay _ d fuel (n+1)
          (order id ((paths cs).flatMap (nextSlots f r rev d n))) rest'
        pure (paths cs :: rows',tail')) = _
      rw [List.filterMap_append,List.append_assoc,← sh,← class_word bit xs,decodeRow_word]
      dsimp only
      rw [ps,ns]
      rw [ih fuel (by simpa using h) (n+1) gn tail]
      rfl

private theorem root_good {i f r rev s d} {a : Arm i} (va : Valid a) (oa : On f a)
    (rootType : RingUnitTypeTransitions.key i r rev a = d) :
    Good f r rev s d 0 (Oracle.root (likeAt i r rev s) a) :=
  ⟨va,oa,[],[],rfl,rfl,rfl,rootType⟩

/-- The same decoder works for either reference and any successful walk on
a ready frozen reader. It stops at the last nonempty sphere. -/
theorem reconstruct {i f r rev s} (ready : @RingGroupedStereo.Ready i f r)
    {a : Arm i} (va : Valid a) (oa : On f a) {out rows}
    (walk : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out rows) (fuel : Nat) (bound : rows.length ≤ fuel) :
    replay (RingUnitTypeTransitions.offspring f r rev) (RingUnitTypeTransitions.key i r rev a)
      fuel 0 [[[]]] (out.filterMap (fun v => likeAt i r rev s v.cursor)) = some (rows,[]) := by
  simpa [Oracle.root,eraseEndpoint,stripBit_step] using
    replay_walk ready walk fuel bound 0 (fun v hv => List.mem_singleton.mp hv ▸ root_good va oa rfl) []

private theorem forget {α κ : Type} [LinearOrder κ] {key : α → κ} {expansion : α → List α → Prop}
    {row out rows} (walk : Layers key expansion row out rows) : FullTrace key expansion row out := by
  induction walk with
  | stop => exact .stop
  | sphere grown sorted _ ih => exact .sphere grown sorted ih

private theorem layers_word {i : Input} {r : Reader i} {rev s a out rows}
    (walk : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out rows) :
    out.filterMap (fun v => likeAt i r rev s v.cursor) = rows.flatten.filterMap bitOf := by
  rw [flatten_layers walk]
  exact Oracle.walk_bits (forget walk)

theorem layers_iff {i f r rev s t} (ready : @RingGroupedStereo.Ready i f r) {a b : Arm i}
    (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {out rows out' rows'}
    (left : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out rows)
    (right : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev t))
      [Oracle.root (likeAt i r rev t) b] out' rows') :
    rows = rows' ↔ out.filterMap (fun v => likeAt i r rev s v.cursor) =
        out'.filterMap (fun v => likeAt i r rev t v.cursor) := by
  constructor
  · rintro rfl
    rw [layers_word left,layers_word right]
  · intro words
    let fuel := max rows.length rows'.length
    have h := reconstruct ready va oa left fuel (Nat.le_max_left ..)
    rw [tie,words,reconstruct ready vb ob right fuel (Nat.le_max_right ..)] at h
    exact (congrArg Prod.fst (Option.some.inj h)).symm

end TetraStereo.Engine.RingRule4bPathDecoding
assert_kernel_only TetraStereo.Engine.RingRule4bPathDecoding.reconstruct
assert_kernel_only TetraStereo.Engine.RingRule4bPathDecoding.layers_iff
