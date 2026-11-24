import TetraStereo.Engine.RingRule5SeedExchange
import TetraStereo.Engine.RingFullPathEligibility

/-! # Reconstructing molecular Rule 5 readings from either reference -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingRule5Tie
open OneCenter RingStereoSiblingPass RingFullPathPairs RingRule5Shape RingRule5SeedExchange
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)

private def slotKind (d : List Word) (n : Nat) (slot : Path) :=
  if n = 0 then d else slot.getLast?.getD []

private structure Good {i : Input} (f : Site i) (r : Reader i) (rev : Bool) (s : RS)
    (d : List Word) (n : Nat) (v : FullVisit i) : Prop where
  valid : Valid v.cursor
  onRoot : On f v.cursor
  edge : ∃ p k, p.length = n ∧ k.length = (if n = 0 then 0 else 5) ∧
    v.path = p ++ [stepKey k (likeAt i r rev s v.cursor)] ∧
    key i r rev v.cursor = slotKind d n (p ++ [k])

private theorem good_child {i f r rev s d n v} (ready : @RingGroupedStereo.Ready i f r)
    (parent : Good f r rev s d n v) {c : Arm i} (hc : c ∈ kids i v.cursor) {u}
    (child : (stage i r rev [.lowercase]).Child (likeAt i r rev s) v c u) :
    Good f r rev s d (n+1) u := by
  obtain ⟨k,rank,rfl⟩ := child
  have frame := i.certified.executableLocalizedRerootChildren_declarative v.cursor
  have vc := i.certified.localizedRerootChild_valid _ _ _ frame hc
  have oc := (i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans parent.onRoot
  obtain ⟨b,hb⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] c vc oc
  change RingRetainedStereoRefinement.priority i r rev [.lowercase] c = some b at hb
  obtain rfl := (stage i r rev [.lowercase]).unique c k b rank
    (RingRetainedStereoRefinement.source _ _ hb)
  obtain ⟨p,l,len,_,eqn,_⟩ := parent.edge
  exact ⟨vc,oc,v.path,k.deep,by simp [eqn,len],
    by simpa using (RingRetainedSeedFrames.sizes [.lowercase] c k rank).2,rfl,by simp [slotKind,key,hb]⟩

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
  (offspring f r rev (slotKind d n (eraseEndpoint path))).map (fun k => path ++ [k])

private theorem grow_row {i f r rev s d n row blocks next} (ready : @RingGroupedStereo.Ready i f r)
    (good : ∀ v ∈ row, Good f r rev s d n v)
    (grown : List.Forall₂ ((stage i r rev [.lowercase]).Expansion (likeAt i r rev s)) row blocks)
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
      have shape := expansion_slots ready rev s v h.valid h.onRoot out ex
      have eqn : key i r rev v.cursor = slotKind d n (eraseEndpoint v.path) := by
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

private theorem slot_faithful {i f r rev s d n v} (ready : @RingGroupedStereo.Ready i f r)
    (g : Good f r rev s d n v) :
    (likeAt i r rev s v.cursor).isSome = emits (slotKind d n (eraseEndpoint v.path)) := by
  obtain ⟨p,k,_,_,hv,hk⟩ := g.edge
  have h := emits_exact ready rev (⟨v.cursor,g.valid,g.onRoot⟩ : Carrier f) s
  change _ = emits (key i r rev v.cursor) at h
  rwa [hv,erase_snoc,← hk]

private theorem same_path {i f r rev s d n a b}
    (ha : @Good i f r rev s d n a) (hb : Good f r rev s d n b)
    (slot : eraseEndpoint a.path = eraseEndpoint b.path)
    (bit : likeAt i r rev s a.cursor = likeAt i r rev s b.cursor) : a.path = b.path := by
  obtain ⟨p,k,_,_,hp,_⟩ := ha.edge
  obtain ⟨q,l,_,_,hq,_⟩ := hb.edge
  rw [hp,hq,erase_snoc,erase_snoc] at slot
  have kl : k = l := by simpa using congrArg List.getLast? slot
  subst l
  have pq : p = q := List.append_cancel_right slot
  simp only [hp,hq,bit,pq]

private theorem consume {i f r rev s d n} (ready : @RingGroupedStereo.Ready i f r)
    (xs ys : List (FullVisit i)) (gx : ∀ v ∈ xs, Good f r rev s d n v)
    (gy : ∀ v ∈ ys, Good f r rev s d n v)
    (slots : xs.map (fun v => eraseEndpoint v.path) = ys.map (fun v => eraseEndpoint v.path))
    (u v : List Bool)
    (w : xs.filterMap (fun a => likeAt i r rev s a.cursor) ++ u =
      ys.filterMap (fun a => likeAt i r rev s a.cursor) ++ v) :
    xs.map FullVisit.path = ys.map FullVisit.path ∧ u = v := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at slots
    | cons b ys =>
      obtain ⟨slot,slots⟩ := List.cons.inj slots
      have ha := gx a List.mem_cons_self
      have hb := gy b List.mem_cons_self
      have presence := (slot_faithful ready ha).trans ((congrArg (fun p => emits (slotKind d n p)) slot).trans (slot_faithful ready hb).symm)
      have split : likeAt i r rev s a.cursor = likeAt i r rev s b.cursor ∧
          xs.filterMap (fun a => likeAt i r rev s a.cursor) ++ u =
          ys.filterMap (fun b => likeAt i r rev s b.cursor) ++ v := by
        cases ea : likeAt i r rev s a.cursor <;> cases eb : likeAt i r rev s b.cursor <;>
          simp_all only [List.filterMap_cons,Option.isSome_none,Option.isSome_some,
            Bool.false_eq_true,Bool.true_eq_false,List.cons_append,List.cons.injEq,and_true]
      obtain ⟨keys,eqn⟩ := ih ys (fun x hx => gx x (.tail _ hx)) (fun x hx => gy x (.tail _ hx)) slots split.2
      exact ⟨congrArg₂ List.cons (same_path ha hb slot split.1) keys,eqn⟩

private theorem recover {i f r rev s d row out rows} (ready : @RingGroupedStereo.Ready i f r)
    (t : Layers FullVisit.path ((stage i r rev [.lowercase]).Expansion (likeAt i r rev s)) row out rows) :
    ∀ {row' out' rows'}, Layers FullVisit.path ((stage i r rev [.lowercase]).Expansion (likeAt i r rev s))
      row' out' rows' → ∀ n, (∀ v ∈ row, Good f r rev s d n v) → (∀ v ∈ row', Good f r rev s d n v) →
      row.map (fun v => eraseEndpoint v.path) = row'.map (fun v => eraseEndpoint v.path) →
      out.filterMap (fun v => likeAt i r rev s v.cursor) = out'.filterMap (fun v => likeAt i r rev s v.cursor) →
      rows = rows' := by
  induction t with
  | stop =>
    intro row' out' rows' t' n ga gb slots w
    cases t' with
    | stop => rfl
    | sphere => simp at slots
  | @sphere a row blocks next rest layers grow sorted tail ih =>
    intro row' out' rows' t' n ga gb slots w
    cases t' with
    | stop => simp at slots
    | @sphere b row' blocks' next' rest' layers' grow' sorted' tail' =>
      rw [List.filterMap_append,List.filterMap_append] at w
      obtain ⟨head,more⟩ := consume ready _ _ ga gb slots _ _ w
      obtain ⟨gn,p⟩ := grow_row ready ga grow sorted
      obtain ⟨gn',p'⟩ := grow_row ready gb grow' sorted'
      rw [head] at p
      have ns := List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
        (slot_descending gn sorted.descending) (slot_descending gn' sorted'.descending) (p.trans p'.symm)
      exact congrArg₂ List.cons head (ih tail' (n+1) gn gn' ns more)

private theorem root_good {i f r rev s d} {q : Arm i} (v : Valid q) (o : On f q)
    (h : key i r rev q = d) : Good f r rev s d 0 (Oracle.root (likeAt i r rev s) q) :=
  ⟨v,o,[],[],rfl,rfl,rfl,h⟩

/-- Two legal walks with the same through-4c root key and the same emitted
word have the same opposite-reference word, even across parent boundaries. -/
theorem opposite_words {i f r rev s} (ready : @RingGroupedStereo.Ready i f r) {a b : Arm i}
    (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) (tie : key i r rev a = key i r rev b)
    {w u v : List Bool} (a₁ : RingFullPathRule5.Word i r rev s a w)
    (b₁ : RingFullPathRule5.Word i r rev s b w) (a₂ : RingFullPathRule5.Word i r rev s.swap a u)
    (b₂ : RingFullPathRule5.Word i r rev s.swap b v) : u = v := by
  obtain ⟨x,tx,hx⟩ := a₁
  obtain ⟨y,ty,hy⟩ := b₁
  obtain ⟨z,tz,rfl⟩ := a₂
  obtain ⟨t,tt,rfl⟩ := b₂
  obtain ⟨rx,lx⟩ := record tx
  obtain ⟨ry,ly⟩ := record ty
  obtain ⟨rz,lz⟩ := record tz
  obtain ⟨rt,lt⟩ := record tt
  have eqn : rx = ry := recover ready lx ly 0
    (fun _ h => List.mem_singleton.mp h ▸ root_good va oa rfl)
    (fun _ h => List.mem_singleton.mp h ▸ root_good vb ob tie.symm)
    (by simp [Oracle.root,eraseEndpoint,stripBit_step]) (hx.symm.trans hy)
  have a' := molecular_exchange _ r rev s a lx lz
  have b' := molecular_exchange _ r rev s b ly lt
  rw [eqn,← b'] at a'
  rw [Oracle.walk_bits tz,Oracle.walk_bits tt,← flatten_layers lz,← flatten_layers lt,a']

/-- Equality of the executable fixed-reference words is independent of
the chosen reference at every through-4c tie on a ready original root. -/
theorem tie_iff {i f r rev} (ready : @RingGroupedStereo.Ready i f r) {a b : Arm i}
    (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) (tie : key i r rev a = key i r rev b) :
    RingFullPathRule5.word? i r rev .R a = RingFullPathRule5.word? i r rev .R b ↔
    RingFullPathRule5.word? i r rev .S a = RingFullPathRule5.word? i r rev .S b := by
  have pass (s : RS) :
      RingFullPathRule5.word? i r rev s a = RingFullPathRule5.word? i r rev s b →
      RingFullPathRule5.word? i r rev s.swap a = RingFullPathRule5.word? i r rev s.swap b := by
    obtain ⟨x,ax,ex⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) s a va oa
    obtain ⟨y,by',ey⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) s b vb ob
    obtain ⟨u,au,eu⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) s.swap a va oa
    obtain ⟨v,bv,ev⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) s.swap b vb ob
    rw [ax,by',au,bv]
    rintro h
    obtain rfl := Option.some.inj h
    exact congrArg some (opposite_words ready va vb oa ob tie ((ex _).mpr rfl) ((ey _).mpr rfl)
      ((eu _).mpr rfl) ((ev _).mpr rfl))
  exact ⟨pass .R,pass .S⟩

/-- On the published frozen state the only original/mirror score pairs are
a joint tie, the same unit sign, or opposite doubled signs. -/
theorem view_scores {i : Input} (f : Site i) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    let r := RingActiveDistanceSchedule.frozen view f
    key i r false a = key i r false b →
    (RingFullPathRule5.score? i r false a b,RingFullPathRule5.score? i r true a b) ∈
      ([(some 0,some 0),(some 1,some 1),(some (-1),some (-1)),(some 2,some (-2)),(some (-2),some 2)] :
        List (Option Int × Option Int)) := by
  intro r tie
  obtain ⟨x,y,l,h,sc,mir,_⟩ := RingFullPathRule5.view_casing f view ready a b va vb oa ob
  have eqn := tie_iff ready va vb oa ob tie
  rw [l .R,h .R,l .S,h .S] at eqn
  simp only [Option.some.injEq] at eqn
  have z : compare (x .R) (y .R) = .eq ↔ compare (x .S) (y .S) = .eq := by
    simpa only [Std.compare_eq_eq_iff_eq] using eqn
  change (RingFullPathRule5.score? i r false a b,RingFullPathRule5.score? i r true a b) ∈ _
  rw [sc,mir]
  generalize compare (x .R) (y .R) = cr at z ⊢
  generalize compare (x .S) (y .S) = cs at z ⊢
  cases cr <;> cases cs <;> first | decide | simp at z

theorem frozen_scores {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    key i r false a = key i r false b →
    (RingFullPathRule5.score? i r false a b,RingFullPathRule5.score? i r true a b) ∈
      ([(some 0,some 0),(some 1,some 1),(some (-1),some (-1)),(some 2,some (-2)),(some (-2),some 2)] :
        List (Option Int × Option Int)) :=
  view_scores f _ (RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f) a b va vb oa ob

open RingFullPathEligibility (Key Reads)
open RingNestedActivePair (Frame)
open RingActivePairReport (Slot)

theorem reading_key {i f r rev} (ready : @RingGroupedStereo.Ready i f r) {q : Arm i} {k : Key}
    (valid : Valid q) (on : On f q) (read : Reads i r rev q k) :
    key i r rev q = k.throughFourA ++ [k.fourC] := by
  obtain ⟨u,l,_,_,_,hu,hl,_,_,_,rfl⟩ := read
  obtain ⟨b,hb⟩ := RingOccurrenceStereo.rank_total ready rev [.lowercase] q valid on
  change RingRetainedStereoRefinement.priority i r rev [.lowercase] q = some b at hb
  have eqn := RingRetainedStereoRefinement.unique [.lowercase] q b l
    (RingRetainedStereoRefinement.source _ _ hb) hl
  subst b
  simp only [key,hb,Option.map_some,Option.getD_some]
  cases hl with
  | node prior _ _ _ _ _ _ =>
    obtain rfl := RingRetainedStereoRefinement.unique [] q _ _ prior hu
    rfl

theorem reflected_read {i : Input} (f : Site i) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) (rev : Bool) {q : Arm i} {k : Key} {w : List Bool} :
    let r := RingActiveDistanceSchedule.frozen view f
    Reads i r rev q k → RingFullPathRule5.Word i r rev .S q w →
    Reads i r (!rev) q {k with fixedR := w} := by
  intro r read hs
  obtain ⟨u,l,a,b,t,hu,hl,ha,hb,_,rfl⟩ := read
  exact ⟨u,l,b,a,w,RingRetainedStereoRefinement.mirror [] _ _ hu,
    RingRetainedStereoRefinement.mirror [.lowercase] _ _ hl,
    RingFullPathRule5.view_mirror_source f view ready rev .S q b [] hb,
    RingFullPathRule5.view_mirror_source f view ready rev .R q a [] ha,
    RingFullPathRule5.view_mirror_source f view ready rev .S q w [.lowercase] hs,by simp [max_comm]⟩

private theorem mirror_tied {i : Input} (f : Site i) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) (rev : Bool) {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    {k m n : Key} :
    let r := RingActiveDistanceSchedule.frozen view f
    Reads i r rev a k → Reads i r rev b k → Reads i r (!rev) a m → Reads i r (!rev) b n → m = n := by
  intro r ha hb hm hn
  have tie := (reading_key ready va oa ha).trans (reading_key ready vb ob hb).symm
  obtain ⟨x,_,ex⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) .S a va oa
  obtain ⟨y,_,ey⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) .S b vb ob
  have fixed {q : Arm i} (h : Reads i r rev q k) : RingFullPathRule5.Word i r rev .R q k.fixedR := by
    obtain ⟨_,_,_,_,_,_,_,_,_,h,rfl⟩ := h
    exact h
  have same := opposite_words (s := .R) ready va vb oa ob tie (fixed ha) (fixed hb)
    ((ex _).mpr rfl) ((ey _).mpr rfl)
  subst y
  have unique {q : Arm i} {u v : Key} (valid : Valid q) (on : On f q) (left : Reads i r (!rev) q u)
      (right : Reads i r (!rev) q v) : u = v := by
    obtain ⟨z,_,all⟩ := RingFullPathEligibility.key_exact ready (!rev) q valid on
    exact ((all u).mp left).trans ((all v).mp right).symm
  exact (unique va oa hm (reflected_read f view ready rev ha ((ex _).mpr rfl))).trans
    (unique vb ob hn (reflected_read f view ready rev hb ((ey _).mpr rfl))).symm

theorem view_partition {i : Input} {f : Site i} (fr : Frame i f) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f))
    (x y : Slot → Key) (hx : ∀ s, Reads i (RingActiveDistanceSchedule.frozen view f) false (RingGroupedCentre.cursor fr s) (x s))
      (hy : ∀ s, Reads i (RingActiveDistanceSchedule.frozen view f) true (RingGroupedCentre.cursor fr s) (y s)) (j k : Slot) :
      x j = x k ↔ y j = y k := by
  constructor
  · intro same
    exact mirror_tied f view ready false (RingGroupedCentre.valid fr j) (RingGroupedCentre.valid fr k)
      (fr.direction j).property.1 (fr.direction k).property.1 (hx j) (same ▸ hx k) (hy j) (hy k)
  · intro same
    exact mirror_tied f view ready true (RingGroupedCentre.valid fr j) (RingGroupedCentre.valid fr k)
      (fr.direction j).property.1 (fr.direction k).property.1 (hy j) (same ▸ hy k) (hx j) (hx k)

/-- Reflection preserves the complete ordinary tie partition and hence the
exact ordered list of eligible molecular slots on the frozen frame. -/
theorem frozen_promotions {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    RingFullPathEligibility.candidates? fr r false = RingFullPathEligibility.candidates? fr r true ∧
      ∀ x y : Slot → Key, (∀ s, Reads i r false (RingGroupedCentre.cursor fr s) (x s)) →
        (∀ s, Reads i r true (RingGroupedCentre.cursor fr s) (y s)) →
        ∀ j k, x j = x k ↔ y j = y k := by
  intro r
  have part := view_partition fr (RingGroupedPublication.state i)
    (RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f)
  refine ⟨?_,part⟩
  obtain ⟨x,hx,cx,_⟩ := RingFullPathEligibility.frozen_candidates geom fr false
  obtain ⟨y,hy,cy,_⟩ := RingFullPathEligibility.frozen_candidates geom fr true
  rw [cx,cy]
  unfold RingFullPathEligibility.candidates
  have eqn : RingFullPathEligibility.tiedSlots x = RingFullPathEligibility.tiedSlots y := by
    unfold RingFullPathEligibility.tiedSlots
    congr 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,part x y hx hy]
  rw [eqn]

end TetraStereo.Engine.RingRule5Tie
assert_kernel_only TetraStereo.Engine.RingRule5Tie.opposite_words
assert_kernel_only TetraStereo.Engine.RingRule5Tie.frozen_scores
assert_kernel_only TetraStereo.Engine.RingRule5Tie.frozen_promotions
