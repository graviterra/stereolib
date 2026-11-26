import TetraStereo.Engine.RingFullPathEligibility
import TetraStereo.Engine.RingRawRenumbering

/-! Full-path priority words under atom renumbering. A complete sphere is sorted across
parents, so tied visits may move. The expansion permutation preserves every sorted key row. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathKeyTransport
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open RingFullPathPairs (FullTrace FullVisit Oracle stage likeAt handAt stepKey bitOf pick pick_eq
  flatten_pick)
open RingGeometryExchange (Carrier Frozen)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (arm carrier)
open RingActiveDistanceSchedule (View Visible distance frozen)
open RingFullPathEligibility (Reads key? key_exact)

/-! ## List facts -/

private theorem forall2_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {a : α} (ha : a ∈ xs) : ∃ b, b ∈ ys ∧ R a b := by
  induction h with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp ha with rfl | rest
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨b,mem,hb⟩ := ih rest
      exact ⟨b,List.mem_cons_of_mem _ mem,hb⟩

private theorem forall2_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x, x ∈ xs ∧ R x y := by
  induction h with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp hy with rfl | rest
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨a,mem,ha⟩ := ih rest
      exact ⟨a,List.mem_cons_of_mem _ mem,ha⟩

private noncomputable def chosen {α β : Type} (R : α → β → Prop) (a : α) : Option β :=
  open Classical in if h : ∃ y, R a y then some h.choose else none

private theorem chosen_eq {α β : Type} {R : α → β → Prop}
    (fn : ∀ a x y, R a x → R a y → x = y) {a : α} {y : β} (h : R a y) : chosen R a = some y := by
  have hx : ∃ z, R a z := ⟨y,h⟩
  unfold chosen
  rw [dif_pos hx]
  exact congrArg some (fn _ _ _ hx.choose_spec h)

private theorem forall2_chosen {α β : Type} {R : α → β → Prop}
    (fn : ∀ a x y, R a x → R a y → x = y) {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : xs.filterMap (chosen R) = ys := by
  induction h with
  | nil => rfl
  | cons head _ ih => rw [List.filterMap_cons_some (chosen_eq fn head),ih]

private theorem forall2_image {α β α' β' : Type} {R : α → β → Prop} {ψ : α' → Option β'}
    {e : α → α'} {g : β → β'} {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (each : ∀ a ∈ xs, ∀ b, R a b → ψ (e a) = some (g b)) :
    (xs.map e).filterMap ψ = ys.map g := by
  induction h with
  | nil => rfl
  | cons head _ ih =>
    rw [List.map_cons,List.map_cons,List.filterMap_cons_some (each _ List.mem_cons_self _ head),
      ih (fun c hc => each c (List.mem_cons_of_mem _ hc))]

/-- Two functional row relations over inputs matched up to permutation give
outputs matched up to permutation. -/
private theorem forall2_perm {α β α' β' : Type} {R : α → β → Prop} {R' : α' → β' → Prop}
    {e : α → α'} {g : β → β'} (fn : ∀ a x y, R' a x → R' a y → x = y)
    {xs : List α} {ys : List β} {xs' : List α'} {ys' : List β'}
    (h : List.Forall₂ R xs ys) (h' : List.Forall₂ R' xs' ys') (p : (xs.map e).Perm xs')
    (compat : ∀ a ∈ xs, ∀ b b', R a b → R' (e a) b' → g b = b') : (ys.map g).Perm ys' := by
  have left : (xs.map e).filterMap (chosen R') = ys.map g := forall2_image h (fun a ha b hb => by
    obtain ⟨b',_,hb'⟩ := forall2_left h' (p.mem_iff.mp (List.mem_map.mpr ⟨a,ha,rfl⟩))
    rw [chosen_eq fn hb',compat a ha b b' hb hb'])
  rw [← left,← forall2_chosen fn h']
  exact p.filterMap _

private theorem flat_image {β β' : Type} {E : β → List β → Prop} {V : β → β'}
    {F : β' → List β'} {xs : List β} {blocks : List (List β)} (all : List.Forall₂ E xs blocks)
    (each : ∀ x ∈ xs, ∀ ys, E x ys → (ys.map V).Perm (F (V x))) :
    (blocks.flatten.map V).Perm ((xs.map V).flatMap F) := by
  induction all with
  | nil => exact List.Perm.refl _
  | cons head _ ih =>
    simp only [List.flatten_cons,List.map_append,List.map_cons,List.flatMap_cons]
    exact (each _ List.mem_cons_self _ head).append
      (ih (fun c hc => each c (List.mem_cons_of_mem _ hc)))

/-! ## Two traces over corresponding expansions -/

/-- Two-sided `FullTrace.keys_unique`. The traces live on different carriers.
Matched visits expand to rows matched up to permutation, and the sort key is
carried by the match. The emitted key rows are then equal, whatever legal
order either side chose inside each tied sphere. -/
theorem trace_transport {β β' κ : Type} [LinearOrder κ] {key : β → κ} {key' : β' → κ}
    {E : β → List β → Prop} {E' : β' → List β' → Prop} (V : β → β') (P : β → Prop)
    (hkey : ∀ b, key' (V b) = key b)
    (functional : ∀ b xs ys, E' b xs → E' b ys → xs = ys)
    (step : ∀ b ys, P b → E b ys → ∀ c ∈ ys, P c)
    (matched : ∀ b ys ys', P b → E b ys → E' (V b) ys' → (ys.map V).Perm ys')
    {r o : List β} (a : FullTrace key E r o) :
    ∀ {r' o' : List β'}, FullTrace key' E' r' o' → (∀ b ∈ r, P b) → (r.map V).Perm r' →
      r.map key = r'.map key' → o.map key = o'.map key' := by
  induction a with
  | stop =>
    intro r' o' t _ p _
    have p' : r'.Perm [] := p.symm
    obtain rfl := p'.eq_nil
    cases t
    rfl
  | @sphere b row blocks next rest expand sorted _ ih =>
    intro r' o' t ok p same
    cases t with
    | stop => exact absurd p.eq_nil (by simp)
    | @sphere b' row' blocks' next' rest' expand' sorted' tail' =>
      have image : (blocks.flatten.map V).Perm (((b::row).map V).flatMap (pick E')) :=
        flat_image expand (fun x hx ys hy => by
          obtain ⟨ys',_,hy'⟩ := forall2_left expand' (p.mem_iff.mp (List.mem_map.mpr ⟨x,hx,rfl⟩))
          rw [pick_eq functional hy']
          exact matched x ys ys' (ok x hx) hy hy')
      have flat : (blocks.flatten.map V).Perm blocks'.flatten := by
        rw [flatten_pick functional expand']
        exact image.trans (p.flatMap_right (pick E'))
      have np : (next.map V).Perm next' := (sorted.perm.map V).trans (flat.trans sorted'.perm.symm)
      have pk : (next.map key).Perm (next'.map key') := by
        have h := np.map key'
        rwa [List.map_map,show key' ∘ V = key from funext hkey] at h
      have keys : next.map key = next'.map key' :=
        List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
          sorted.descending sorted'.descending pk
      have okNext : ∀ c ∈ next, P c := by
        intro c hc
        obtain ⟨block,inBlocks,inBlock⟩ := List.mem_flatten.mp (sorted.perm.mem_iff.mp hc)
        obtain ⟨parent,inRow,grown⟩ := forall2_right expand inBlocks
        exact step parent block (ok parent inRow) grown c inBlock
      rw [List.map_append,List.map_append,same,ih tail' okNext np keys]

/-! ## Two ranking oracles related by a child-permuting map -/

/-- Carry the cursor, keep the whole priority path. -/
def visit {i j : Input} (image : Arm i → Arm j) (v : FullVisit i) : FullVisit j :=
  ⟨image v.cursor,v.path⟩

section Oracles
variable {i j : Input} (o : Oracle i) (o' : Oracle j) (bit : Arm i → Option Bool)
  (bit' : Arm j → Option Bool) (image : Arm i → Arm j) (D : Arm i → Prop)
  (below : ∀ q, D q → ∀ c ∈ i.certified.executableLocalizedRerootChildren q, D c)
  (children : ∀ q, D q → ((i.certified.executableLocalizedRerootChildren q).map image).Perm
    (j.certified.executableLocalizedRerootChildren (image q)))
  (rank : ∀ c, D c → ∀ k k', o.Rank c k → o'.Rank (image c) k' → k = k')
  (bits : ∀ c, D c → bit' (image c) = bit c)

include below children rank bits in
/-- The children of matched visits carry equal complete priorities and equal
bits, so the two expansions are equal as multisets of (cursor, path). -/
theorem expansion_perm (p : FullVisit i) (vs : List (FullVisit i)) (ws : List (FullVisit j))
    (on : D p.cursor) (left : o.Expansion bit p vs)
    (right : o'.Expansion bit' (visit image p) ws) : (vs.map (visit image)).Perm ws := by
  refine forall2_perm (R := o.Child bit p) (R' := o'.Child bit' (visit image p)) (e := image)
    (g := visit image) ?_ left right (children p.cursor on) ?_
  · rintro c x y ⟨k,rk,rfl⟩ ⟨l,rl,rfl⟩
    obtain rfl := o'.unique _ _ _ rk rl
    rfl
  · rintro c hc b b' ⟨k,rk,rfl⟩ ⟨k',rk',rfl⟩
    have dc := below p.cursor on c hc
    obtain rfl := rank c dc k k' rk rk'
    show (⟨image c,p.path ++ [stepKey k.deep (bit c)]⟩ : FullVisit j) =
      ⟨image c,p.path ++ [stepKey k.deep (bit' (image c))]⟩
    rw [bits c dc]

include below children rank bits in
/-- Seed-word transport for arbitrary oracles. Any legal walk on either side
may be used. Their sphere orders are unrelated. -/
theorem source_transport {q : Arm i} (on : D q) {w w' : List Bool}
    (left : o.Source bit q w) (right : o'.Source bit' (image q) w') : w = w' := by
  obtain ⟨out,walk,rfl⟩ := left
  obtain ⟨out',walk',rfl⟩ := right
  have start : visit image (Oracle.root bit q) = Oracle.root bit' (image q) := by
    show (⟨image q,[stepKey [] (bit q)]⟩ : FullVisit j) =
      ⟨image q,[stepKey [] (bit' (image q))]⟩
    rw [bits q on]
  have paths : out.map FullVisit.path = out'.map FullVisit.path :=
    trace_transport (key := FullVisit.path (i := i)) (key' := FullVisit.path (i := j))
      (E := o.Expansion bit) (E' := o'.Expansion bit') (visit image) (fun v => D v.cursor)
      (fun _ => rfl) (o'.expansion_functional bit')
      (fun p ys hp grown c hc => by
        obtain ⟨a,ha,k,_,rfl⟩ := forall2_right grown hc
        exact below p.cursor hp a ha)
      (fun p ys ys' hp l r =>
        expansion_perm o o' bit bit' image D below children rank bits p ys ys' hp l r)
      walk walk'
      (fun b hb => by
        obtain rfl := List.mem_singleton.mp hb
        exact on)
      (List.Perm.of_eq (congrArg (fun x => [x]) start))
      (congrArg (fun x : FullVisit j => [x.path]) start)
  exact (Oracle.walk_bits walk).trans
    ((congrArg (List.filterMap bitOf) paths).trans (Oracle.walk_bits walk').symm)

end Oracles

/-! ## Carriers with matched frozen labels -/

theorem like_eq {i j : Input} (c : Carrier i j) {L : Reader i} {R : Reader j}
    (same : Frozen c L R) (rev : Bool) (seed : RS) (q : Arm i) (on : c.domain q) :
    likeAt j R rev seed (c.image q) = likeAt i L rev seed q := by
  unfold likeAt handAt
  rw [same q on]

/-- Full-path seed words at any list of priority stages, either seed. -/
theorem stage_source {i j : Input} (c : Carrier i j) {L : Reader i} {R : Reader j}
    (same : Frozen c L R) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation)
    (seed : RS) {q : Arm i} (on : c.domain q) {w w' : List Bool}
    (left : (stage i L rev os).Source (likeAt i L rev seed) q w)
    (right : (stage j R rev os).Source (likeAt j R rev seed) (c.image q) w') : w = w' :=
  source_transport (stage i L rev os) (stage j R rev os) (likeAt i L rev seed)
    (likeAt j R rev seed) c.image c.domain c.below c.children
    (fun a da k k' x y => c.refinement same os a da k k' x y)
    (fun a da => like_eq c same rev seed a da) on left right

/-- The declarative key judgment is carried. No readiness or totality is
needed: any two derivations at matched arms give equal keys. -/
theorem reads_transport {i j : Input} (c : Carrier i j) {L : Reader i} {R : Reader j}
    (same : Frozen c L R) (rev : Bool) {q : Arm i} (dom : c.domain q)
    {k k' : RingFullPathEligibility.Key} (left : Reads i L rev q k)
    (right : Reads j R rev (c.image q) k') : k = k' := by
  obtain ⟨u,lo,ar,as',fr,du,dl,sr,ss,sf,rfl⟩ := left
  obtain ⟨u',lo',ar',as'',fr',du',dl',sr',ss',sf',rfl⟩ := right
  obtain rfl := c.refinement same [] q dom _ _ du du'
  obtain rfl := c.refinement same [.lowercase] q dom _ _ dl dl'
  obtain rfl := stage_source c same rev [] .R dom sr sr'
  obtain rfl := stage_source c same rev [] .S dom ss ss'
  obtain rfl := stage_source c same rev [.lowercase] .R dom sf sf'
  rfl

/-- Executable keys agree for ready readers on both sides. -/
theorem key_transport {i j : Input} (c : Carrier i j) {L : Reader i} {R : Reader j}
    (same : Frozen c L R) {f : Site i} {g : Site j} (ready : RingGroupedStereo.Ready f L)
    (ready' : RingGroupedStereo.Ready g R) (rev : Bool) {q : Arm i} (dom : c.domain q)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (valid' : j.certified.LocalizedRerootCursorValid (c.image q))
    (on' : (c.image q).occurrence.val.root = g.val.root) :
    key? j R rev (c.image q) = key? i L rev q := by
  obtain ⟨k,hk,ek⟩ := key_exact ready rev q valid on
  obtain ⟨k',hk',ek'⟩ := key_exact ready' rev (c.image q) valid' on'
  rw [hk,hk']
  exact congrArg some (reads_transport c same rev dom ((ek k).mpr rfl) ((ek' k').mpr rfl)).symm

variable {i j : Input}

/-- A renumbered child of an aligned cursor is a valid cursor of the target. -/
theorem valid_child (r : AtomMap i j) {p q : Arm i}
    (hp : i.certified.cursorPreviousRootAligned p)
    (hq : q ∈ i.certified.executableLocalizedRerootChildren p) :
    j.certified.LocalizedRerootCursorValid (arm r q) := by
  have edges : ((i.certified.executableLocalizedRerootChildren p).map (arm r)).Perm
      (j.certified.executableLocalizedRerootChildren (arm r p)) := (carrier r).children p hp
  exact j.certified.localizedRerootChild_valid (arm r p) (arm r q) _
    (j.certified.executableLocalizedRerootChildren_declarative (arm r p))
    (edges.mem_iff.mp (List.mem_map.mpr ⟨q,hq,rfl⟩))

end TetraStereo.Engine.RingFullPathKeyTransport

assert_kernel_only TetraStereo.Engine.RingFullPathKeyTransport.key_transport
