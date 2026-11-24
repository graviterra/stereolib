import TetraStereo.Engine.RingOccurrenceStereo

/-! # Rule 4b like/unlike reading in one global full-path order

Hanson et al. (2018), pp. 1759–1760 and Figure 9, allow equivalent
occurrences from different parents to be ordered together under Rule 4b.

Every visited occurrence carries its whole path from the ligand root. Each
edge contributes the complete through-4a priority of the child followed by
the like/unlike bit of that child, so the path of a node is the prefix of
priorities interleaved with the bits of all its ancestors, ending in its own
bit. Spheres are compared first. Inside one sphere the whole sphere is sorted
by this path.

The molecular fixture in `validation/ring-chronology/Rule4bCrossParent.mol` has leaf hands
(RR,SS) against (RS,RS) below constitutionally equivalent parents. All four
leaves of an arm have equal priority prefixes, so only their own bit orders
them and every reading is 1100, as in stock Jmol. A parent-by-parent
breadth-first pass gives 1100 against 1010. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathPairs
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels upper)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path Occurs)
open RingRetainedUnitPass (Reading atArm)

private abbrev kids (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q
private abbrev budget (i : Input) (q : Arm i) := i.certified.localizedRerootCursorBudget q
private abbrev Valid {i : Input} (q : Arm i) := i.certified.LocalizedRerootCursorValid q
private abbrev On {i : Input} (f : Site i) (q : Arm i) := q.occurrence.val.root = f.val.root
private abbrev Ready {i : Input} (f : Site i) (r : Reader i) := RingGroupedStereo.Ready f r

/-! ## List facts -/

private theorem mapM_related {α β : Type} {f : α → Option β} {R : α → β → Prop}
    (sound : ∀ a b, f a = some b → R a b) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    have e : ([] : List α).mapM f = some [] := rfl
    obtain rfl := Option.some.inj (e.symm.trans h)
    exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨u,hu,more⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us,hus,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    exact .cons (sound _ _ hu) (ih hus)

private theorem related_of_mem {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp hy with rfl | rest
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨a,mem,ha⟩ := ih rest
      exact ⟨a,List.mem_cons_of_mem _ mem,ha⟩

private theorem forall2_functional {α β : Type} {R : α → β → Prop}
    (fn : ∀ a x y, R a x → R a y → x = y) {xs : List α} {us vs : List β}
    (l : List.Forall₂ R xs us) (r : List.Forall₂ R xs vs) : us = vs := by
  induction l generalizing vs with
  | nil => cases r; rfl
  | cons head _ ih =>
    cases r with
    | cons head' tail' => exact congrArg₂ List.cons (fn _ _ _ head head') (ih tail')

private theorem flatMap_perm {α β : Type} (f : α → List β) {xs ys : List α} (p : xs.Perm ys) :
    (xs.flatMap f).Perm (ys.flatMap f) := by
  induction p with
  | nil => exact List.Perm.refl _
  | cons x _ ih => simpa only [List.flatMap_cons] using ih.append_left (f x)
  | swap x y l =>
    have h : (f y ++ f x ++ l.flatMap f).Perm (f x ++ f y ++ l.flatMap f) :=
      List.perm_append_comm.append_right _
    simpa only [List.flatMap_cons,List.append_assoc] using h
  | trans _ _ first second => exact first.trans second

noncomputable def pick {β : Type} (E : β → List β → Prop) (b : β) : List β :=
  open Classical in if h : ∃ ys, E b ys then h.choose else []

theorem pick_eq {β : Type} {E : β → List β → Prop}
    (functional : ∀ b xs ys, E b xs → E b ys → xs = ys) {b : β} {ys : List β} (h : E b ys) :
    pick E b = ys := by
  have hx : ∃ zs, E b zs := ⟨ys,h⟩
  unfold pick
  rw [dif_pos hx]
  exact functional _ _ _ hx.choose_spec h

theorem flatten_pick {β : Type} {E : β → List β → Prop}
    (functional : ∀ b xs ys, E b xs → E b ys → xs = ys) {xs : List β} {bs : List (List β)}
    (all : List.Forall₂ E xs bs) : bs.flatten = xs.flatMap (pick E) := by
  induction all with
  | nil => rfl
  | cons head _ ih => rw [List.flatten_cons,List.flatMap_cons,ih,pick_eq functional head]

/-! ## Sphere-first traversal with one global sort per sphere -/

/-- Independent source judgment. A sphere is expanded completely: every
member contributes all of its children. The whole next sphere is then one
legal row, so ties between children of different parents are sorted together
and no occurrence is dropped. -/
inductive FullTrace {β κ : Type} [LinearOrder κ] (key : β → κ) (E : β → List β → Prop) :
    List β → List β → Prop where
  | stop : FullTrace key E [] []
  | sphere {b row blocks next rest} (expand : List.Forall₂ E (b::row) blocks)
      (sorted : Legal key blocks.flatten next) (tail : FullTrace key E next rest) :
      FullTrace key E (b::row) ((b::row) ++ rest)

/-- Two traces whose first spheres agree as multisets and as key rows emit
the same key at every position, whatever legal rows were chosen later. -/
theorem FullTrace.keys_unique {β κ : Type} [LinearOrder κ] {key : β → κ} {E : β → List β → Prop}
    (functional : ∀ b xs ys, E b xs → E b ys → xs = ys) {r o : List β} (a : FullTrace key E r o) :
    ∀ {r' o' : List β}, FullTrace key E r' o' → r.Perm r' → r.map key = r'.map key →
      o.map key = o'.map key := by
  induction a with
  | stop =>
    intro r' o' t p _
    obtain rfl := p.symm.eq_nil
    cases t
    rfl
  | @sphere b row blocks next rest expand sorted _ ih =>
    intro r' o' t p same
    cases t with
    | stop => exact absurd p.eq_nil (by simp)
    | @sphere b' row' blocks' next' rest' expand' sorted' tail' =>
      have flat : blocks.flatten.Perm blocks'.flatten := by
        rw [flatten_pick functional expand,flatten_pick functional expand']
        exact flatMap_perm _ p
      have np : next.Perm next' := sorted.perm.trans (flat.trans sorted'.perm.symm)
      have keys : next.map key = next'.map key :=
        List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
          sorted.descending sorted'.descending (np.map _)
      simp only [List.map_append,same,ih tail' np keys]

theorem FullTrace.all {β κ : Type} [LinearOrder κ] {key : β → κ} {E : β → List β → Prop}
    {P : β → Prop} (step : ∀ b ys, P b → E b ys → ∀ c ∈ ys, P c) {row out : List β}
    (t : FullTrace key E row out) : (∀ b ∈ row, P b) → ∀ b ∈ out, P b := by
  induction t with
  | stop => intro _ _ hb; contradiction
  | @sphere x row blocks next rest expand sorted _ ih =>
    intro start c hc
    rcases List.mem_append.mp hc with here | later
    · exact start c here
    · refine ih ?_ c later
      intro d hd
      obtain ⟨block,inBlocks,inBlock⟩ := List.mem_flatten.mp (sorted.perm.mem_iff.mp hd)
      obtain ⟨parent,inRow,grown⟩ := related_of_mem expand inBlocks
      exact step parent block (start parent inRow) grown d inBlock

/-- Executable global order: expand the whole sphere, sort it once. -/
def sphereRun {β κ : Type} [LinearOrder κ] (key : β → κ) (next : β → Option (List β)) :
    Nat → List β → Option (List β)
  | _,[] => some []
  | 0,_::_ => none
  | n+1,x::xs => do
    let blocks ← (x::xs).mapM next
    return (x::xs) ++ (← sphereRun key next n (order key blocks.flatten))

theorem sphereRun_sound {β κ : Type} [LinearOrder κ] {key : β → κ} {next : β → Option (List β)}
    {E : β → List β → Prop} (sound : ∀ b ys, next b = some ys → E b ys) :
    ∀ n row out, sphereRun key next n row = some out → FullTrace key E row out := by
  intro n
  induction n with
  | zero =>
    intro row out h
    cases row with
    | nil =>
      obtain rfl := Option.some.inj (show some ([] : List β) = some out from h)
      exact .stop
    | cons x xs => exact absurd (show (none : Option (List β)) = some out from h) (by simp)
  | succ n ih =>
    intro row out h
    cases row with
    | nil =>
      obtain rfl := Option.some.inj (show some ([] : List β) = some out from h)
      exact .stop
    | cons x xs =>
      change (List.mapM next (x::xs) >>= _) = _ at h
      obtain ⟨blocks,hb,more⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest,hr,eqn⟩ := Option.bind_eq_some_iff.mp more
      obtain rfl := Option.some.inj eqn
      exact .sphere (mapM_related sound hb) (legal_order key blocks.flatten) (ih _ _ hr)

theorem sphereRun_total {β κ : Type} [LinearOrder κ] (key : β → κ) (next : β → Option (List β))
    (good : Nat → β → Prop) (empty : ∀ b, ¬ good 0 b)
    (step : ∀ n b, good (n+1) b → ∃ ys, next b = some ys ∧ ∀ c ∈ ys, good n c) :
    ∀ n row, (∀ b ∈ row, good n b) → ∃ out, sphereRun key next n row = some out := by
  intro n
  induction n with
  | zero =>
    intro row ok
    cases row with
    | nil => exact ⟨[],rfl⟩
    | cons x xs => exact (empty x (ok x List.mem_cons_self)).elim
  | succ n ih =>
    intro row ok
    cases row with
    | nil => exact ⟨[],rfl⟩
    | cons x xs =>
      obtain ⟨blocks,hb⟩ := RingRetainedUnitPass.collect next (x::xs) (fun b hb => by
        obtain ⟨ys,hy,_⟩ := step n b (ok b hb)
        exact ⟨ys,hy⟩)
      obtain ⟨rest,hr⟩ := ih (order key blocks.flatten) (fun c hc => by
        obtain ⟨block,inBlocks,inBlock⟩ :=
          List.mem_flatten.mp ((legal_order key blocks.flatten).perm.mem_iff.mp hc)
        obtain ⟨b,member,got⟩ := RingRetainedUnitPass.forOutput hb inBlocks
        obtain ⟨ys,hy,small⟩ := step n b (ok b member)
        obtain rfl := Option.some.inj (hy.symm.trans got)
        exact small c inBlock)
      refine ⟨(x::xs) ++ rest,?_⟩
      change (List.mapM next (x::xs) >>= _) = _
      rw [hb]
      simp [hr]

/-! ## Molecular paths -/

def handAt (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option RS :=
  upper ((r q.occurrence).join.map fun p => if rev then p.2 else p.1)

/-- Like/unlike status of an uppercase occurrence against the seed. -/
def likeAt (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i) : Option Bool :=
  (handAt i r rev q).map (· == seed)

/-- Descending order gives the author implementation's neutral, like,
unlike order. Only the latter two emit a bit. -/
def likeCode : Option Bool → Nat
  | some true => 2
  | some false => 1
  | none => 3

/-- One edge: the child's complete through-4a priority, then its own bit. -/
def stepKey (deep : List Word) (m : Option Bool) : List Word := deep ++ [[[likeCode m]]]

/-- The bit recorded at the end of a path. -/
def bitOf (p : Path) : Option Bool :=
  match p.reverse with
  | step :: _ =>
    match step.reverse with
    | w :: _ => if w = [[2]] then some true else if w = [[1]] then some false else none
    | [] => none
  | [] => none

theorem bitOf_snoc (p : Path) (d : List Word) (m : Option Bool) :
    bitOf (p ++ [stepKey d m]) = m := by
  rcases m with _ | (_ | _) <;> simp [bitOf,stepKey,likeCode]

def stripBit (s : List Word) : List Word := s.reverse.tail.reverse

theorem stripBit_step (d : List Word) (m : Option Bool) : stripBit (stepKey d m) = d := by
  simp [stripBit,stepKey]

/-- The earlier-stage path of `RingRetainedReferenceGroup`: drop the root
step and every interleaved bit. -/
def priorities (p : Path) : Path := (p.drop 1).map stripBit

/-- The cursor keeps occurrences apart even when their paths coincide. -/
structure FullVisit (i : Input) where
  cursor : Arm i
  path : Path

private theorem child_facts {i : Input} {f : Site i} {q c : Arm i} (valid : Valid q)
    (on : On f q) (hc : c ∈ kids i q) : Valid c ∧ On f c ∧ budget i c < budget i q := by
  have frame := i.certified.executableLocalizedRerootChildren_declarative q
  exact ⟨i.certified.localizedRerootChild_valid q c _ frame hc,
    (i.certified.localizedRerootChildren_root_eq q c _ frame hc).trans on,
    i.certified.localizedRerootChild_budget_lt q c _ valid frame hc⟩

/-- Ranking oracle of one stage: source judgment, executable reader, functionality. -/
structure Oracle (i : Input) where
  Rank : Arm i → Branch → Prop
  rank? : Arm i → Option Branch
  sound : ∀ c k, rank? c = some k → Rank c k
  unique : ∀ c k l, Rank c k → Rank c l → k = l

def stage (i : Input) (r : Reader i) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) : Oracle i :=
  ⟨RingRetainedStereoRefinement.Derives i r rev stages,
   RingRetainedStereoRefinement.priority i r rev stages,
   fun c _ h => RingRetainedStereoRefinement.source stages c h,
   RingRetainedStereoRefinement.unique stages⟩

namespace Oracle

def root {i : Input} (bit : Arm i → Option Bool) (q : Arm i) : FullVisit i :=
  ⟨q,[stepKey [] (bit q)]⟩

def Child {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (p : FullVisit i)
    (c : Arm i) (v : FullVisit i) : Prop :=
  ∃ k, o.Rank c k ∧ v = ⟨c,p.path ++ [stepKey k.deep (bit c)]⟩

def Expansion {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (p : FullVisit i)
    (vs : List (FullVisit i)) : Prop :=
  List.Forall₂ (o.Child bit p) (kids i p.cursor) vs

abbrev Walk {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) :=
  FullTrace (FullVisit.path (i := i)) (o.Expansion bit)

def Source {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (q : Arm i)
    (bits : List Bool) : Prop :=
  ∃ out, o.Walk bit [root bit q] out ∧ bits = out.filterMap fun v => bit v.cursor

theorem expansion_functional {i : Input} (o : Oracle i) (bit : Arm i → Option Bool)
    (p : FullVisit i) (xs ys : List (FullVisit i)) (a : o.Expansion bit p xs)
    (b : o.Expansion bit p ys) : xs = ys :=
  forall2_functional (R := o.Child bit p) (fun _ _ _ u v => by
    obtain ⟨k,rk,rfl⟩ := u
    obtain ⟨l,rl,rfl⟩ := v
    obtain rfl := o.unique _ _ _ rk rl
    rfl) a b

inductive Reach {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (q : Arm i) :
    FullVisit i → Prop where
  | root : Reach o bit q (Oracle.root bit q)
  | child {p c k} (parent : Reach o bit q p) (edge : c ∈ kids i p.cursor) (rank : o.Rank c k) :
      Reach o bit q ⟨c,p.path ++ [stepKey k.deep (bit c)]⟩

theorem reached {i : Input} {o : Oracle i} {bit : Arm i → Option Bool} {q : Arm i}
    {out : List (FullVisit i)} (t : o.Walk bit [root bit q] out) : ∀ v ∈ out, Reach o bit q v :=
  FullTrace.all (P := Reach o bit q) (fun _ _ hp grown _ hv => by
    obtain ⟨c,hc,k,rank,rfl⟩ := related_of_mem grown hv
    exact .child hp hc rank) t (fun b hb => by
      obtain rfl := List.mem_singleton.mp hb
      exact .root)

theorem Reach.faithful {i : Input} {o : Oracle i} {bit : Arm i → Option Bool} {q : Arm i}
    {v : FullVisit i} (h : Reach o bit q v) : bitOf v.path = bit v.cursor := by
  cases h with
  | root => exact (bitOf_snoc [] [] (bit q) : bitOf [stepKey [] (bit q)] = _)
  | child _ _ _ => exact bitOf_snoc _ _ _

theorem walk_bits {i : Input} {o : Oracle i} {bit : Arm i → Option Bool} {q : Arm i}
    {out : List (FullVisit i)} (t : o.Walk bit [root bit q] out) :
    out.filterMap (fun v => bit v.cursor) = (out.map FullVisit.path).filterMap bitOf := by
  rw [List.filterMap_map]
  apply List.filterMap_congr
  intro v hv
  exact ((reached t v hv).faithful).symm

def next? {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (p : FullVisit i) :
    Option (List (FullVisit i)) :=
  (kids i p.cursor).mapM fun c => do
    let k ← o.rank? c
    return (⟨c,p.path ++ [stepKey k.deep (bit c)]⟩ : FullVisit i)

def visits? {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (q : Arm i) :
    Option (List (FullVisit i)) :=
  sphereRun FullVisit.path (o.next? bit) (budget i q + 1) [root bit q]

def bits? {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (q : Arm i) :
    Option (List Bool) :=
  (o.visits? bit q).map fun out => out.filterMap fun v => bit v.cursor

theorem next_sound {i : Input} (o : Oracle i) (bit : Arm i → Option Bool) (p : FullVisit i)
    (ys : List (FullVisit i)) (h : o.next? bit p = some ys) : o.Expansion bit p ys := by
  unfold next? at h
  show List.Forall₂ (o.Child bit p) (kids i p.cursor) ys
  refine mapM_related (fun c v hv => ?_) h
  obtain ⟨k,hk,out⟩ := Option.bind_eq_some_iff.mp hv
  obtain rfl := Option.some.inj out
  exact ⟨k,o.sound c k hk,rfl⟩

/-- Existence and exactness for any oracle that is total on the focus. -/
theorem source_exact {i : Input} {f : Site i} (o : Oracle i) (bit : Arm i → Option Bool)
    (total : ∀ c, Valid c → On f c → ∃ k, o.rank? c = some k)
    (q : Arm i) (valid : Valid q) (on : On f q) :
    ∃ bits, o.bits? bit q = some bits ∧ ∀ other, o.Source bit q other ↔ other = bits := by
  obtain ⟨out,h⟩ := sphereRun_total FullVisit.path (o.next? bit)
    (fun n v => Valid v.cursor ∧ On f v.cursor ∧ budget i v.cursor < n)
    (fun _ h => Nat.not_lt_zero _ h.2.2)
    (fun n p ok => by
      obtain ⟨pv,po,enough⟩ := ok
      obtain ⟨ys,hy⟩ := RingRetainedUnitPass.collect
        (fun c : Arm i => do
          let k ← o.rank? c
          return (⟨c,p.path ++ [stepKey k.deep (bit c)]⟩ : FullVisit i))
        (kids i p.cursor) (fun c hc => by
          obtain ⟨vc,oc,_⟩ := child_facts pv po hc
          obtain ⟨k,hk⟩ := total c vc oc
          exact ⟨⟨c,p.path ++ [stepKey k.deep (bit c)]⟩,by simp [hk]⟩)
      refine ⟨ys,hy,fun v hv => ?_⟩
      obtain ⟨c,hc,k,_,rfl⟩ := related_of_mem (o.next_sound bit p ys hy) hv
      obtain ⟨vc,oc,lt⟩ := child_facts pv po hc
      show Valid c ∧ On f c ∧ budget i c < n
      exact ⟨vc,oc,by omega⟩)
    (budget i q + 1) [root bit q]
    (fun b hb => by
      obtain rfl := List.mem_singleton.mp hb
      exact ⟨valid,on,Nat.lt_succ_self _⟩)
  have walk : o.Walk bit [root bit q] out := sphereRun_sound (o.next_sound bit) _ _ _ h
  refine ⟨out.filterMap (fun v => bit v.cursor),by simp [bits?,visits?,h],fun other => ⟨?_,?_⟩⟩
  · rintro ⟨alt,legal,rfl⟩
    rw [walk_bits legal,walk_bits walk,
      FullTrace.keys_unique (o.expansion_functional bit) legal walk (List.Perm.refl _) rfl]
  · rintro rfl
    exact ⟨out,walk,rfl⟩

end Oracle

abbrev FullWalk (i : Input) (r : Reader i) (rev : Bool) (seed : RS) :=
  (stage i r rev []).Walk (likeAt i r rev seed)
abbrev FullSource (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i)
    (bits : List Bool) := (stage i r rev []).Source (likeAt i r rev seed) q bits
abbrev rootVisit (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :=
  Oracle.root (likeAt i r rev seed) q
abbrev FullReach (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :=
  Oracle.Reach (stage i r rev []) (likeAt i r rev seed) q
theorem reached {i : Input} {r : Reader i} {rev : Bool} {seed : RS} {q : Arm i}
    {out : List (FullVisit i)} (t : FullWalk i r rev seed [rootVisit i r rev seed q] out) :
    ∀ v ∈ out, FullReach i r rev seed q v := Oracle.reached t

private def nextWith {i : Input} (r : Reader i) (rev : Bool) (seed : RS)
    (edges : Arm i → List (Arm i)) (rank : Arm i → Option Branch) (p : FullVisit i) :
    Option (List (FullVisit i)) :=
  (edges p.cursor).mapM fun c => do
    let k ← rank c
    return (⟨c,p.path ++ [stepKey k.deep (likeAt i r rev seed c)]⟩ : FullVisit i)

/-- The complete molecular priority at each edge uses the stages preceding
the reference comparison. -/
def stageWords (i : Input) (r : Reader i) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) : Option (List Bool) :=
  (stage i r rev os).bits? (likeAt i r rev seed) q

private def cachedWords (i : Input) (r : Reader i) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) (q : Arm i) : Option (List Bool) :=
  RingOccurrenceStereo.withRankReaders i r rev os q fun edges rank =>
    (sphereRun FullVisit.path (nextWith r rev seed edges rank) (budget i q + 1)
      [rootVisit i r rev seed q]).map fun out => out.filterMap fun v => likeAt i r rev seed v.cursor

@[csimp] private theorem cached_words_exact : @stageWords = @cachedWords := by
  funext i r rev os seed q
  unfold cachedWords
  rw [RingOccurrenceStereo.withRankReaders_eq]
  rfl

def pairs? (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i) : Option (List Bool) :=
  stageWords i r rev [] seed q

theorem source_exact {i : Input} {f : Site i} {r : Reader i} (ready : Ready f r) (rev : Bool)
    (seed : RS) (q : Arm i) (valid : Valid q) (on : On f q) :
    ∃ bits, pairs? i r rev seed q = some bits ∧
      ∀ other, FullSource i r rev seed q other ↔ other = bits :=
  (stage i r rev []).source_exact (likeAt i r rev seed)
    (RingOccurrenceStereo.rank_total ready rev []) q valid on

/-- The same statement at any reached state of the seeded frames. -/
theorem state_exact {i : Input} {f : Site i} {r : Reader i} {rev : Bool} (ready : Ready f r)
    (t : RingRetainedSeedFrames.State i r rev) (on : On f t.q) (seed : RS) :
    ∃ bits, pairs? i r rev seed t.q = some bits ∧
      ∀ other, FullSource i r rev seed t.q other ↔ other = bits :=
  source_exact ready rev seed t.q t.valid on

/-! ## Bridge to the earlier-stage keys -/

private theorem here_of_hand {i : Input} {r : Reader i} {rev : Bool} {c : Arm i} {h : RS}
    (hh : handAt i r rev c = some h) : Occurs i r rev c ⟨[],h⟩ := by
  unfold handAt at hh
  generalize seen : r c.occurrence = o at hh
  cases o with
  | none => exact absurd (show (none : Option RS) = some h from hh) (by simp)
  | some v => exact .here seen hh

private theorem FullReach.descends {i : Input} {r : Reader i} {rev : Bool} {seed : RS} {q : Arm i}
    {v : FullVisit i} (h : FullReach i r rev seed q v) :
    ∃ pre : Path, v.path = stepKey [] (likeAt i r rev seed q) :: pre ∧
      ∀ (tail : Path) (hand : RS), Occurs i r rev v.cursor ⟨tail,hand⟩ →
        Occurs i r rev q ⟨pre.map stripBit ++ tail,hand⟩ := by
  induction h with
  | root => exact ⟨[],rfl,fun _ _ o => o⟩
  | @child p c k _ edge rank ih =>
    obtain ⟨pre,eqn,lift⟩ := ih
    refine ⟨pre ++ [stepKey k.deep (likeAt i r rev seed c)],?_,?_⟩
    · exact congrArg (fun l => l ++ [stepKey k.deep (likeAt i r rev seed c)]) eqn
    · intro tail hand o
      have up := lift (k.deep :: tail) hand (.child edge rank o)
      have e : (pre ++ [stepKey k.deep (likeAt i r rev seed c)]).map stripBit ++ tail =
          pre.map stripBit ++ (k.deep :: tail) := by simp [stripBit_step]
      rw [e]
      exact up

/-- Every uppercase visit of a source trace is an occurrence of the existing
reference-selection judgment, at exactly the through-4a path obtained by
forgetting the interleaved bits. The full-path order therefore refines the
earlier-stage keys and introduces no occurrence of its own. -/
theorem occurs {i : Input} {r : Reader i} {rev : Bool} {seed : RS} {q : Arm i}
    {out : List (FullVisit i)} (t : FullWalk i r rev seed [rootVisit i r rev seed q] out)
    {v : FullVisit i} (hv : v ∈ out) {h : RS} (chiral : handAt i r rev v.cursor = some h) :
    Occurs i r rev q ⟨priorities v.path,h⟩ := by
  obtain ⟨pre,eqn,lift⟩ := (reached t v hv).descends
  have e : priorities v.path = pre.map stripBit ++ [] := by
    rw [eqn]
    simp [priorities]
  rw [e]
  exact lift [] h (here_of_hand chiral)

/-! ## The chosen chemical rule -/

private def sign (o : Ordering) : Int := match o with
  | .lt => -1 | .eq => 0 | .gt => 1

/-- Rule 4b with the existing reference selection and the full-path
readings. With two references on each side the ligand holding the highest of
the four readings wins; otherwise the contest ties. -/
def decision? (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) : Option Int := do
  match ← RingOccurrenceStereo.seeds? i r rev a, ← RingOccurrenceStereo.seeds? i r rev b with
  | [],[] => return 0
  | [s],[t] => return sign (compare (← pairs? i r rev s a) (← pairs? i r rev t b))
  | [_],[_,_] => return 1
  | [_,_],[_] => return -1
  | [s,t],[u,v] =>
    return sign (RingOccurrenceStereo.fourLists (← pairs? i r rev s a) (← pairs? i r rev t a)
      (← pairs? i r rev u b) (← pairs? i r rev v b))
  | _,_ => none

/-- The four-reading contest is a function of the source relation alone: any
four source readings give the comparison of the two best executable readings. -/
theorem rule_exact {i : Input} {f : Site i} {r : Reader i} (ready : Ready f r) (rev : Bool)
    (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) (s t u v : RS) :
    ∃ w x y z, pairs? i r rev s a = some w ∧ pairs? i r rev t a = some x ∧
      pairs? i r rev u b = some y ∧ pairs? i r rev v b = some z ∧
      ∀ w' x' y' z', FullSource i r rev s a w' → FullSource i r rev t a x' →
        FullSource i r rev u b y' → FullSource i r rev v b z' →
        RingOccurrenceStereo.fourLists w' x' y' z' = compare (max w x) (max y z) := by
  obtain ⟨w,hw,ew⟩ := source_exact ready rev s a va oa
  obtain ⟨x,hx,ex⟩ := source_exact ready rev t a va oa
  obtain ⟨y,hy,ey⟩ := source_exact ready rev u b vb ob
  obtain ⟨z,hz,ez⟩ := source_exact ready rev v b vb ob
  refine ⟨w,x,y,z,hw,hx,hy,hz,?_⟩
  intro w' x' y' z' sw sx sy sz
  obtain rfl := (ew w').mp sw
  obtain rfl := (ex x').mp sx
  obtain rfl := (ey y').mp sy
  obtain rfl := (ez z').mp sz
  exact RingOccurrenceStereo.fourLists_order ..

/-- An arm's references come from a complete occurrence listing. Its two
reference-dependent words may be derived using independent legal sphere orders. -/
structure ArmReading (i : Input) (r : Reader i) (rev : Bool) (q : Arm i)
    (refs : List RS) (words : RS → List Bool) : Prop where
  references : ∃ hs, RingRetainedReferenceGroup.Listing i r q hs ∧
    DeclarativeLocalizedRule4bReferencesFromPopulation (RingRetainedReferenceGroup.hands hs rev) refs
  readings : ∀ s, FullSource i r rev s q (words s)

theorem armReading_exact {i f r rev} (ready : @Ready i f r)
    (a : RingRetainedSeedFrames.State i r rev) (on : On f a.q)
    (refs : List RS) (words : RS → List Bool) :
    ArmReading i r rev a.q refs words ↔
      RingOccurrenceStereo.seeds? i r rev a.q = some refs ∧
      ∀ s, pairs? i r rev s a.q = some (words s) := by
  rw [RingOccurrenceStereo.seeds_exact ready a on]
  constructor
  · rintro ⟨⟨hs,listing,votes⟩,legal⟩
    obtain rfl := listing.unique a.source.hits
    refine ⟨congrArg some ((RingRetainedReferenceGroup.references_exact ..).mpr votes),fun s => ?_⟩
    obtain ⟨w,hw,eqn⟩ := state_exact ready a on s
    rw [(eqn _).mp (legal s)]
    exact hw
  · rintro ⟨selected,computed⟩
    refine ⟨⟨_,a.source.hits,(RingRetainedReferenceGroup.references_exact ..).mp
      (Option.some.inj selected)⟩,fun s => ?_⟩
    obtain ⟨w,hw,eqn⟩ := state_exact ready a on s
    exact (eqn _).mpr (Option.some.inj ((computed s).symm.trans hw))

def contest (x y : RS → List Bool) : List RS → List RS → Option Int
  | [],[] => some 0
  | [s],[t] => some (sign (compare (x s) (y t)))
  | [_],[_,_] => some 1
  | [_,_],[_] => some (-1)
  | [s,t],[u,v] => some (sign (compare (max (x s) (x t)) (max (y u) (y v))))
  | _,_ => none

/-- Every combination of admitted reference counts is adjudicated from its
two complete arm readings, including single versus dual before comparing bits. -/
theorem decision_of_readings {i f r rev} (ready : @Ready i f r)
    (a b : RingRetainedSeedFrames.State i r rev) (oa : On f a.q) (ob : On f b.q)
    {rs ts x y} (left : ArmReading i r rev a.q rs x) (right : ArmReading i r rev b.q ts y) :
    decision? i r rev a.q b.q = contest x y rs ts := by
  obtain ⟨hr,hx⟩ := (armReading_exact ready a oa rs x).mp left
  obtain ⟨ht,hy⟩ := (armReading_exact ready b ob ts y).mp right
  simp only [decision?,hr,ht,Option.bind_some,Option.bind_eq_bind]
  cases rs with
  | nil => cases ts <;> rfl
  | cons s ss =>
    cases ts with
    | nil => rcases ss with _ | ⟨_,_ | ⟨_,_⟩⟩ <;> rfl
    | cons t tt =>
      cases ss with
      | nil => cases tt with
        | nil => simp [contest,hx,hy]
        | cons u us => cases us <;> rfl
      | cons s' ss =>
        cases ss with
        | cons _ _ => cases tt <;> rfl
        | nil => cases tt with
          | nil => rfl
          | cons t' tt =>
            cases tt with
            | cons _ _ => rfl
            | nil => simp [contest,hx,hy,RingOccurrenceStereo.fourLists_order]

theorem armReading_exists {i f r rev} (ready : @Ready i f r)
    (a : RingRetainedSeedFrames.State i r rev) (on : On f a.q) :
    ∃ rs words, ArmReading i r rev a.q rs words := by
  obtain ⟨wr,hr,_⟩ := state_exact ready a on .R
  obtain ⟨ws,hs,_⟩ := state_exact ready a on .S
  let words : RS → List Bool := fun | .R => wr | .S => ws
  exact ⟨_,words,(armReading_exact ready a on _ words).mpr
    ⟨RingOccurrenceStereo.seeds_exact ready a on,fun | .R => hr | .S => hs⟩⟩

/-- Coordinate admission discharges the frozen-reader premise at every site
of the public grouped publication schedule, for either geometry. -/
theorem frozen_decision {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool)
    (a b : RingRetainedSeedFrames.State i
      (RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f) rev)
    (oa : On f a.q) (ob : On f b.q) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    ∃ rs ts x y, ArmReading i r rev a.q rs x ∧ ArmReading i r rev b.q ts y ∧
      decision? i r rev a.q b.q = contest x y rs ts := by
  intro r
  have ready := RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f
  obtain ⟨rs,x,hx⟩ := armReading_exists ready a oa
  obtain ⟨ts,y,hy⟩ := armReading_exists ready b ob
  exact ⟨rs,ts,x,y,hx,hy,decision_of_readings ready a b oa ob hx hy⟩

private theorem state_for {i f r} (ready : @Ready i f r) (rev : Bool) (q : Arm i)
    (valid : Valid q) (on : On f q) : ∃ a : RingRetainedSeedFrames.State i r rev, a.q = q := by
  obtain ⟨p,hp⟩ := RingGroupedStereo.arm_ready ready q valid on
  have src := RingGroupedStereo.arm_source hp
  cases rev with
  | false => exact ⟨⟨q,valid,p,src⟩,rfl⟩
  | true => exact ⟨⟨q,valid,p.reflect,src.reflect⟩,rfl⟩

private theorem contest_total {i r rev} (a b : RingRetainedSeedFrames.State i r rev)
    (tie : a.profile.unit.word = b.profile.unit.word) (x y : RS → List Bool) :
    ∃ score, contest x y (RingRetainedReferenceGroup.references a.profile.hits rev)
      (RingRetainedReferenceGroup.references b.profile.hits rev) = some score := by
  obtain ⟨k,hk⟩ := RingRetainedStereoDecision.fourB_total a.source b.source tie
  rcases RingRetainedReferenceGroup.references_cases a.profile.hits rev with l | ⟨s,l⟩ | l <;>
    rcases RingRetainedReferenceGroup.references_cases b.profile.hits rev with h | ⟨t,h⟩ | h <;>
    simp_all [contest,RingRetainedStereoDecision.fourB?]

/-- On any two valid arms of the focus that reach Rule 4b, a score exists.
Every legal pair of arm readings produces that score. The only input beyond
the molecular data and arm incidence is the through-4a tie that invokes 4b. -/
theorem frozen_score {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) (a b : Arm i) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    (∃ u v, Reading i r rev a u ∧ Reading i r rev b v ∧ u.word = v.word) →
    ∃ score, decision? i r rev a b = some score ∧
      (∃ rs x, ArmReading i r rev a rs x) ∧ (∃ ts y, ArmReading i r rev b ts y) ∧
      ∀ rs ts x y, ArmReading i r rev a rs x → ArmReading i r rev b ts y →
        contest x y rs ts = some score := by
  intro r ⟨u,v,hu,hv,tie⟩
  have ready : Ready f r := RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f
  obtain ⟨sa,rfl⟩ := state_for ready rev a va oa
  obtain ⟨sb,rfl⟩ := state_for ready rev b vb ob
  have ua : u = sa.profile.unit := hu.unique sa.source.unit
  have ub : v = sb.profile.unit := hv.unique sb.source.unit
  obtain ⟨rs,x,hx⟩ := armReading_exists ready sa oa
  obtain ⟨ts,y,hy⟩ := armReading_exists ready sb ob
  have left := (armReading_exact ready sa oa _ _).mp hx
  have right := (armReading_exact ready sb ob _ _).mp hy
  have lr := Option.some.inj (left.1.symm.trans (RingOccurrenceStereo.seeds_exact ready sa oa))
  have rr := Option.some.inj (right.1.symm.trans (RingOccurrenceStereo.seeds_exact ready sb ob))
  obtain ⟨score,hs⟩ := contest_total sa sb (ua ▸ ub ▸ tie) x y
  have dec := (decision_of_readings ready sa sb oa ob hx hy).trans ((lr ▸ rr ▸ hs) :
    contest x y rs ts = some score)
  exact ⟨score,dec,⟨rs,x,hx⟩,⟨ts,y,hy⟩,fun _ _ _ _ ha hb =>
    (decision_of_readings ready sa sb oa ob ha hb).symm.trans dec⟩

/-- The molecular entry point checks incidence, constitution and Rule 4a.
A zero there supplies all the hypotheses of the graph theorem on both
geometries, including the existence of complete reference derivations. -/
theorem after_fourA {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f a b : Site i) (rev : Bool) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    let left : Arm i := ⟨a,some f⟩
    let right : Arm i := ⟨b,some f⟩
    RingRetainedUnitPass.compareUnit? i f a b r = some 0 →
    ∃ score, decision? i r rev left right = some score ∧
      (∃ rs x, ArmReading i r rev left rs x) ∧ (∃ ts y, ArmReading i r rev right ts y) ∧
      ∀ rs ts x y, ArmReading i r rev left rs x → ArmReading i r rev right ts y →
        contest x y rs ts = some score := by
  intro r left right evaluated
  unfold RingRetainedUnitPass.compareUnit? at evaluated
  obtain ⟨_,prior,more⟩ := Option.bind_eq_some_iff.mp evaluated
  obtain ⟨_,_,more⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨u,hu,more⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨v,hv,out⟩ := Option.bind_eq_some_iff.mp more
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  have valid (q : Site i) (near : i.certified.LocalizedCarrierTreeAdjacent q.val f.val) :
      Valid (⟨q,some f⟩ : Arm i) :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨q.property,near⟩
  exact frozen_score geom f rev left right (valid a inc.2.2.1) (valid b inc.2.2.2)
    inc.2.2.1.1 inc.2.2.2.1 ⟨u,v,RingRetainedUnitPass.source i r rev _ _ hu,
      RingRetainedUnitPass.source i r rev _ _ hv,
      (RingRetainedUnitPass.signed_zero_iff ..).mp (Option.some.inj out)⟩

/-- Hanson et al. evaluate both references for each ligand and retain the
highest word on each side. This version needs no population shortcut. -/
def hanson? (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) : Option Int := do
  let ar ← pairs? i r rev .R a
  let as' ← pairs? i r rev .S a
  let br ← pairs? i r rev .R b
  let bs ← pairs? i r rev .S b
  return sign (RingOccurrenceStereo.fourLists ar as' br bs)

/-- Once the actual molecular comparison reaches Rule 4b, the best-of-both
test exists on the frozen store. Every quartet of independently legal
readings gives exactly that signed comparison. -/
theorem hanson_after_fourA {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f a b : Site i) (rev : Bool) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    let left : Arm i := ⟨a,some f⟩
    let right : Arm i := ⟨b,some f⟩
    RingRetainedUnitPass.compareUnit? i f a b r = some 0 →
    ∃ score, hanson? i r rev left right = some score ∧
      (∃ x : RS → List Bool, ∀ s, FullSource i r rev s left (x s)) ∧
      (∃ y : RS → List Bool, ∀ s, FullSource i r rev s right (y s)) ∧
      ∀ ar as' br bs, FullSource i r rev .R left ar → FullSource i r rev .S left as' →
        FullSource i r rev .R right br → FullSource i r rev .S right bs →
        score = sign (compare (max ar as') (max br bs)) := by
  intro r left right prior
  obtain ⟨_,_,⟨_,x,hx⟩,⟨_,y,hy⟩,_⟩ := after_fourA geom f a b rev prior
  unfold RingRetainedUnitPass.compareUnit? at prior
  obtain ⟨_,connected,_⟩ := Option.bind_eq_some_iff.mp prior
  have inc := (RingRetainedChemicalTrace.compareAt?_source connected).1
  have valid (q : Site i) (near : i.certified.LocalizedCarrierTreeAdjacent q.val f.val) :
      Valid (⟨q,some f⟩ : Arm i) :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨q.property,near⟩
  have ready : Ready f r := RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f
  obtain ⟨ar,as',br,bs,har,has,hbr,hbs,_⟩ := rule_exact ready rev left right
    (valid a inc.2.2.1) (valid b inc.2.2.2) inc.2.2.1.1 inc.2.2.2.1 .R .S .R .S
  refine ⟨sign (RingOccurrenceStereo.fourLists ar as' br bs),by simp [hanson?,har,has,hbr,hbs],
    ⟨x,hx.readings⟩,⟨y,hy.readings⟩,?_⟩
  intro w v u t sw sv su st
  have same {s : RS} {q : Arm i} (vq : Valid q) (oq : On f q) {word readback : List Bool}
      (hw : pairs? i r rev s q = some word) (src : FullSource i r rev s q readback) :
      readback = word := by
    obtain ⟨word',h,eqn⟩ := source_exact ready rev s q vq oq
    exact ((eqn _).mp src).trans (Option.some.inj (h.symm.trans hw))
  rw [same (valid a inc.2.2.1) inc.2.2.1.1 har sw,
    same (valid a inc.2.2.1) inc.2.2.1.1 has sv,
    same (valid b inc.2.2.2) inc.2.2.2.1 hbr su,
    same (valid b inc.2.2.2) inc.2.2.2.1 hbs st,RingOccurrenceStereo.fourLists_order]

end TetraStereo.Engine.RingFullPathPairs

assert_kernel_only TetraStereo.Engine.RingFullPathPairs.FullTrace.keys_unique
assert_kernel_only TetraStereo.Engine.RingFullPathPairs.source_exact
assert_kernel_only TetraStereo.Engine.RingFullPathPairs.occurs
assert_kernel_only TetraStereo.Engine.RingFullPathPairs.rule_exact
assert_kernel_only TetraStereo.Engine.RingFullPathPairs.frozen_decision
assert_kernel_only TetraStereo.Engine.RingFullPathPairs.frozen_score
assert_kernel_only TetraStereo.Engine.RingFullPathPairs.after_fourA
assert_kernel_only TetraStereo.Engine.RingFullPathPairs.hanson_after_fourA
