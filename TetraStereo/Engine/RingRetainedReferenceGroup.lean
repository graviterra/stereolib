import TetraStereo.Engine.RingRetainedStereoRefinement
import TetraStereo.OneCenter.LocalizedRule4bPopulationInvariance

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedReferenceGroup
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open RingRetainedChemicalTrace (Word)
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels upper consistent)
open RingRetainedUnitPass (Reading atArm)

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- Each edge contributes its complete through-4a priority in the group of
children of its own parent. Equal paths retain all their occurrences. -/
abbrev Path := List (List Word)
structure Hit where
  path : Path
  hand : RS
  deriving Repr, DecidableEq

private def atSite (v : Option Labels) : List Hit :=
  ((upper (v.map Prod.fst)).map fun h => Hit.mk [] h).toList

private def under (key : List Word) (hits : List Hit) : List Hit :=
  hits.map fun h => { h with path := key :: h.path }

def joinHits (v : Option Labels) (parts : List (Branch × List Hit)) :=
  atSite v ++ parts.flatMap fun (k,hs) => under k.deep hs

/-- Read each occurrence once in the enumeration. The incidence list keeps
multiplicity even if two child branches have the same complete priority. -/
def enumerate (i : Input) (read : Reader i) : Nat → Arm i → Option (List Hit)
  | 0,_ => none
  | n+1,q => do
    let v ← read q.occurrence
    let branches ← (children i q).mapM fun c => do
      let k ← atArm i read c
      return (k,← enumerate i read n c)
    return joinHits v branches

/-- The allowed enumeration uses any complete molecular 4a reading on each
edge, before considering a reference descriptor. -/
inductive Listing (i : Input) (read : Reader i) : Arm i → List Hit → Prop where
  | node {q v parts} (seen : read q.occurrence = some v)
      (physical : v.all consistent = true ∧ (children i q = [] → v = none))
      (lookup : Arm i → Option (Branch × List Hit)) (allChildren : (children i q).mapM lookup = some parts)
      (rank : ∀ c ∈ children i q, ∀ {k hs}, lookup c = some (k,hs) → Reading i read false c k)
      (below : ∀ c ∈ children i q, ∀ {k hs}, lookup c = some (k,hs) → Listing i read c hs) :
      Listing i read q (joinHits v parts)

theorem Listing.unique {i read q xs ys} (a : Listing i read q xs) (b : Listing i read q ys) : xs = ys := by
  induction a generalizing ys with
  | node seen _ lookup found rank below ih =>
    cases b with
    | node seen' _ _ found' rank' below' =>
      obtain rfl := Option.some.inj (seen.symm.trans seen')
      apply congrArg (joinHits _)
      apply RingRetainedUnitPass.map_same found found'
      rintro c hc ⟨k,hs⟩ ⟨l,ts⟩ hu hv
      exact Prod.ext ((rank c hc hu).unique (rank' c hc hv)) (ih c hc hu (below' c hc hv))

/-- Follow actual child incidences, using any allowed 4a reading to label each
edge. The endpoint has the indicated uppercase descriptor on this geometry. -/
inductive Occurs (i : Input) (read : Reader i) (rev : Bool) : Arm i → Hit → Prop where
  | here {q v h} (seen : read q.occurrence = some v)
      (label : upper (v.map (fun p => if rev then p.2 else p.1)) = some h) :
      Occurs i read rev q ⟨[],h⟩
  | child {q c k path h} (edge : c ∈ children i q) (rank : Reading i read rev c k)
      (rest : Occurs i read rev c ⟨path,h⟩) : Occurs i read rev q ⟨k.deep :: path,h⟩

def Hit.geometry (h : Hit) (rev : Bool) : Hit :=
  { h with hand := if rev then h.hand.swap else h.hand }

private theorem mirrorHand (v : Option Labels) (ok : v.all consistent = true) (rev : Bool) :
    upper (v.map (fun p => if rev then p.2 else p.1)) =
      (upper (v.map Prod.fst)).map (fun h => if rev then h.swap else h) := by
  cases rev <;> rcases v with _ | ⟨(_|_),(_|_)⟩ <;> simp_all [consistent,upper]

theorem forInput {α β : Type} {f : α → Option β} {xs : List α} {ys : List β} {c : α}
    (found : xs.mapM f = some ys) (mem : c ∈ xs) : ∃ b ∈ ys, f c = some b := by
  have pairs := TerminalTie.mapM_forall₂ _ _ _ found
  clear found
  induction pairs with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨b,hb,get⟩ := ih tail
      exact ⟨b,List.mem_cons_of_mem _ hb,get⟩

private theorem both {i read q k} (rank : Reading i read false q k) (rev : Bool) :
    Reading i read rev q k := by
  cases rev
  · exact rank
  · exact RingRetainedStereoRefinement.mirror [] q k rank

private theorem atSite_iff {v : Option Labels} {p h} :
    Hit.mk p h ∈ atSite v ↔ p = [] ∧ upper (v.map Prod.fst) = some h := by
  cases e : upper (v.map Prod.fst) <;> simp [atSite,e,eq_comm]

theorem Listing.mem_iff {i read q hs} (listing : Listing i read q hs) (rev : Bool) (hit : Hit) :
    hit ∈ hs ↔ Occurs i read rev q (hit.geometry rev) := by
  induction listing generalizing hit with
  | @node q v parts seen physical lookup complete rank below ih =>
    rcases hit with ⟨path,h⟩
    simp only [joinHits,List.mem_append,List.mem_flatMap]
    constructor
    · rintro (atRoot | ⟨⟨k,sub⟩,part,member⟩)
      · obtain ⟨rfl,hand⟩ := atSite_iff.mp atRoot
        exact .here seen (by rw [mirrorHand v physical.1 rev,hand]; rfl)
      · obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput complete part
        obtain ⟨⟨p,s⟩,mem,eqn⟩ := List.mem_map.mp member
        cases eqn
        exact .child hc (both (rank c hc get) rev) ((ih c hc get _).mp mem)
    · intro walk
      change Occurs _ _ _ _ ⟨path,if rev then h.swap else h⟩ at walk
      cases walk with
      | here found hand =>
        obtain rfl := Option.some.inj (seen.symm.trans found)
        left
        apply atSite_iff.mpr
        refine ⟨rfl,?_⟩
        rw [mirrorHand _ physical.1 rev] at hand
        cases u : upper (v.map Prod.fst) with
        | none => simp [u] at hand
        | some s => cases rev <;> cases s <;> cases h <;> simp_all [RS.swap]
      | @child _ c k p _ edge key tail =>
        obtain ⟨⟨l,sub⟩,part,get⟩ := forInput complete edge
        obtain rfl := key.unique (both (rank c edge get) rev)
        right
        exact ⟨_,part,List.mem_map.mpr ⟨⟨p,h⟩,(ih c edge get _).mpr tail,rfl⟩⟩

private theorem mem_interleave {α : Type} {z : α} (a b : List (List α)) :
    z ∈ (RingChildKeyRecovery.interleave a b).flatten ↔ z ∈ a.flatten ∨ z ∈ b.flatten := by
  induction a generalizing b with
  | nil => simp [RingChildKeyRecovery.interleave]
  | cons x xs ih =>
    cases b with
    | nil => simp [RingChildKeyRecovery.interleave]
    | cons y ys => simp [RingChildKeyRecovery.interleave,ih,or_assoc,or_left_comm]

private theorem mem_forest (cs : List Branch) (z : Nat) :
    z ∈ ((cs.map Branch.levels).foldr RingChildKeyRecovery.interleave []).flatten.flatten ↔
      ∃ c ∈ cs, z ∈ c.levels.flatten.flatten := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.foldr_cons]
    rw [List.mem_flatten]
    simp_rw [mem_interleave]
    rw [show (∃ x ∈ c :: cs, z ∈ x.levels.flatten.flatten) ↔
      z ∈ c.levels.flatten.flatten ∨ ∃ x ∈ cs, z ∈ x.levels.flatten.flatten by simp, ← ih]
    simp only [List.mem_flatten]
    grind

private theorem mem_rows {cs sh de : List Branch} (a : sh.Perm cs) (d : de.Perm cs) (z : Nat) :
    z ∈ (rows sh de).flatten.flatten ↔ ∃ c ∈ cs, z ∈ c.word.flatten := by
  simp only [rows,List.flatten_cons,List.flatten_append,List.flatten_nil,List.append_nil,
    List.mem_append,List.mem_map,mem_forest,Branch.word,List.mem_singleton]
  constructor
  · rintro ((⟨c,h,rfl⟩ | ⟨c,h,rfl⟩) | ⟨c,h,occ⟩)
    · exact ⟨c,a.mem_iff.mp h,Or.inl rfl⟩
    · exact ⟨c,d.mem_iff.mp h,Or.inl rfl⟩
    · exact ⟨c,d.mem_iff.mp h,Or.inr occ⟩
  · rintro ⟨c,h,rfl | occ⟩
    · exact Or.inl (Or.inr ⟨c,d.mem_iff.mpr h,rfl⟩)
    · exact Or.inr ⟨c,d.mem_iff.mpr h,occ⟩

private theorem empty_join {v : Option Labels} {parts : List (Branch × List Hit)} :
    joinHits v parts = [] ↔ atSite v = [] ∧ ∀ p ∈ parts, p.2 = [] := by
  simp [joinHits,under,List.flatMap_eq_nil_iff]

private theorem atSite_empty (v : Option Labels) :
    atSite v = [] ↔ RingNestedActivePair.unit (v.map Prod.fst) ≠ 2 := by
  rcases v with _ | ⟨(_|_),y⟩ <;> simp [atSite,upper,RingNestedActivePair.unit]

/-- Rule 4a already fixes whether any uppercase descriptor exists. Thus a
tied pair cannot reach reference selection with an empty ligand on one side
and an occupied ligand on the other. -/
theorem Listing.empty_iff {i read q xs} (all : Listing i read q xs) {b}
    (reading : Reading i read false q b) : xs = [] ↔ 2 ∉ b.word.flatten := by
  induction all generalizing b with
  | @node q v parts seen _ lookup found rank sub ih =>
    cases reading with
    | @node _ k w cs sh de _ visited _ reader materialized childrenRead first second =>
      obtain rfl := Option.some.inj (seen.symm.trans visited)
      rw [empty_join,atSite_empty]
      change _ ↔ 2 ∉ [RingNestedActivePair.unit (v.map Prod.fst)] ++ (rows sh de).flatten.flatten
      simp only [List.mem_append,List.mem_singleton,not_or,mem_rows first.perm second.perm,not_exists,not_and]
      rw [eq_comm (a := 2)]
      apply and_congr_right
      intro _
      constructor
      · intro empty c hc occurs
        obtain ⟨t,edge,get⟩ := RingRetainedUnitPass.forOutput materialized hc
        obtain ⟨⟨l,hs⟩,part,look⟩ := forInput found edge
        exact ((ih t edge look (childrenRead t edge get)).mp (empty _ part)) occurs
      · rintro no ⟨l,hs⟩ part
        obtain ⟨t,edge,look⟩ := RingRetainedUnitPass.forOutput found part
        obtain ⟨c,hc,get⟩ := forInput materialized edge
        exact (ih t edge look (childrenRead t edge get)).mpr (no c hc)

/-- A chiral occurrence at smaller distance precedes every more distant
one. At one distance, comparison follows the first unequal child priority
on the path from the ligand root. -/
def senior (a b : Path) : Bool :=
  decide (a.length < b.length ∨ (a.length = b.length ∧ b < a))

def group (hits : List Hit) : List Hit :=
  hits.filter fun h => !(hits.any fun other => senior other.path h.path)

theorem mem_group {h : Hit} {hits : List Hit} : h ∈ group hits ↔ h ∈ hits ∧
    ∀ x ∈ hits, h.path.length ≤ x.path.length ∧ (x.path.length = h.path.length → x.path ≤ h.path) := by
  simp only [group,List.mem_filter,Bool.not_eq_true',List.any_eq_false,senior,decide_eq_true_eq]
  constructor
  · rintro ⟨mem,none⟩
    refine ⟨mem,fun x hx => ?_⟩
    have := none x hx
    exact ⟨Nat.le_of_not_gt (fun v => this (Or.inl v)),fun eqn => le_of_not_gt (fun v => this (Or.inr ⟨eqn,v⟩))⟩
  · rintro ⟨mem,all⟩
    exact ⟨mem,fun x hx => fun s => s.elim (Nat.not_lt.mpr (all x hx).1) (fun a => (not_lt_of_ge ((all x hx).2 a.1)) a.2)⟩

theorem group_empty (hits : List Hit) : group hits = [] ↔ hits = [] := by
  constructor
  · intro empty
    by_contra occupied
    obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil hits occupied
    obtain ⟨near,hn,least⟩ := Finset.exists_min_image hits.toFinset (fun h => h.path.length)
      ⟨a,List.mem_toFinset.mpr ha⟩
    let nearest := hits.toFinset.filter fun h => h.path.length = near.path.length
    obtain ⟨best,hb,greatest⟩ := Finset.exists_max_image nearest Hit.path
      ⟨near,Finset.mem_filter.mpr ⟨hn,rfl⟩⟩
    obtain ⟨member,depth⟩ := Finset.mem_filter.mp hb
    have seniorHit : best ∈ group hits := mem_group.mpr ⟨List.mem_toFinset.mp member,fun h hh =>
      ⟨depth ▸ least h (List.mem_toFinset.mpr hh),fun same =>
        greatest h (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hh,same.trans depth⟩)⟩⟩
    simp [empty] at seniorHit
  · rintro rfl; rfl

/-- Reflecting a selected population reverses every uppercase descriptor.
The complete 4a priority on each edge is shared by both geometries. -/
def hands (hits : List Hit) (rev : Bool) :=
  (group hits).map fun h => if rev then h.hand.swap else h.hand

def references (hits : List Hit) (rev : Bool) := localizedRule4bReferencesFromPopulation (hands hits rev)

/-- Reordering the enumeration of ranked occurrences preserves every
reference count, including a balanced population spanning tied parents. -/
theorem references_perm {xs ys : List Hit} (same : xs.Perm ys) (rev : Bool) :
    references xs rev = references ys rev := by
  have predicate (h : Hit) : xs.any (fun x => senior x.path h.path) = ys.any (fun x => senior x.path h.path) :=
    Bool.eq_iff_iff.mpr (by simp only [List.any_eq_true,same.mem_iff])
  have g : (group xs).Perm (group ys) := by
    unfold group
    simp_rw [predicate]
    exact same.filter _
  exact localizedRule4bReferencesFromPopulation_perm (g.map _)

theorem references_exact (hits : List Hit) (rev : Bool) (refs : List RS) :
    references hits rev = refs ↔ DeclarativeLocalizedRule4bReferencesFromPopulation (hands hits rev) refs :=
  localizedRule4bReferencesFromPopulation_eq_iff ..

theorem references_empty (hits : List Hit) (rev : Bool) : references hits rev = [] ↔ hits = [] := by
  rw [references_exact]
  simp [DeclarativeLocalizedRule4bReferencesFromPopulation,hands,group_empty]

theorem references_cases (hits : List Hit) (rev : Bool) :
    references hits rev = [] ∨ (∃ h, references hits rev = [h]) ∨ references hits rev = [.R,.S] := by
  have spec := (references_exact hits rev (references hits rev)).mp rfl
  rcases spec with ⟨_,empty⟩ | ⟨_,(⟨_,right⟩ | ⟨_,left⟩ | ⟨_,both⟩)⟩
  · exact Or.inl empty
  · exact Or.inr (Or.inl ⟨_,right⟩)
  · exact Or.inr (Or.inl ⟨_,left⟩)
  · exact Or.inr (Or.inr both)

theorem references_reflect (hits : List Hit) :
    references hits true = reflectSelectedRule4bReferences (references hits false) := by
  have h : hands hits true = (hands hits false).map RS.swap := by simp [hands,List.map_map,Function.comp_def]
  exact (congrArg localizedRule4bReferencesFromPopulation h).trans (localizedRule4bReferencesFromPopulation_reflectUppercase _)

abbrev hits? (i : Input) (read : Reader i) (q : Arm i) :=
  enumerate i read (i.certified.localizedRerootCursorBudget q + 1) q

theorem frontier {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ hits, hits? i read q = some hits ∧ Listing i read q hits := by
  intro read
  suffices ∀ n (t : Arm i), i.certified.LocalizedRerootCursorValid t → t.occurrence.val.root = f.val.root →
      i.certified.localizedRerootCursorBudget t < n → ∃ hs, enumerate i read n t = some hs ∧ Listing i read t hs
    from this _ q valid on (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro t _ _ b; omega
  | succ n ih =>
    intro t vt same bound
    obtain ⟨v,hv,ok,terminal⟩ := RingFrontierProfileShape.frontier_observation listed t same
    change read t.occurrence = some v at hv
    let lookup (c : Arm i) := do
      let k ← atArm i read c
      return (k,← enumerate i read n c)
    have frame := i.certified.executableLocalizedRerootChildren_declarative t
    have entries (c : Arm i) (hc : c ∈ children i t) : ∃ k hs, Reading i read false c k ∧
        Listing i read c hs ∧ lookup c = some (k,hs) := by
      have vc := i.certified.localizedRerootChild_valid t c _ frame hc
      have rc := (i.certified.localizedRerootChildren_root_eq t c _ frame hc).trans same
      obtain ⟨k,hk,src⟩ := RingRetainedUnitPass.frontier listed c vc rc
      change atArm i read c = some k at hk
      obtain ⟨hs,hhs,sub⟩ := ih c vc rc (by have := i.certified.localizedRerootChild_budget_lt t c _ vt frame hc; omega)
      exact ⟨k,hs,src false,sub,by simp [lookup,hk,hhs]⟩
    obtain ⟨parts,found⟩ := RingRetainedUnitPass.collect lookup (children i t) (fun c hc => by
      obtain ⟨_,_,_,_,h⟩ := entries c hc
      exact ⟨_,h⟩)
    refine ⟨joinHits v parts,?_,.node hv ⟨ok,terminal⟩ lookup found ?_ ?_⟩
    · simp only [enumerate,hv,Option.bind_eq_bind,Option.bind_some]
      change ((children i t).mapM lookup).bind _ = _
      rw [found]
      rfl
    all_goals
      intro c hc k hs get
      obtain ⟨l,ts,src,sub,computed⟩ := entries c hc
      cases Option.some.inj (get.symm.trans computed)
      assumption

end TetraStereo.Engine.RingRetainedReferenceGroup

assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.Listing.unique
assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.mem_group
assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.references_exact
assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.references_reflect
assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.frontier

assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.Listing.mem_iff

assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.Listing.empty_iff

assert_kernel_only TetraStereo.Engine.RingRetainedReferenceGroup.references_perm
