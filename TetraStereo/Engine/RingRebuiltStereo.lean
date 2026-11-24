import TetraStereo.Engine.RingZeroDuplicateMass
import TetraStereo.Engine.RingZeroMassReport

/-! # Rebuilt constitutional prefixes in every molecular stereo pass -/

set_option autoImplicit false
namespace TetraStereo.Engine.RingRebuiltStereo
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels)
open RingRetainedChemicalTrace (Key Word)
open RingZeroDuplicateMass (Corresponds headPriority)
open RingRetainedChemicalPreorder (orderWord)
open RingRetainedStereoDecision (ArmProfile)
open RingRetainedReferenceGroup (Hit)
open RingRetainedStereoRefinement (Observation)

/-- All branches have three constitutional prefix entries. Appending later
stages uses the later comparison exactly when these entries tie. -/
private theorem cmp_append {α : Type} [Ord α] (a b c d : List α) (len : a.length = b.length) :
    compare (a ++ c) (b ++ d) = (compare a b).then (compare c d) := by
  induction a generalizing b with
  | nil => cases b <;> first | rfl | simp at len
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      simp only [List.cons_append,List.compare_cons_cons,ih ys (Nat.succ.inj len)]
      cases compare x y <;> rfl

private structure Basis where
  old : Key
  rebuilt : Key
  related : Corresponds old rebuilt

private def Basis.key (b : Basis) (z : Bool) := if z then b.rebuilt else b.old

/-- A proof witness for two independently sorted branches. The stereo
suffixes, root observation and all sphere rows are shared. -/
private structure PairedBranch where
  basis : Basis
  headSuffix : List Nat
  deepSuffix : List Word
  value : Nat
  levels : Layers

private def PairedBranch.get (p : PairedBranch) (z : Bool) : Branch :=
  ⟨headPriority (p.basis.key z) ++ p.headSuffix,orderWord (p.basis.key z) ++ p.deepSuffix,p.value,p.levels⟩

private theorem shallow_cmp (a b : PairedBranch) :
    compare (a.get true).shallow (b.get true).shallow = compare (a.get false).shallow (b.get false).shallow := by
  simp only [PairedBranch.get,Branch.shallow,List.append_assoc]
  rw [cmp_append (headPriority (a.basis.key true)) (headPriority (b.basis.key true)) _ _ rfl,
      cmp_append (headPriority (a.basis.key false)) (headPriority (b.basis.key false)) _ _ rfl]
  exact congrArg (fun v : Ordering => v.then _) (a.basis.related.orders b.basis.related).1

private theorem deep_cmp (a b : PairedBranch) :
    compare (a.get true).deep (b.get true).deep = compare (a.get false).deep (b.get false).deep := by
  simp only [PairedBranch.get,Branch.deep,List.append_assoc]
  rw [cmp_append (orderWord (a.basis.key true)) (orderWord (b.basis.key true)) _ _ rfl,
      cmp_append (orderWord (a.basis.key false)) (orderWord (b.basis.key false)) _ _ rfl]
  exact congrArg (fun v : Ordering => v.then _) (a.basis.related.orders b.basis.related).2

private theorem list_lt {α : Type} [LinearOrder α] [Ord α] (lt : ∀ x y : α, compare x y = .lt ↔ x < y)
    (eqn : ∀ x y : α, compare x y = .eq ↔ x = y) (x y : List α) :
    compare x y = .lt ↔ x < y := DeclarativeCIP.compareLex_eq_lt_iff_of compare lt eqn x y

private theorem natList_lt (a b : List Nat) : compare a b = .lt ↔ a < b :=
  list_lt (fun _ _ => compare_lt_iff_lt) (fun _ _ => Std.compare_eq_eq_iff_eq) a b

private theorem word_lt (a b : Word) : compare a b = .lt ↔ a < b :=
  list_lt natList_lt (fun _ _ => Std.compare_eq_eq_iff_eq) a b

private theorem deep_lt (a b : List Word) : compare a b = .lt ↔ a < b :=
  list_lt word_lt (fun _ _ => Std.compare_eq_eq_iff_eq) a b

private def sorted {κ : Type} [LinearOrder κ] (key : Branch → κ) (xs : List PairedBranch) :=
  order (fun p : PairedBranch => key (p.get false)) xs

private theorem sort_project {κ : Type} [LinearOrder κ] (cmp : κ → κ → Ordering)
    (lt : ∀ x y, cmp x y = .lt ↔ x < y) (key : Branch → κ)
    (stable : ∀ a b : PairedBranch, cmp (key (a.get true)) (key (b.get true)) =
      cmp (key (a.get false)) (key (b.get false))) (xs : List PairedBranch) (z : Bool) :
    (sorted key xs).map (·.get z) = order key (xs.map (·.get z)) := by
  apply List.map_mergeSort
  intro a _ b _
  cases z with
  | false => rfl
  | true =>
    have h : key (b.get false) ≤ key (a.get false) ↔ key (b.get true) ≤ key (a.get true) := by
      rw [← not_lt,← not_lt,← lt,← lt,stable]
    change decide (_ ≤ _) = decide (_ ≤ _)
    simp only [h]

private def layers (xs : List PairedBranch) : Layers :=
  let sh := sorted Branch.shallow xs
  let de := sorted Branch.deep xs
  [sh.map (·.value),de.map (·.value)] :: (de.map (·.levels)).foldr RingChildKeyRecovery.interleave []

private theorem layers_project (xs : List PairedBranch) (z : Bool) :
    layers xs = rows (order Branch.shallow (xs.map (·.get z))) (order Branch.deep (xs.map (·.get z))) := by
  rw [← sort_project compare natList_lt _ shallow_cmp xs z,← sort_project compare deep_lt _ deep_cmp xs z]
  simp only [layers,rows,List.map_map]
  rfl

private def unitBranch (k : Basis) (v : Nat) (xs : List PairedBranch) : PairedBranch :=
  ⟨k,[],[],v,layers xs⟩

private def extend (p : PairedBranch) (v : Nat) (xs : List PairedBranch) : PairedBranch :=
  ⟨p.basis,p.headSuffix ++ [p.value],p.deepSuffix ++ [(p.get false).word],v,layers xs⟩

private theorem unit_project (k : Basis) (v : Nat) (xs : List PairedBranch) (z : Bool) :
    (unitBranch k v xs).get z = RingRetainedUnitPass.branch (k.key z) v
      (order Branch.shallow (xs.map (·.get z))) (order Branch.deep (xs.map (·.get z))) := by
  simp [PairedBranch.get,unitBranch,RingRetainedUnitPass.branch,layers_project xs z,headPriority]

private theorem extend_project (p : PairedBranch) (v : Nat) (xs : List PairedBranch) (z : Bool) :
    (extend p v xs).get z = RingRetainedStereoRefinement.extend (p.get z) v
      (order Branch.shallow (xs.map (·.get z))) (order Branch.deep (xs.map (·.get z))) := by
  simp [PairedBranch.get,extend,RingRetainedStereoRefinement.extend,Branch.shallow,Branch.deep,
    Branch.word,List.append_assoc,layers_project xs z]

private structure Address where
  path : List PairedBranch
  hand : RS

private def Address.hit (h : Address) (z : Bool) : Hit :=
  ⟨h.path.map (fun p => (p.get z).deep),h.hand⟩

private theorem path_cmp (a b : List PairedBranch) :
    compare (a.map fun p => (p.get true).deep) (b.map fun p => (p.get true).deep) =
    compare (a.map fun p => (p.get false).deep) (b.map fun p => (p.get false).deep) := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b with
    | nil => rfl
    | cons y ys => simp only [List.map_cons,List.compare_cons_cons,deep_cmp,ih]

private theorem senior_same (a b : Address) :
    RingRetainedReferenceGroup.senior (a.hit true).path (b.hit true).path =
    RingRetainedReferenceGroup.senior (a.hit false).path (b.hit false).path := by
  have lt := list_lt deep_lt (fun _ _ => Std.compare_eq_eq_iff_eq)
  simp only [RingRetainedReferenceGroup.senior,Address.hit,List.length_map,← lt,path_cmp]

private def population (xs : List Address) (z : Bool) :=
  xs.filter fun h => !(xs.any fun other => RingRetainedReferenceGroup.senior (other.hit z).path (h.hit z).path)

private theorem population_same (xs : List Address) : population xs true = population xs false := by
  simp only [population,senior_same]

private theorem hands_project (xs : List Address) (z rev : Bool) :
    RingRetainedReferenceGroup.hands (xs.map (·.hit z)) rev =
      (population xs z).map fun h => if rev then h.hand.swap else h.hand := by
  simp only [RingRetainedReferenceGroup.hands,RingRetainedReferenceGroup.group,List.filter_map,
    List.any_map,List.map_map,population,Function.comp_def,Address.hit]

private structure Profile where
  unit : PairedBranch
  hits : List Address
  localR : PairedBranch
  localS : PairedBranch
  lower : PairedBranch
  fixedR : PairedBranch
  fixedS : PairedBranch

private def Profile.get (p : Profile) (z : Bool) : ArmProfile :=
  ⟨p.unit.get z,p.hits.map (·.hit z),p.localR.get z,p.localS.get z,p.lower.get z,p.fixedR.get z,p.fixedS.get z⟩

private def joinHits (v : Option Labels) (cs : List Profile) : List Address :=
  ((RingNestedActivePair.upper (v.map Prod.fst)).map (Address.mk [])).toList ++
    cs.flatMap fun c => c.hits.map fun h => {h with path := c.unit :: h.path}

private theorem hits_project (v : Option Labels) (cs : List Profile) (z : Bool) :
    (joinHits v cs).map (·.hit z) =
      RingRetainedReferenceGroup.joinHits v ((cs.map (·.get z)).map fun p => (p.unit,p.hits)) := by
  unfold joinHits RingRetainedReferenceGroup.joinHits
  rw [List.map_append]
  apply congrArg₂ List.append
  · cases h : RingNestedActivePair.upper (v.map Prod.fst) <;>
      change _ = ((RingNestedActivePair.upper (v.map Prod.fst)).map (Hit.mk [])).toList <;> rw [h] <;> rfl
  · simp only [List.map_flatMap,List.flatMap_map,List.map_map]
    apply List.flatMap_congr
    intro c _
    change _ = (c.hits.map (·.hit z)).map (fun h => {h with path := (c.unit.get z).deep :: h.path})
    simp only [List.map_map]
    rfl

private def Profile.assemble (k : Basis) (v : Option Labels) (cs : List Profile) : Profile :=
  let u := unitBranch k (RingNestedActivePair.unit (v.map Prod.fst)) (cs.map Profile.unit)
  let loc (s : RS) (child : Profile → PairedBranch) :=
    extend u ((Observation.pairing s).value v false) (cs.map child)
  let lo := extend u (Observation.lowercase.value v false) (cs.map Profile.lower)
  let fixed (s : RS) (child : Profile → PairedBranch) :=
    extend lo ((Observation.pairing s).value v false) (cs.map child)
  ⟨u,joinHits v cs,loc .R Profile.localR,loc .S Profile.localS,lo,fixed .R Profile.fixedR,fixed .S Profile.fixedS⟩

private theorem assemble_project (k : Basis) (v : Option Labels) (cs : List Profile) (z : Bool) :
    (Profile.assemble k v cs).get z = RingGroupedStereo.assemble (k.key z) v (cs.map (·.get z)) := by
  simp only [Profile.get,Profile.assemble,unit_project,extend_project,hits_project,
    RingGroupedStereo.assemble,List.map_map]
  rfl

private def Entry := Profile × PairedBranch

private def render (e : Entry) (z : Bool) : RingGroupedMark.Entry := (e.1.get z,e.2.get z)

private def join (k : Basis) (v : Option Labels) (mark : Nat) (cs : List Entry) : Entry :=
  let p := Profile.assemble k v (cs.map Prod.fst)
  (p,extend p.lower mark (cs.map Prod.snd))

private theorem join_project {i : Input} (q : Arm i) (atom : Nat) (k : Basis) (v : Option Labels)
    (cs : List Entry) (z : Bool) :
    render (join k v (RingGroupedMark.bit atom q) cs) z =
      RingGroupedMark.join atom q (k.key z) v (cs.map (fun e => render e z)) := by
  simp only [render,join,RingGroupedMark.join,assemble_project,extend_project,List.map_map]
  change (_,RingRetainedStereoRefinement.extend _ _ _ _) = _
  rw [show ((Profile.assemble k v (cs.map Prod.fst)).lower.get z) =
      (RingGroupedStereo.assemble (k.key z) v ((cs.map Prod.fst).map (·.get z))).lower
    from congrArg ArmProfile.lower (assemble_project ..)]
  simp only [List.map_map]
  rfl

/-- Every constitutional read inside the marked and unmarked stereo trees
comes from a fresh zero-duplicate-mass expansion. -/
def arm? (i : Input) (read : Reader i) (atom : Nat) (q : Arm i) :=
  RingGroupedMark.build i read atom (RingZeroDuplicateMass.rebuiltKey? i)
    i.certified.executableLocalizedRerootChildren (i.certified.localizedRerootCursorBudget q + 1) q

private def indexedArm (i : Input) (read : Reader i) (atom : Nat) (q : Arm i) :=
  let slice := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  RingGroupedMark.build i read atom (RingZeroDuplicateMass.rebuiltWith i slice.reader)
    (fun c => (slice.reader.readChildren c).getD []) (i.certified.localizedRerootCursorBudget q + 1) q

@[csimp] private theorem indexed_eq : @arm? = @indexedArm := by
  funext i r atom q
  dsimp only [indexedArm,arm?]
  rw [RingZeroDuplicateMass.rebuiltWith_eq]
  congr 2
  funext c; rw [LocalizedRerootChildReader.readChildren_eq]; rfl

private theorem collect {α : Type} {old newRead : α → Option RingGroupedMark.Entry} {xs : List α} {ys}
    (hit : xs.mapM old = some ys)
    (each : ∀ c ∈ xs, ∀ {y}, old c = some y → ∃ w : Entry, render w false = y ∧ newRead c = some (render w true)) :
    ∃ ws : List Entry, ws.map (fun w => render w false) = ys ∧ xs.mapM newRead = some (ws.map (fun w => render w true)) := by
  induction xs generalizing ys with
  | nil => exact ⟨[],Option.some.inj hit,rfl⟩
  | cons c cs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨y,hy,tail⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨ys,hys,out⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj out
    obtain ⟨w,hw,hnew⟩ := each c List.mem_cons_self hy
    obtain ⟨ws,hs,hn⟩ := ih hys fun t ht => each t (List.mem_cons_of_mem _ ht)
    exact ⟨w::ws,by simp [hw,hs],by simp [List.mapM_cons,hnew,hn]⟩

private theorem coupled {i : Input} (r : Reader i) (atom : Nat) :
    ∀ n (q : Arm i) {old}, i.certified.LocalizedRerootCursorValid q →
    RingGroupedMark.build i r atom (RingRetainedChemicalTrace.key? i) i.certified.executableLocalizedRerootChildren n q = some old →
    ∃ e : Entry, render e false = old ∧
      RingGroupedMark.build i r atom (RingZeroDuplicateMass.rebuiltKey? i) i.certified.executableLocalizedRerootChildren n q =
        some (render e true) := by
  intro n
  induction n with
  | zero => intros; contradiction
  | succ n ih =>
    intro q old valid hit
    unfold RingGroupedMark.build at hit
    obtain ⟨v,seen,rest⟩ := Option.bind_eq_some_iff.mp hit
    dsimp only at rest
    obtain ⟨_,gate,rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨k,hk,rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨cs,hcs,out⟩ := Option.bind_eq_some_iff.mp rest
    obtain rfl := Option.some.inj out
    obtain ⟨t,ht,rel⟩ := RingZeroDuplicateMass.rebuilt_corresponds valid hk
    obtain ⟨es,hOld,hNew⟩ := collect hcs fun c hc _ h => ih c
      (i.certified.localizedRerootChild_valid q c _ (i.certified.executableLocalizedRerootChildren_declarative q) hc) h
    let base : Basis := ⟨k,t,rel⟩
    refine ⟨join base v (RingGroupedMark.bit atom q) es,?_,?_⟩
    · rw [join_project,hOld]; rfl
    · rw [join_project]
      unfold RingGroupedMark.build
      simp only [seen,gate,ht,hNew,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
      rfl

private theorem arm_coupled {i r atom q old} (valid : i.certified.LocalizedRerootCursorValid q)
    (found : RingGroupedMark.arm? i r atom q = some old) :
    ∃ w : Entry, render w false = old ∧ arm? i r atom q = some (render w true) :=
  coupled r atom _ q valid found

private def Profile.on (p : Profile) (rev : Bool) : Profile :=
  if rev then {p with localR := p.localS,localS := p.localR,fixedR := p.fixedS,fixedS := p.fixedR} else p

private theorem Profile.on_get (p : Profile) (rev z : Bool) : (p.on rev).get z =
    (if rev then (p.get z).reflect else p.get z) := by cases rev <;> rfl

private theorem refs_same (p : Profile) (rev : Bool) :
    RingRetainedReferenceGroup.references (p.get true).hits rev =
      RingRetainedReferenceGroup.references (p.get false).hits rev := by
  simp only [RingRetainedReferenceGroup.references,Profile.get,hands_project,population_same]

private theorem local_nonterminal (p : Profile) (s : RS) :
    ((p.get true).localPair s).nonterminalStream = ((p.get false).localPair s).nonterminalStream := by
  cases s <;> rfl

private theorem accept_fixed (p : Profile) (s : RS) :
    RingRetainedStereoDecision.accepted (p.get true).unit ((p.get true).fixedPair s) =
    RingRetainedStereoDecision.accepted (p.get false).unit ((p.get false).fixedPair s) := by cases s <;> rfl

private theorem local_key (p : Profile) (rev : Bool) :
    RingGroupedRanking.localKey (p.get true) rev = RingGroupedRanking.localKey (p.get false) rev := by
  simp only [RingGroupedRanking.localKey,refs_same,local_nonterminal]
  split <;> rfl

private theorem stereo_key (p : Profile) (rev : Bool) :
    RingGroupedRanking.stereoKey (p.get true) rev = RingGroupedRanking.stereoKey (p.get false) rev := by
  simp only [RingGroupedRanking.stereoKey,local_key,accept_fixed]
  rfl

private theorem local_score (p q : Profile) (rev : Bool) :
    RingRetainedStereoDecision.fourB? (p.get true) (q.get true) rev =
      RingRetainedStereoDecision.fourB? (p.get false) (q.get false) rev := by
  simp only [RingRetainedStereoDecision.fourB?,refs_same,RingRetainedStereoRefinement.pairSign,local_nonterminal]
  split <;> rfl

private theorem decision (p q : Profile) (rev : Bool) :
    RingRetainedStereoDecision.decide? (p.get true) (q.get true) rev =
    RingRetainedStereoDecision.decide? (p.get false) (q.get false) rev := by
  simp only [RingRetainedStereoDecision.decide?,local_score,RingRetainedStereoDecision.seedSign,accept_fixed]
  rfl

attribute [local instance] lexOrd

private theorem full_key (p q : Profile) (rev : Bool) :
    compare (RingGroupedRanking.key (p.get true) rev) (RingGroupedRanking.key (q.get true) rev) =
    compare (RingGroupedRanking.key (p.get false) rev) (RingGroupedRanking.key (q.get false) rev) := by
  have base : compare (p.get true).unit.priorDeep (q.get true).unit.priorDeep =
      compare (p.get false).unit.priorDeep (q.get false).unit.priorDeep := by
    change compare (_ ++ _) (_ ++ _) = compare (_ ++ _) (_ ++ _)
    rw [cmp_append (orderWord (p.unit.basis.key true)) (orderWord (q.unit.basis.key true)) _ _ rfl,
      cmp_append (orderWord (p.unit.basis.key false)) (orderWord (q.unit.basis.key false)) _ _ rfl]
    exact congrArg (fun v : Ordering => v.then _) (p.unit.basis.related.orders q.unit.basis.related).2
  change (compare (p.get true).unit.priorDeep (q.get true).unit.priorDeep).then
    (compare (RingGroupedRanking.stereoKey (p.get true) rev) (RingGroupedRanking.stereoKey (q.get true) rev)) = _
  rw [base,stereo_key,stereo_key]
  rfl

private theorem read_both {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (atom : Nat) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    ∃ e : Entry, arm? i r atom q = some (render e true) ∧
      RingGroupedMark.arm? i r atom q = some (render e false) ∧ RingGroupedStereo.arm? i r q = some (e.1.get false) := by
  obtain ⟨old,found⟩ := RingGroupedMark.arm_ready ready atom q valid on
  obtain ⟨e,eqn,got⟩ := arm_coupled valid found
  subst old
  exact ⟨e,got,found,(RingGroupedStereo.arm_iff_reads q valid _).mpr (RingGroupedMark.arm_source found).1⟩

/-- Each constructor names the child priority consumed by a stereo pass. -/
inductive Stage where
  | unit | localPair (hand : RS) | lower | fixedPair (hand : RS) | marked

def Stage.branch (stage : Stage) (entry : RingGroupedMark.Entry) : Branch :=
  match stage with
  | .unit => entry.1.unit
  | .localPair s => entry.1.localPair s
  | .lower => entry.1.lower
  | .fixedPair s => entry.1.fixedPair s
  | .marked => entry.2

private def Stage.paired (stage : Stage) (e : Entry) : PairedBranch :=
  match stage with
  | .unit => e.1.unit
  | .localPair .R => e.1.localR
  | .localPair .S => e.1.localS
  | .lower => e.1.lower
  | .fixedPair .R => e.1.fixedR
  | .fixedPair .S => e.1.fixedS
  | .marked => e.2

private theorem Stage.project (s : Stage) (e : Entry) (z : Bool) :
    s.branch (render e z) = (s.paired e).get z := by
  cases s <;> first | rfl | rename_i hand; cases hand <;> rfl

/-- Sort actual identifiers with the same shallow or deep sort as the recursive
pass. Identifiers can repeat and never enter the comparison. -/
def orderedSites {α : Type} (s : Stage) (deep : Bool) (key : α → RingGroupedMark.Entry) (xs : List α) :=
  if deep then order (fun a => (s.branch (key a)).deep) xs
  else order (fun a => (s.branch (key a)).shallow) xs

/-- Any list of identified visits with successful molecular reads retains its
exact order at every pass. A caller can use a finite type of list positions
to distinguish separate visits to the same cursor. -/
theorem ordered_sites_agree {i : Input} {r : Reader i} {α : Type} (atom : Nat)
    (cursorAt : α → Arm i) (valid : ∀ a, i.certified.LocalizedRerootCursorValid (cursorAt a))
    (newKey oldKey : α → RingGroupedMark.Entry)
    (hn : ∀ a, arm? i r atom (cursorAt a) = some (newKey a))
    (ho : ∀ a, RingGroupedMark.arm? i r atom (cursorAt a) = some (oldKey a))
    (s : Stage) (deep : Bool) (xs : List α) : orderedSites s deep newKey xs = orderedSites s deep oldKey xs := by
  choose es old newRead using fun a => arm_coupled (valid a) (ho a)
  have newEq (a : α) := Option.some.inj ((hn a).symm.trans (newRead a))
  cases deep <;> simp only [orderedSites,Bool.false_eq_true,if_false,if_true,order] <;>
    apply congrArg (fun cmp => xs.mergeSort cmp) <;> funext a b
  · have h := shallow_cmp (s.paired (es a)) (s.paired (es b))
    simp only [newEq,← old,s.project,← not_lt,← natList_lt,h]
  · have h := deep_cmp (s.paired (es a)) (s.paired (es b))
    simp only [newEq,← old,s.project,← not_lt,← deep_lt,h]

/-- One flag per reference occurrence, in the native molecular traversal order.
Equal paths retain each tied occurrence at its original position. -/
def retainedMask (hits : List Hit) :=
  hits.map fun h => !(hits.any fun other => RingRetainedReferenceGroup.senior other.path h.path)

private theorem mask_same (p : Profile) : retainedMask (p.get true).hits = retainedMask (p.get false).hits := by
  simp only [retainedMask,Profile.get,List.map_map,List.any_map,Function.comp_def,senior_same]

/-- Native occurrence enumeration is unchanged. These rows record the length,
hand and ordering against every other reference path, including every tie. -/
def referenceRows (hits : List Hit) := hits.map fun h =>
  (h.path.length,h.hand,hits.map fun other => compare h.path other.path)

private theorem reference_rows (p : Profile) :
    referenceRows (p.get true).hits = referenceRows (p.get false).hits := by
  simp only [referenceRows,Profile.get,List.map_map,Function.comp_def,Address.hit,List.length_map,path_cmp]

/-- Stereo data that downstream rules actually compare. Exposing both sets
of words also distinguishes a Rule 4b tie from a later Rule 5 decision. -/
def stereoWords (p : ArmProfile) :=
  (p.unit.word,p.localR.word,p.localS.word,p.lower.word,p.fixedR.word,p.fixedS.word)

/-- Applies to every valid molecular cursor on the same original root.
No particular seed, successful branch calculation or matching path is assumed. -/
theorem arm_invariants {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (atom : Nat) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    ∃ newArm oldArm, arm? i r atom q = some newArm ∧ RingGroupedMark.arm? i r atom q = some oldArm ∧
      stereoWords newArm.1 = stereoWords oldArm.1 ∧ newArm.2.word = oldArm.2.word ∧
      referenceRows newArm.1.hits = referenceRows oldArm.1.hits ∧
      retainedMask newArm.1.hits = retainedMask oldArm.1.hits ∧
      ∀ rev, RingRetainedReferenceGroup.hands newArm.1.hits rev = RingRetainedReferenceGroup.hands oldArm.1.hits rev := by
  obtain ⟨e,hn,ho,_⟩ := read_both ready atom q valid on
  refine ⟨_,_,hn,ho,rfl,rfl,reference_rows _,mask_same _,?_⟩
  intro rev
  simp only [render,Profile.get,hands_project,population_same]

open RingRetainedStereoDecision (Result)
private def mirrored (rev : Bool) (p : ArmProfile) := if rev then p.reflect else p

def comparison? (i : Input) (f a b : Site i) (r : Reader i) : Option (Result × Result) := do
  let prior ← RingZeroDuplicateMass.compareAt? i f a b
  guard (prior == .eq)
  let x ← arm? i r 0 ⟨a,some f⟩
  let y ← arm? i r 0 ⟨b,some f⟩
  return (← RingRetainedStereoDecision.decide? x.1 y.1 false,
    ← RingRetainedStereoDecision.decide? x.1.reflect y.1.reflect true)

theorem comparison_agrees (i : Input) (f a b : Site i) (r : Reader i) (ready : RingGroupedStereo.Ready f r) :
    comparison? i f a b r = RingGroupedStereo.comparison? i f a b r := by
  unfold comparison? RingGroupedStereo.comparison?
  rw [RingZeroDuplicateMass.compareAt_agrees]
  cases h : RingRetainedChemicalTrace.compareAt? i f a b with
  | none => rfl
  | some t =>
    by_cases tie : cipTraceOutcome t = .eq
    · have inc := (RingRetainedChemicalTrace.compareAt?_source h).1
      have valid (c : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent c.val f.val) :
          i.certified.LocalizedRerootCursorValid (⟨c,some f⟩ : Arm i) :=
        (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨c.property,adj⟩
      obtain ⟨x,nx,_,ox⟩ := read_both ready 0 _ (valid a inc.2.2.1) inc.2.2.1.1
      obtain ⟨y,ny,_,oy⟩ := read_both ready 0 _ (valid b inc.2.2.2) inc.2.2.2.1
      have mirror := decision (x.1.on true) (y.1.on true) true
      simp only [Profile.on_get,if_true] at mirror
      simp [tie,nx,ny,ox,oy,render,decision,mirror]
    · simp [tie,guard]

open RingActivePairReport (Slot)
open RingNestedActivePair (Frame)
open RingGeometryCriterion (Signature)
open RingGroupedCentre (Arms cursor)

/-- A strict order gives its parity. Equality at any unordered pair
makes the orientation zero. -/
private def parity (cmp : Slot → Slot → Ordering) : Int :=
  let pairs := LocalizedChemicalRing.ConstitutionalPartition.pairs
  if pairs.any (fun p => cmp p.1 p.2 == .eq) then 0
  else if pairs.countP (fun p => cmp p.1 p.2 == .lt) % 2 = 0 then 1 else -1

private def signatureFrom (base : Int) (cmp : Bool → Slot → Slot → Ordering)
    (words : Slot → Slot → Word) : Signature :=
  let slots := List.finRange 4
  let marks := slots.filter fun j => slots.any fun k => j != k && cmp false j k == .eq
  let index := if marks.length < 3 then parity (cmp false) else
    (marks.map fun s => parity fun j k => (cmp false j k).then (compare (words s j) (words s k))).sum
  let crossings := LocalizedChemicalRing.ConstitutionalPartition.pairs.countP fun p =>
    (cmp false p.1 p.2 == .gt) != (cmp true p.1 p.2 == .gt)
  ⟨base * index,crossings⟩

private theorem signatureFrom_old {i f fr r} (a : @Arms i f fr r) :
    signatureFrom (RingOrientation.baseline fr) (fun rev j k => compare (a.key rev j) (a.key rev k))
      (RingOrientation.markedWord fr r) = ⟨RingOrientation.baseline fr * RingOrientation.index a,RingGeometryCriterion.reversals a⟩ := by
  have eqn (j k : Slot) :
      (compare (a.key false j) (a.key false k) == .eq) = (a.key false j == a.key false k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Std.compare_eq_eq_iff_eq]
  simp only [signatureFrom,eqn,RingGroupedOrders.marks,RingOrientation.index,RingGeometryCriterion.reversals]
  rfl

/-- Build all four unmarked priorities once. A Rule 6 trial also rebuilds
its through-4c child ranks before it assembles its marked word. -/
def signature? (i : Input) (f : Site i) (r : Reader i) : Option Signature := do
  let fr ← RingNestedActivePair.frame? i f
  let ps ← RingActivePairReport.four? fun k => (arm? i r 0 (cursor fr k)).map Prod.fst
  let key rev k := RingGroupedRanking.key (mirrored rev (ps k)) rev
  let word s k := ((arm? i r (RingGroupedTrials.atom fr s) (cursor fr k)).map (fun e => e.2.word)).getD []
  return signatureFrom (RingOrientation.baseline fr) (fun rev j k => compare (key rev j) (key rev k)) word

theorem signature_agrees (i : Input) (f : Site i) (r : Reader i) (ready : RingGroupedStereo.Ready f r) :
    signature? i f r = RingGeometryCriterion.signature? i f r := by
  unfold signature? RingGeometryCriterion.signature?
  cases frame : RingNestedActivePair.frame? i f with
  | none => rfl
  | some fr =>
    obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready fr ready)
    have atSlot (k : Slot) := read_both ready 0 (cursor fr k) (RingGroupedCentre.valid fr k) (fr.direction k).property.1
    choose es en _ eo using atSlot
    let readArm (k : Slot) := (arm? i r 0 (cursor fr k)).map Prod.fst
    have get (k : Slot) : readArm k = some ((es k).1.get true) := by simp [readArm,en,render]
    obtain ⟨ps,hp⟩ := Option.isSome_iff_exists.mp (RingActivePairReport.four_full readArm fun k =>
      Option.isSome_iff_exists.mpr ⟨_,get k⟩)
    have got (k : Slot) := Option.some.inj ((RingActivePairReport.four_at hp k).symm.trans (get k))
    have old (k : Slot) := Option.some.inj ((a.computed k).symm.trans (eo k))
    have keys (rev : Bool) (j k : Slot) :
        compare (RingGroupedRanking.key (mirrored rev (ps j)) rev) (RingGroupedRanking.key (mirrored rev (ps k)) rev) =
          compare (a.key rev j) (a.key rev k) := by
      have same := full_key ((es j).1.on rev) ((es k).1.on rev) rev
      simp only [Profile.on_get] at same
      simpa only [RingGroupedCentre.Arms.key,old,got,mirrored] using same
    have words (s k : Slot) :
        ((arm? i r (RingGroupedTrials.atom fr s) (cursor fr k)).map (fun e => e.2.word)).getD [] =
          RingOrientation.markedWord fr r s k := by
      obtain ⟨e,hn,ho,_⟩ := read_both ready (RingGroupedTrials.atom fr s) _ (RingGroupedCentre.valid fr k) (fr.direction k).property.1
      simp only [RingOrientation.markedWord,hn,ho,Option.map_some,Option.getD_some]
      rfl
    change (RingActivePairReport.four? readArm >>= _) = _
    rw [hp]
    simp only [ha,Option.bind_eq_bind,Option.bind_some,Option.pure_def,keys,words,signatureFrom_old]


open RingActiveDistanceSchedule (View Cell evaluate frozen)
open RingSphereQueue (SkipsNoncentres finalCell molecularQueue)

/-- Every constitutional gate, every stereo sibling rank, and every trial
word use rebuilt keys. Only the already-published descriptor cells are frozen. -/
def publish (i : Input) (f : Site i) (r : Reader i) : Cell :=
  if i.certified.localizedOccurrenceDescriptorCenter? f = none then some none
  else match RingZeroMassReport.zeroEarly? i f with
    | some s => some s.letters
    | none => (signature? i f r).map Signature.letters

theorem state_exact (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    evaluate (publish i) = RingGroupedPublication.state i := by
  have geom : evaluate (RingGeometryCriterion.rule i) = RingGroupedPublication.state i :=
    (RingActiveDistanceSchedule.snapshot_table ..).symm.trans (RingGeometryCriterion.state_eq coords)
  symm
  apply RingActiveDistanceSchedule.unique
  intro f
  have law := RingActiveDistanceSchedule.evaluate_eq (RingGeometryCriterion.rule i) f
  rw [geom] at law
  unfold publish
  by_cases absent : i.certified.localizedOccurrenceDescriptorCenter? f = none
  · simpa only [if_pos absent,RingGeometryCriterion.rule] using law
  · rw [if_neg absent]
    cases h : RingZeroMassReport.zeroEarly? i f with
    | some s => exact RingSphereQueue.early_exact coords ((RingZeroMassReport.zero_early_exact i f).symm.trans h)
    | none =>
      rw [signature_agrees i f _ (RingGroupedPublication.ready (RingGroupedGeometry.physical coords) f)]
      simpa only [RingGeometryCriterion.rule,if_neg absent] using law

private theorem skips (i : Input) : SkipsNoncentres (publish i) := by
  intro f r h
  simp only [publish,if_pos h]

def root (i : Input) (a : i.certified.Atom) : Cell :=
  match RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a) with
  | some s => some s.letters
  | none => finalCell (publish i) a (molecularQueue i a)

theorem root_exact (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) : root i a = RingGroupedPublication.state i (RingGroupedReport.origin i a) := by
  unfold root
  cases hit : RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a) with
  | some s => exact (RingSphereQueue.early_exact coords ((RingZeroMassReport.zero_early_exact i _).symm.trans hit)).symm
  | none => rw [RingSphereQueue.final_exact (skips i) (RingSphereQueue.inventory i a),state_exact i coords]

def report? (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (root i a).map fun v => (a.val,v)

theorem report_exact (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : report? i atoms = RingGroupedReport.forAtoms? i atoms := by
  unfold report?
  simp only [root_exact i coords]
  rfl

theorem frozen_scores (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (f a b : Site i) :
    let r := frozen (evaluate (publish i)) f
    comparison? i f a b r = RingGroupedStereo.comparison? i f a b (frozen (RingGroupedPublication.state i) f) := by
  rw [state_exact i coords]
  exact comparison_agrees i f a b _ (RingGroupedPublication.ready (RingGroupedGeometry.physical coords) f)

end TetraStereo.Engine.RingRebuiltStereo

assert_kernel_only TetraStereo.Engine.RingRebuiltStereo.ordered_sites_agree
assert_kernel_only TetraStereo.Engine.RingRebuiltStereo.arm_invariants
assert_kernel_only TetraStereo.Engine.RingRebuiltStereo.frozen_scores
assert_kernel_only TetraStereo.Engine.RingRebuiltStereo.signature_agrees
assert_kernel_only TetraStereo.Engine.RingRebuiltStereo.state_exact
assert_kernel_only TetraStereo.Engine.RingRebuiltStereo.report_exact
