import TetraStereo.Examples.CrossParentSphereWords
import TetraStereo.Examples.CrossParentClasses
import TetraStereo.Examples.CrossParentRootOrder

/-! Reconstruct all four bit readings of the two nitrogen arms from the
eight independent physical donor hands. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentPublicWords
open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingFullPathPairs (Oracle FullVisit stepKey)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingGroupedCentre (cursor)
open RingGroupedReport (origin)
open RingGroupedTrials (atom)
open AntipodalCyclohexaneWords (EdgeHistory histories Rooted children expansion_histories)
open CrossParentDonorStore (molecule ligandRow)
open CrossParentClasses (AtLevel publicRead prefixHistory)
open CrossParentRootOrder (countWord donor donors)
open DecalinAuxiliary (history)
open CrossParentSphereWords (sortedBits)
open private start from TetraStereo.Examples.DecalinRootWords
open private related_of_mem from TetraStereo.Engine.RingFullPathPairs

private inductive Place where
  | arm (left : Bool)
  | fork (j : Fin 4)
  | tip (j : Fin 8)
  | leaf (j : Fin 8) (k : Fin 3)
  deriving DecidableEq

private def level : Place → Nat | .arm _ => 0 | .fork _ => 1 | .tip _ => 2 | .leaf .. => 3
private def representative : Place → Fin 8
  | .arm l => donor l 0 | .fork j => Fin.ofNat 8 (2*j.val) | .tip j | .leaf j _ => j
private def path : Place → List Nat
  | .arm l => [if l then 1 else 2,0]
  | .fork j => [3+j.val,1+j.val/2,0]
  | .tip j => CrossParentClasses.route j
  | .leaf j k => (15+3*j.val+k.val)::CrossParentClasses.route j
private def edge (p : Place) : EdgeHistory := ((path p).tail,path p)
private def locate (e : EdgeHistory) : Place :=
  let n := e.2.headD 0
  if n < 3 then .arm (n == 1) else if n < 7 then .fork (Fin.ofNat 4 (n-3))
  else if n < 15 then .tip (Fin.ofNat 8 (n-7))
  else .leaf (Fin.ofNat 8 ((n-15)/3)) (Fin.ofNat 3 ((n-15)%3))
private def kids : Place → List Place
  | .arm l => (List.finRange 2).map fun k => .fork (Fin.ofNat 4 ((if l then 0 else 2)+k.val))
  | .fork j => (List.finRange 2).map fun k => .tip (Fin.ofNat 8 (2*j.val+k.val))
  | .tip j => (List.finRange 3).map (.leaf j)
  | .leaf .. => []

private def tag : Place → Option (Fin 8) | .tip j => some j | _ => none
private theorem tables (p : Place) :
    locate (edge p) = p ∧ (children molecule (edge p)).Perm ((kids p).map edge) ∧
    (∀ c ∈ kids p, level c = level p+1) ∧
    CrossParentClasses.donor? (path p) = tag p ∧
    (∀ n : Fin 3, level p = n.val → path p = prefixHistory (representative p) n) := by
  cases p with
  | arm l => cases l <;> decide +kernel
  | fork j => fin_cases j <;> decide +kernel
  | tip j => fin_cases j <;> decide +kernel
  | leaf j k => fin_cases j <;> fin_cases k <;> decide +kernel

private theorem written : AntipodalCyclohexaneHands.HistoryPriority.GraphFacts molecule := by
  unfold AntipodalCyclohexaneHands.HistoryPriority.GraphFacts
  decide +kernel

private def bitOfHand (rev : Bool) (seed h : RS) := (if rev then h.swap else h) == seed
private def emit (hands : Fin 8 → RS) (rev : Bool) (seed : RS) (p : Place) :=
  (tag p).map fun j => bitOfHand rev seed (hands j)

/-- The root, two forks, and four donors have common prefixes within each
depth; after the donors, all physical terminals are silent. -/
private def Form (parent tip : List Word) (n : Nat) (bit : Option Bool) (p : Path) : Prop :=
  match n with
  | 0 => p = [stepKey [] none]
  | 1 => p = [stepKey [] none,stepKey parent none]
  | 2 => p = [stepKey [] none,stepKey parent none,stepKey tip bit]
  | _ => True

private theorem sufficient (n : Place) (hands : Fin 8 → RS) (rev : Bool) (seed : RS)
    {b : Bool} (h : emit hands rev seed n = some b) : level n = 2 := by
  cases n <;> simp_all [emit,tag,level]

private theorem observed_none (p : Place) (hands : Fin 8 → RS) (rev : Bool) (seed : RS)
    (h : level p ≠ 2) : emit hands rev seed p = none := by
  cases p <;> simp_all [emit,tag,level]

private theorem bit_strict (parent tip : List Word) :
    ([stepKey [] none,stepKey parent none,stepKey tip (some false)] : Path) <
      [stepKey [] none,stepKey parent none,stepKey tip (some true)] := by
  apply List.Lex.cons
  apply List.Lex.cons
  apply List.Lex.rel
  apply List.append_left_lt
  decide

private def whereAt {i : Input} (v : FullVisit i) := locate (histories v.cursor)

private structure Located {i : Input} (root : i.certified.Atom) (v : FullVisit i) : Prop where
  rooted : Rooted root v
  previous : ∀ p, v.cursor.previous? = some p → p.val.root = root
  exactEdge : histories v.cursor = edge (whereAt v)

private theorem atLevel {i : Input} {root : i.certified.Atom} {v : FullVisit i} (here : Located root v)
    (n : Fin 3) (depth : level (whereAt v) = n.val) :
    AtLevel root v.cursor (representative (whereAt v)) n := by
  obtain ⟨_,on,p,hp⟩ := here.rooted
  have pos := (tables _).2.2.2.2 n depth
  have h := here.exactEdge
  change (v.cursor.previous?.elim [] history,history v.cursor.occurrence) = _ at h
  rw [hp] at h
  exact ⟨on,(congrArg Prod.snd h).trans pos,p,hp,here.previous _ hp,
    (congrArg Prod.fst h).trans (congrArg List.tail pos)⟩

private theorem bits {i : Input} (raw : i.molecule = molecule) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0) (hands : Fin 8 → RS)
    (signs : ∀ j, readback? (RingWrittenPHReadings.geometry i.spatial) (ligandRow j) = some (hands j))
    (rev : Bool) (seed : RS) (v : FullVisit i) (here : Located root v) :
    RingFullPathPairs.likeAt i (publicRead i root) rev seed v.cursor = emit hands rev seed (whereAt v) := by
  change (RingFullPathPairs.handAt i _ rev _).map _ = _
  rw [CrossParentClasses.handAt_eq raw ok root zero _ here.rooted.2.1 rev,
    show history v.cursor.occurrence = path (whereAt v) from congrArg Prod.snd here.exactEdge,(tables _).2.2.2.1]
  unfold emit
  cases tag (whereAt v) with
  | none => rfl
  | some j =>
    have observed : CrossParentClasses.measured i.spatial j = some (hands j) := signs j
    simp [CrossParentClasses.hand,observed,bitOfHand]


private theorem sample (left : Bool) :
    let a := [Place.arm left]
    let b := a.flatMap kids
    let c := b.flatMap kids
    let d := c.flatMap kids
    a.filterMap tag = [] ∧ b.filterMap tag = [] ∧ c.filterMap tag = (List.finRange 4).map (donor left) ∧
      d.filterMap tag = [] ∧ d.flatMap kids = [] := by cases left <;> decide +kernel

private theorem count_bits (hs : List RS) (rev : Bool) (seed : RS) :
    let nr := hs.count .R
    let yesR := if rev then hs.length-nr else nr
    let yes := if seed = .R then yesR else hs.length-yesR
    ((hs.map (bitOfHand rev seed)).count true = yes ∧
      (hs.map (bitOfHand rev seed)).count false = hs.length-yes) := by
  cases rev <;> cases seed <;> induction hs with
  | nil => decide
  | cons h hs ih =>
    have bound : hs.count .R ≤ hs.length := List.count_le_length
    cases h <;> simp_all [bitOfHand,RS.swap,List.count_cons] <;> omega

private theorem expected (hands : Fin 8 → RS) (left rev : Bool) (seed : RS) :
    CrossParentSphereWords.word? kids (emit hands rev seed) 4 [.arm left] = some (countWord hands left rev seed) := by
  obtain ⟨a,b,c,d,e⟩ := sample left
  have observed (row : List Place) : row.filterMap (emit hands rev seed) =
      (row.filterMap tag).map (fun j => bitOfHand rev seed (hands j)) := by rw [List.map_filterMap]; rfl
  simp only [CrossParentSphereWords.word?,observed,a,b,c,d,e,List.isEmpty_nil,if_true,List.map_nil,
    Option.map_some]
  have mapped : (((List.finRange 4).map (donor left)).map (fun j => bitOfHand rev seed (hands j))) =
      (donors hands left).map (bitOfHand rev seed) := by simp [donors,List.map_map,Function.comp_def]
  have counts := count_bits (donors hands left) rev seed
  have width : (donors hands left).length = 4 := by simp [donors]
  dsimp only at counts
  rw [width] at counts
  simp [sortedBits,mapped,counts.1,counts.2,countWord,CrossParentRootOrder.rCount]

private theorem uniform {i : Input} (raw : i.molecule = molecule) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) (stage : os = [] ∨ os = [.lowercase]) :
    ∃ prior : Fin 3 → List Word, ∀ (n : Fin 3) (q : Arm i) (j : Fin 8), AtLevel root q j n →
      ∀ k, RingRetainedStereoRefinement.priority i (publicRead i root) rev os q = some k → k.deep = prior n := by
  classical
  suffices ∀ n : Fin 3, ∃ w : List Word, ∀ (q : Arm i) (j : Fin 8), AtLevel root q j n →
      ∀ k, RingRetainedStereoRefinement.priority i (publicRead i root) rev os q = some k → k.deep = w by
    choose f hf using this
    exact ⟨f,hf⟩
  intro n
  by_cases any : ∃ (q : Arm i) (j : Fin 8) (k : RingStereoSiblingPass.Branch), AtLevel root q j n ∧
      RingRetainedStereoRefinement.priority i (publicRead i root) rev os q = some k
  · obtain ⟨q,j,k,atQ,hq⟩ := any
    exact ⟨k.deep, fun a t atA b hb => congrArg RingStereoSiblingPass.Branch.deep
      (CrossParentClasses.priority_eq raw ok root zero a q t j n atA atQ rev os stage hb hq)⟩
  · exact ⟨[],fun q j atQ k hk => (any ⟨q,j,k,atQ,hk⟩).elim⟩

private theorem newForm {prior : Fin 3 → List Word} {h c : Place} {p : Path}
    {d : List Word} {hb cb : Option Bool}
    (inc : level c = level h + 1) (parent : Form (prior 1) (prior 2) (level h) hb p)
    (nextSilent : level c ≠ 2 → cb = none)
    (branch : ∀ n : Fin 3, level c = n.val → d = prior n) :
    Form (prior 1) (prior 2) (level c) cb (p ++ [stepKey d cb]) := by
  cases depth : level h with
  | zero =>
    have child : level c = 1 := by omega
    rw [depth] at parent
    rw [child,branch 1 child,nextSilent (by omega)]
    exact congrArg (· ++ [stepKey (prior 1) none]) parent
  | succ m => cases m with
    | zero =>
      have child : level c = 2 := by omega
      rw [depth] at parent
      rw [child,branch 2 child]
      exact congrArg (· ++ [stepKey (prior 2) cb]) parent
    | succ n =>
      rw [inc,depth]
      trivial

/-- On both nitrogen arms all four actual terminal hands form one rank class.
Each seed therefore reads like hands first across both parent atoms. -/
theorem ring_word {i : Input} (raw : i.molecule = molecule) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0) (fr : RingNestedActivePair.Frame i (origin i root))
    (s : Fin 4) (left : Bool) (id : atom fr s = if left then 1 else 2) (hands : Fin 8 → RS)
    (signs : ∀ j, readback? (RingWrittenPHReadings.geometry i.spatial) (ligandRow j) = some (hands j))
    (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (stage : os = [] ∨ os = [.lowercase])
    (seed : RS) : RingFullPathPairs.stageWords i (publicRead i root) rev os seed (cursor fr s) =
      some (countWord hands left rev seed) := by
  let o := RingFullPathPairs.stage i (publicRead i root) rev os
  let bit := RingFullPathPairs.likeAt i (publicRead i root) rev seed
  let mark := emit hands rev seed
  have total := RingOccurrenceStereo.rank_total (RingChemicalGraphProof.ready ok (origin i root)) rev os
  obtain ⟨prior,rank⟩ := uniform raw ok root zero rev os stage
  let D (v : FullVisit i) := Located root v ∧ Form (prior 1) (prior 2) (level (whereAt v)) (mark (whereAt v)) v.path
  have seen (v : FullVisit i) (here : Located root v) : bit v.cursor = mark (whereAt v) :=
    bits raw ok root zero hands signs rev seed v here
  have step (v : FullVisit i) (hv : D v) (ys : List (FullVisit i)) (grow : o.Expansion bit v ys) :
      (ys.map whereAt).Perm (kids (whereAt v)) ∧ ∀ y ∈ ys, D y := by
    obtain ⟨loc,form⟩ := hv
    obtain ⟨paths,sub⟩ := expansion_histories raw written o bit root v loc.rooted ys grow
    rw [loc.exactEdge] at paths
    have walked := paths.trans (tables _).2.1
    have inv (p : Place) : locate (edge p) = p := (tables p).1
    constructor
    · simpa [whereAt,List.map_map,Function.comp_def,inv] using walked.map locate
    · intro y mem
      obtain ⟨p,hp,hy⟩ := List.mem_map.mp (walked.mem_iff.mp (List.mem_map_of_mem (f := fun z => histories z.cursor) mem))
      have pos : whereAt y = p := by change locate (histories y.cursor) = p; rw [←hy,inv]
      obtain ⟨c,inC,k,hk,formed⟩ := related_of_mem grow mem
      have prev : y.cursor.previous? = some v.cursor.occurrence := by
        rw [formed]; exact i.certified.executableLocalizedRerootChildren_previous _ _ inC
      have entry : Located root y := ⟨sub y mem,fun pr he => Option.some.inj (he.symm.trans prev) ▸ loc.rooted.2.1,
        by rw [pos]; exact hy.symm⟩
      refine ⟨entry,?_⟩
      have rankAt (n : Fin 3) (depth : level (whereAt y) = n.val) : k.deep = prior n := by
        have atY := atLevel entry n depth
        obtain ⟨b,hb⟩ := total y.cursor entry.rooted.1 entry.rooted.2.1
        have matchK : b = k := o.unique _ _ _ (o.sound _ _ hb) (formed ▸ hk)
        exact matchK ▸ rank n _ _ atY _ hb
      have name : y.path = v.path ++ [stepKey k.deep (mark (whereAt y))] := by
        rw [←seen y entry,formed]
      rw [name]
      apply newForm (prior := prior) (h := whereAt v) (c := whereAt y) (hb := mark (whereAt v))
        (by rw [pos]; exact (tables _).2.2.1 p hp) form
        (observed_none _ _ _ _) rankAt
  have strong (x y : FullVisit i) (dx : D x) (dy : D y) (f : mark (whereAt x) = some false)
      (t : mark (whereAt y) = some true) : x.path < y.path := by
    have fx := dx.2
    have fy := dy.2
    rw [sufficient _ _ _ _ f,f] at fx
    rw [sufficient _ _ _ _ t,t] at fy
    exact fx ▸ fy ▸ bit_strict (prior 1) (prior 2)
  let initial := Oracle.root bit (cursor fr s)
  have startEdge : histories initial.cursor = edge (.arm left) := by
    change ([root.val],DecalinLigandOrder.history (cursor fr s)) = _
    rw [start,zero,id]
    rfl
  have place : whereAt initial = .arm left := by unfold whereAt; rw [startEdge,(tables _).1]
  have first : Located root initial := by
    refine ⟨⟨RingGroupedCentre.valid fr s,(fr.direction s).property.1,origin i root,rfl⟩,?_,by rw [place]; exact startEdge⟩
    intro p hp
    obtain rfl : p = origin i root := Option.some.inj hp.symm
    rfl
  have initialD : D initial := by
    refine ⟨first,?_⟩
    rw [place]
    change [stepKey [] (bit initial.cursor)] = _
    rw [seen initial first,place]
    rfl
  obtain ⟨w,hit,src⟩ := o.source_exact (f := origin i root) bit total _ (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  obtain ⟨out,walk,rfl⟩ := (src w).mpr rfl
  have graphWord := expected hands left rev seed
  obtain ⟨eq,dom⟩ := CrossParentSphereWords.trace_word (D := fun _ => D) (fun _ => step) mark (fun _ => strong) walk 0 (by simpa using initialD)
    (by simp) 4 [.arm left] _ (by simp [place,initial]) graphWord
  apply hit.trans
  apply congrArg some
  exact (List.filterMap_congr (fun v hv => seen v (dom v hv).choose_spec.1)).trans eq

end TetraStereo.Examples.CrossParentPublicWords
assert_kernel_only TetraStereo.Examples.CrossParentPublicWords.ring_word
