import TetraStereo.Examples.DecalinPathSwap
import TetraStereo.Engine.RingFullPathTrialReadings

/-! The four paths out of a decalin junction, including hydrogen and terminal ring
duplicates. A complete singly labelled arm has the same one-bit Rule 5 word in
every possible scan order. Atom IDs in histories run from the focus outwards
when displayed and in reverse order in the computation. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinLigandOrder
open OneCenter Engine DecalinFrames
open RingFullPathTrialReadings (bitWord)
set_option maxRecDepth 150000
set_option maxHeartbeats 3000000

abbrev History := List Nat
private abbrev Junction := Fin 2

/-- Directly read the two endpoints of each of the 29 written bonds. -/
def adjacent (a : Nat) : List Nat := molecule.writtenNeighbors a

def expand : History → List History
  | a :: b :: tail =>
    if (b :: tail).contains a then []
    else ((adjacent a).filter (· != b)).map fun c => c :: a :: b :: tail
  | _ => []

def layersWith {α : Type} (children : α → List α) (front : List α) : Nat → List α
  | 0 => front
  | n+1 => (layersWith children front n).flatMap children

abbrev sphere := layersWith expand

def census (a b : Nat) : List History :=
  (List.range 12).flatMap (sphere [[b,a]])

def arms (j : Junction) : List Nat := junctionRow j.val

/-- Atom paths are actual paths, not node labels: the same junction occurs on
two long routes and on the direct arm. Only the two long occurrences emit. -/
def firstRoute (j : Junction) : History :=
  if j.val = 0 then [1,3,5,4,2,0] else [0,2,4,5,3,1]

def secondRoute (j : Junction) : History := (firstRoute j).map DecalinPathSwap.exchange

def frozen (j : Junction) (h : RS) (p : History) : Option RS :=
  if p = firstRoute j then some h else if p = secondRoute j then some h.swap else none

def word (j : Junction) (h seed : RS) (ps : List History) : List Bool :=
  ps.filterMap fun p => (frozen j h p).map (· == seed)

private def origin (p : History) : Nat :=
  match p with
  | a :: tail => if tail.contains a then 29 - tail.reverse.idxOf a else 0
  | [] => 0

private def z (a : Nat) : Nat := if a < 10 then 6 else 1

private def insertBy {α : Type} (before : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y::ys => if before x y then x::y::ys else y::insertBy before x ys

private def sortedBy {α : Type} (before : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (insertBy before) []

/-- The first two constitutional rows. The two methylene arms still tie. -/
def heads (j : Junction) (a : Nat) : List Nat :=
  z a :: sortedBy (· ≥ ·) ((expand [a,j.val]).map fun p => z (p.headD 28))

/-- Canonical balanced serialization of the child multiset with its complete
constitutional observations and Rule 4a presence marker. All atoms are ordinary
C/H, so element determines mass. Lowercase auxiliary observations are absent.
The length field distinguishes child blocks independently of their contents. -/
def shape (j : Junction) : Nat → History → List Nat
  | 0,_ => []
  | n+1,p =>
    let blocks := sortedBy (fun a b => compare a b != .gt) ((expand p).map (shape j n))
    let stereo := (frozen j .R p).isSome.toNat
    [z (p.headD 28),origin p,stereo,blocks.length] ++
      blocks.flatMap (fun b => b.length :: b)

theorem closed : ∀ j : Junction, ∀ a ∈ arms j, sphere [[a,j.val]] 12 = [] := by
  decide +kernel

theorem constitutional : ∀ j : Junction,
    let other := 1 - j.val
    let a := if j.val = 0 then 2 else 3
    let b := if j.val = 0 then 6 else 8
    let hydrogen := 10 + j.val
    heads j other = [6,6,6,1] ∧ heads j a = [6,6,1,1] ∧
    heads j b = [6,6,1,1] ∧ heads j hydrogen = [1] ∧
    shape j 12 [a,j.val] = shape j 12 [b,j.val] := by
  decide +kernel

theorem words : ∀ j : Junction, ∀ h seed : RS,
    (arms j).map (fun a => word j h seed (census j.val a)) =
      [[],[h == seed],[h.swap == seed],[]] := by
  decide +kernel

/-- Reordering even an entire arm arbitrarily cannot change its singleton/empty
word. This also covers all earlier-stage legal orders in the global path scan. -/
theorem word_of_perm (j : Junction) (h seed : RS) (a : Nat) (member : a ∈ arms j)
    {ps : List History} (perm : ps.Perm (census j.val a)) :
    word j h seed ps = word j h seed (census j.val a) := by
  have rel := perm.filterMap (fun p => (frozen j h p).map (· == seed))
  change (word j h seed ps).Perm (word j h seed (census j.val a)) at rel
  have m : word j h seed (census j.val a) ∈ [[],[h == seed],[h.swap == seed],[]] :=
    words j h seed ▸ List.mem_map_of_mem (f := fun k => word j h seed (census j.val k)) member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with e|e|e|e <;> rw [e] at rel ⊢
  · exact rel.eq_nil
  · exact List.perm_singleton.mp rel
  · exact List.perm_singleton.mp rel
  · exact rel.eq_nil


def censusWith {α : Type} (children : α → List α) : Nat → List α → List α
  | 0,_ => []
  | n+1,row => row ++ censusWith children n (row.flatMap children)


private theorem next_layer {α : Type} (children : α → List α) (row : List α) (k : Nat) :
    layersWith children (row.flatMap children) k = layersWith children row (k+1) := by
  induction k with
  | zero => rfl
  | succ n ih => exact congrArg (List.flatMap children) ih

private theorem bfs_eq (n : Nat) (row : List History) :
    censusWith expand n row = (List.range n).flatMap (sphere row) := by
  induction n generalizing row with
  | zero => rfl
  | succ n ih =>
    rw [censusWith,ih,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
    change row ++ _ = row ++ _
    apply congrArg (row ++ ·)
    apply congrArg (fun f => (List.range n).flatMap f)
    funext k
    exact next_layer expand row k

open RingFullPathPairs (FullTrace Oracle FullVisit)
open private flatMap_perm from TetraStereo.Engine.RingFullPathPairs

private theorem block_paths {α β : Type} {E : α → List α → Prop} {proj : α → β} {children : β → List β}
    {D Next : α → Prop} {xs : List α} {blocks : List (List α)}
    (h : List.Forall₂ E xs blocks) (inside : ∀ x ∈ xs, D x)
    (project : ∀ x, D x → ∀ ys, E x ys →
      (ys.map proj).Perm (children (proj x)) ∧ ∀ y ∈ ys, Next y) :
    (blocks.flatten.map proj).Perm ((xs.map proj).flatMap children) ∧ ∀ y ∈ blocks.flatten, Next y := by
  induction h with
  | nil => exact ⟨.refl _,by simp⟩
  | cons e _ ih =>
    obtain ⟨head,headIn⟩ := project _ (inside _ (by simp)) _ e
    obtain ⟨tail,tailIn⟩ := ih (fun k hk => inside k (List.mem_cons_of_mem _ hk))
    refine ⟨?_,?_⟩
    · simpa only [List.flatten_cons,List.map_append,List.map_cons,List.flatMap_cons] using head.append tail
    · intro k mem
      rcases List.mem_append.mp mem with l|r
      · exact headIn k l
      · exact tailIn k r

/-- Any legal global ranked trace enumerates the same path multiset. The only
bridge required is local: projecting each reachable expansion must give the
molecular children. No previously computed key, ranking, or final word is supplied. -/
theorem trace_projection {α β κ : Type} [LinearOrder κ] {E : α → List α → Prop}
    {key : α → κ} {proj : α → β} {children : β → List β} {D : α → Prop}
    (project : ∀ x, D x → ∀ ys, E x ys →
      (ys.map proj).Perm (children (proj x)) ∧ ∀ y ∈ ys, D y)
    {xs out : List α} (trace : FullTrace key E xs out) (inside : ∀ x ∈ xs, D x) :
    ∀ (fuel : Nat) (row : List β), (xs.map proj).Perm row →
      layersWith children row fuel = [] → (out.map proj).Perm (censusWith children fuel row) ∧ ∀ x ∈ out, D x := by
  induction trace with
  | stop =>
    intro fuel row same closedAt
    obtain rfl := same.symm.eq_nil
    refine ⟨?_,by simp⟩
    clear closedAt
    induction fuel with
    | zero => exact .refl _
    | succ k ih => simpa [censusWith] using ih
  | @sphere first rest blocks next later expanded sorted _ ih =>
    intro fuel row roots closedAt
    cases fuel with
    | zero =>
      change row = [] at closedAt
      subst row
      have impossible := roots.eq_nil
      simp at impossible
    | succ n =>
      obtain ⟨paths,sub⟩ := block_paths expanded inside project
      have nextPaths := ((sorted.perm.map proj).trans paths).trans (flatMap_perm children roots)
      obtain ⟨tail,tailIn⟩ := ih (fun x hx => sub x (sorted.perm.mem_iff.mp hx)) n
        (row.flatMap children) nextPaths ((next_layer children row n).trans closedAt)
      refine ⟨?_,?_⟩
      · simpa only [List.map_append,censusWith] using roots.append tail
      · intro x hx
        exact (List.mem_append.mp hx).elim (inside x) (tailIn x)

/-- Any native Oracle source emits the graph-calculated word. It suffices to
check each local expansion and each frozen bit on a domain containing the
initial directed visit and closed under descendants of that visit. -/
theorem native_source_word {i : LocalizedChemicalRing.Input} (o : Oracle i)
    (bit : RingActivePairs.Arm i → Option Bool) (q : RingActivePairs.Arm i)
    (j : Junction) (a : Nat) (member : a ∈ arms j) (h seed : RS)
    (proj : FullVisit i → History) (D : FullVisit i → Prop)
    (start : proj (Oracle.root bit q) = [a,j.val]) (inside : D (Oracle.root bit q))
    (children : ∀ x, D x → ∀ ys, o.Expansion bit x ys →
      (ys.map proj).Perm (expand (proj x)) ∧ ∀ y ∈ ys, D y)
    (seen : ∀ x, D x → bit x.cursor = (frozen j h (proj x)).map (· == seed))
    {w : List Bool} (source : o.Source bit q w) : w = word j h seed (census j.val a) := by
  obtain ⟨out,walk,rfl⟩ := source
  obtain ⟨perms,domain⟩ := trace_projection children walk (by simpa using inside) 12 [[a,j.val]]
    (by simp only [List.map_cons,List.map_nil,start]; exact .refl _) (closed j a member)
  rw [bfs_eq] at perms
  rw [←word_of_perm j h seed a member perms]
  simp only [word,List.filterMap_map,Function.comp_def]
  exact List.filterMap_congr (fun x hx => seen x (domain x hx))

open RingActivePairs (Arm)
open LocalizedChemicalRing (Input)

def history {i : Input} (q : Arm i) : History := q.occurrence.val.node.history.map Fin.val

private abbrev kids {i : Input} (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- The molecular incidence check ignores all stereo readers, ranks, and sorts.
The child reader can use a shared root-slice cache. Fuel exhaustion fails. -/
def graphCheck {i : Input} (edges : Arm i → List (Arm i)) : Nat → Arm i → Bool
  | 0,_ => false
  | n+1,q =>
    let cs := edges q
    decide ((cs.map history).Perm (expand (history q))) && cs.all (graphCheck edges n)

inductive Descendant {i : Input} (root : Arm i) : Arm i → Prop where
  | root : Descendant root root
  | child {q c} : Descendant root q → c ∈ kids q → Descendant root c

private theorem projected {i : Input} (o : Oracle i) (bit : Arm i → Option Bool)
    {p : FullVisit i} {ys : List (FullVisit i)} (ex : o.Expansion bit p ys) :
    ys.map FullVisit.cursor = kids p.cursor := by
  change List.Forall₂ (o.Child bit p) (kids p.cursor) ys at ex
  generalize kids p.cursor = cs at ex ⊢
  induction ex with
  | nil => rfl
  | cons head _ tail =>
    obtain ⟨_,_,rfl⟩ := head
    simp only [List.map_cons,tail]

/-- Across any admitted graph and any native ranking oracle, if exactly one
visited occurrence in the unsorted child census emits a bit, every complete
legal ranked scan emits that same singleton. No sibling, parent, or atom
ordering is required. -/
theorem native_singleton {i : Input} (o : Oracle i) (bit : Arm i → Option Bool)
    (q : Arm i) (n : Nat) (b : Bool) (exhausted : layersWith kids [q] n = [])
    (one : (censusWith kids n [q]).filterMap bit = [b])
    {w : List Bool} (source : o.Source bit q w) : w = [b] := by
  obtain ⟨out,walk,rfl⟩ := source
  have next (x : FullVisit i) (_ : True) (ys : List (FullVisit i)) (e : o.Expansion bit x ys) :
      (ys.map FullVisit.cursor).Perm (kids x.cursor) ∧ ∀ _ ∈ ys, True :=
    ⟨List.Perm.of_eq (projected o bit e),by simp⟩
  obtain ⟨visits,_⟩ := trace_projection next walk (fun _ _ => trivial) n [q] (List.Perm.refl _) exhausted
  have bits := visits.filterMap bit
  rw [one,List.filterMap_map] at bits
  exact List.perm_singleton.mp bits

/-- The fixed-R/Rule 4b/Rule 5 source words need only the approved frozen
observations on descendants and a finite check of molecular incidence.
The same structural certificate works for every seed, ranking oracle, and
geometry reading. -/
theorem source_word_of_graphCheck {i : Input} (o : Oracle i)
    (bit : Arm i → Option Bool) (q : Arm i) (j : Junction) (a : Nat)
    (member : a ∈ arms j) (h seed : RS)
    (edges : Arm i → List (Arm i)) (correct : ∀ c, edges c = kids c)
    (root : history q = [a,j.val]) {n : Nat} (checked : graphCheck edges n q = true)
    (seen : ∀ c, Descendant q c → bit c = (frozen j h (history c)).map (· == seed))
    {w : List Bool} (source : o.Source bit q w) : w = word j h seed (census j.val a) := by
  let D (x : FullVisit i) := Descendant q x.cursor ∧ ∃ k, graphCheck edges k x.cursor = true
  apply native_source_word o bit q j a member h seed (fun v => history v.cursor) D
    root ⟨.root,_,checked⟩ _ (fun v hv => seen _ hv.1) source
  intro x hx ys ex
  obtain ⟨reach,k,ok⟩ := hx
  cases k with
  | zero => contradiction
  | succ k =>
    obtain ⟨perm,all⟩ := Bool.and_eq_true_iff.mp ok
    have ids := projected o bit ex
    rw [←correct] at ids
    refine ⟨?_,?_⟩
    · have eqmap := congrArg (List.map history) ids
      rw [List.map_map] at eqmap
      exact eqmap ▸ of_decide_eq_true perm
    · intro y hy
      have mem : y.cursor ∈ edges x.cursor := ids ▸ List.mem_map_of_mem hy
      exact ⟨.child reach (correct _ ▸ mem),k,List.all_eq_true.mp all _ mem⟩

/-- Native executable reference words for every earlier-stage oracle, in
particular the through-4a and through-4c oracles for Rules 4b and 5. The only
reader premise specifies the uppercase descriptor at each reachable occurrence. -/
theorem native_stage_word {i : Input} {f : RingActivePairs.Site i}
    {r : RingNestedActivePair.Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root)
    (j : Junction) (a : Nat) (member : a ∈ arms j) (h : RS)
    (edges : Arm i → List (Arm i)) (correct : ∀ c, edges c = kids c)
    (root : history q = [a,j.val]) {n : Nat} (checked : graphCheck edges n q = true)
    (seen : ∀ c, Descendant q c → RingFullPathPairs.handAt i r rev c = frozen j h (history c))
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i r rev os seed q = some (word j h seed (census j.val a)) := by
  let o := RingFullPathPairs.stage i r rev os
  let bit := RingFullPathPairs.likeAt i r rev seed
  obtain ⟨w,hit,unique⟩ := o.source_exact (f := f) bit (RingOccurrenceStereo.rank_total ready rev os)
    q valid on
  have src := (unique w).mpr rfl
  have project (c) (hc : Descendant q c) :
      bit c = (frozen j h (history c)).map (· == seed) := congrArg (Option.map (· == seed)) (seen c hc)
  exact hit.trans (congrArg some (source_word_of_graphCheck o bit q j a member h seed edges correct
    root checked project src))

/-- Assign any common intermediate ranking to congruent signed-erased trees.
The native two-seed maximum for Rule 4b and fixed-R reading for Rule 5 follow.
A last marking is allowed and has no effect on these four strict ranks. -/
def direction (j : Junction) (h : RS) (intermediate : List Nat → List Nat)
    (mark : Nat → List Nat) (a b : Nat) : Ordering :=
  let r x := word j h .R (census j.val x)
  let s x := word j h .S (census j.val x)
  (compare (heads j a) (heads j b)).then <|
    (compare (intermediate (shape j 12 [a,j.val])) (intermediate (shape j 12 [b,j.val]))).then <|
    (compare (max (r a) (s a)) (max (r b) (s b))).then <|
    (compare (r a) (r b)).then (compare (mark a) (mark b))

def ranked (j : Junction) (h : RS) : List Nat :=
  let a := if j.val = 0 then 2 else 3
  let b := if j.val = 0 then 6 else 8
  if h = .R then [1-j.val,a,b,10+j.val] else [1-j.val,b,a,10+j.val]

theorem order_all (j : Junction) (h : RS) (intermediate : List Nat → List Nat)
    (mark : Nat → List Nat) :
    (ranked j h).Pairwise (fun a b => direction j h intermediate mark a b = .gt) := by
  let a := if j.val = 0 then 2 else 3
  let b := if j.val = 0 then 6 else 8
  have data := constitutional j
  obtain ⟨other,ha,hb,hydrogen,same⟩ := data
  have rs := words j h .R
  have ss := words j h .S
  have slots : arms j = [1-j.val,a,b,10+j.val] := by fin_cases j <;> rfl
  rw [slots] at rs ss
  simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at rs ss
  change heads j a = _ at ha
  change heads j b = _ at hb
  change shape j 12 [a,j.val] = shape j 12 [b,j.val] at same
  have shapes : compare (intermediate (shape j 12 [a,j.val])) (intermediate (shape j 12 [b,j.val])) = .eq := by rw [same]; simp
  have shapes' : compare (intermediate (shape j 12 [b,j.val])) (intermediate (shape j 12 [a,j.val])) = .eq := by rw [same]; simp
  change (if h = .R then [1-j.val,a,b,10+j.val] else [1-j.val,b,a,10+j.val]).Pairwise _
  cases h <;>
    simp [direction,other,ha,hb,hydrogen,shapes,shapes',rs.2.1,rs.2.2.1,
      ss.2.1,ss.2.2.1,List.pairwise_cons,List.compare_cons_cons] <;> repeat' constructor

end TetraStereo.Examples.DecalinLigandOrder
assert_kernel_only TetraStereo.Examples.DecalinLigandOrder.constitutional
assert_kernel_only TetraStereo.Examples.DecalinLigandOrder.words
assert_kernel_only TetraStereo.Examples.DecalinLigandOrder.native_source_word
assert_kernel_only TetraStereo.Examples.DecalinLigandOrder.order_all
assert_kernel_only TetraStereo.Examples.DecalinLigandOrder.source_word_of_graphCheck
assert_kernel_only TetraStereo.Examples.DecalinLigandOrder.native_stage_word
assert_kernel_only TetraStereo.Examples.DecalinLigandOrder.native_singleton
