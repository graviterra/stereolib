import TetraStereo.Examples.PairedCyclopropylSphereStore
import TetraStereo.Examples.PairedCyclopropylEarlierTie
import TetraStereo.Examples.PairedCyclopropylComparison
import TetraStereo.Examples.PairedCyclopropylPathOrder
import TetraStereo.Examples.AntipodalCyclohexaneWords
import TetraStereo.Engine.RingEqualPathHandCounts

/-! Project the unseeded native inventory onto the actual molecular histories
before it erases occurrence identities. Neutral endpoints and duplicated
visits are retained by this projection. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylDonorLayers
open OneCenter Engine CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingFullPathPairs (Oracle likeAt handAt)
open RingStereoSphereInventory (Visit Inventory inventory?)
open RingUnorderedSphereReading (layers?)
open DecalinLigandOrder (layersWith)
open AntipodalCyclohexaneWords (EdgeHistory histories children Rooted expansion_histories)
open DecalinAuxiliary (history)
open PairedCyclopropylPaths (molecule route)
open RingGroupedReport (origin)
open RingGroupedCentre (cursor)
open private nextWith start image next_projects eraseVisits from TetraStereo.Engine.RingStereoSphereInventory
open private block_paths next_layer from TetraStereo.Examples.DecalinLigandOrder
open private mapM_related flatMap_perm from TetraStereo.Engine.RingFullPathPairs

/-- A successful native traversal projects sphere by sphere onto the underlying
unranked molecular walk. Multiplicity and reachability are preserved at every
index, even once the traversal is exhausted. -/
private theorem layers_project {α β : Type} {next : α → Option (List α)}
    {proj : α → β} {kids : β → List β} {D : α → Prop}
    (step : ∀ x, D x → ∀ ys, next x = some ys →
      (ys.map proj).Perm (kids (proj x)) ∧ ∀ y ∈ ys, D y)
    (fuel : Nat) (xs : List α) (rows : List (List α)) (hit : layers? next fuel xs = some rows)
    (dom : ∀ x ∈ xs, D x) (n : Nat) :
    ((rows.getD n []).map proj).Perm (layersWith kids (xs.map proj) n) ∧ ∀ y ∈ rows.getD n [], D y := by
  induction fuel generalizing xs rows n with
  | zero =>
    cases xs with
    | nil =>
      have eq : rows = [] := Option.some.inj hit.symm
      subst rows
      have empty : layersWith kids [] n = [] := by induction n <;> simp_all [layersWith]
      simp [empty]
    | cons x xs => simp [layers?] at hit
  | succ fuel ih =>
    cases xs with
    | nil =>
      have eq : rows = [] := Option.some.inj hit.symm
      subst rows
      have empty : layersWith kids [] n = [] := by induction n <;> simp_all [layersWith]
      simp [empty]
    | cons x xs =>
      simp only [layers?] at hit
      obtain ⟨blocks,expanded,rest⟩ := Option.bind_eq_some_iff.mp hit
      obtain ⟨tail,rec,eq⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj eq
      cases n with
      | zero => exact ⟨.refl _,dom⟩
      | succ n =>
        have mapped := mapM_related (R := fun a bs => next a = some bs) (fun _ _ h => h) expanded
        obtain ⟨same,valid⟩ := block_paths mapped dom step
        obtain ⟨perm,also⟩ := ih _ _ rec valid n
        have ext {u v : List β} (p : u.Perm v) (k : Nat) :
            (layersWith kids u k).Perm (layersWith kids v k) := by
          induction k with
          | zero => exact p
          | succ k h => exact flatMap_perm kids h
        exact ⟨(perm.trans (ext same n)).trans (List.Perm.of_eq (next_layer kids _ n)),also⟩

def firstEdge (side : Bool) : EdgeHistory := ([0],route side 0)

def tag (p : EdgeHistory) : Option (Bool × Fin 5) :=
  ([false,true].flatMap fun s => (List.finRange 5).map (s,·)).find?
    (fun sv => p.2 == route sv.1 sv.2)

def expected (side : Bool) (d : Nat) : List (Bool × Fin 5) :=
  match d with
  | 0 => [(side,0)]
  | 1 => [(side,1)]
  | 2 => [(side,2),(side,3)]
  | 3 => [(side,4)]
  | _ => []

abbrev graphLayer (side : Bool) := layersWith (children molecule) [firstEdge side]

private theorem tables : ∀ (side : Bool) (n : Fin 5),
    ((graphLayer side n).filterMap tag).Perm (expected side n) := by decide +kernel
private theorem stop : ∀ side, graphLayer side 5 = [] := by decide +kernel
private theorem written : AntipodalCyclohexaneHands.HistoryPriority.GraphFacts molecule := by
  unfold AntipodalCyclohexaneHands.HistoryPriority.GraphFacts
  decide +kernel

theorem graph_donors (side : Bool) (n : Nat) :
    ((graphLayer side n).filterMap tag).Perm (expected side n) := by
  by_cases h : n < 5
  · exact tables side ⟨n,h⟩
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 5 ≤ n by omega)
    have empty (j : Nat) : graphLayer side (5+j) = [] := by
      induction j with
      | zero => exact stop side
      | succ j ih => change (graphLayer side (5+j)).flatMap _ = _; rw [ih]; rfl
    rw [empty,Nat.add_comm 5 k]; rfl

abbrev publicRead := AntipodalCyclohexaneWords.publicRead

def next {i : Input} (r : Reader i) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) :=
  nextWith r rev i.certified.executableLocalizedRerootChildren
    (RingRetainedStereoRefinement.priority i r rev os)

def first {i : Input} (r : Reader i) (rev : Bool) (q : Arm i) := start r rev q

def erase {i : Input} (rows : List (List (Visit i))) : Inventory := eraseVisits rows

def edge {i : Input} (v : Visit i) := histories v.arm

private def valid {i : Input} (root : i.certified.Atom) (v : Visit i) :=
  Rooted root (image .R v)

private theorem step {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (r : Reader i) (rev : Bool) (os : List RingRetainedStereoRefinement.Observation)
    (v : Visit i) (good : valid root v) (ys : List (Visit i)) (hit : next r rev os v = some ys) :
    (ys.map edge).Perm (children molecule (edge v)) ∧ ∀ y ∈ ys, valid root y := by
  let o := RingFullPathPairs.stage i r rev os
  have projects := next_projects o r rev .R v
  change (next r rev os v).map _ = _ at projects
  rw [hit] at projects
  have ex := o.next_sound (likeAt i r rev .R) _ _ projects.symm
  obtain ⟨hs,dom⟩ := expansion_histories raw written o _ root _ good _ ex
  exact ⟨by simpa [edge,image,List.map_map,Function.comp_def] using hs,
    fun y hy => dom _ (List.mem_map_of_mem hy)⟩

open private start from TetraStereo.Examples.DecalinRootWords in
private theorem start_edge {i : Input} (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4) (side : Bool)
    (id : RingGroupedTrials.atom fr s = if side then 14 else 3) :
    histories (cursor fr s) = firstEdge side := by
  change ([root.val],DecalinLigandOrder.history (cursor fr s)) = _
  rw [start root fr s,id,zero]
  cases side <;> rfl

/-- The actual inventories of any earlier-stage reader with total stage ranks
are the erasures of these same occurrence layers. For the public root both
through-4a and through-4c stages (and either geometry) are covered. -/
theorem native_layers {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (zero : root.val = 0)
    (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4) (side : Bool)
    (id : RingGroupedTrials.atom fr s = if side then 14 else 3) (rev : Bool)
    (os : List RingRetainedStereoRefinement.Observation) :
    let r := publicRead i root
    let q := cursor fr s
    ∃ rows : List (List (Visit i)),
      layers? (next r rev os) (i.certified.localizedRerootCursorBudget q + 1) [first r rev q] = some rows ∧
      inventory? i r rev os q = some (erase rows) ∧
      ∀ d, (((rows.getD d []).map edge).Perm (graphLayer side d)) ∧
        (((rows.getD d []).filterMap (tag ∘ edge)).Perm (expected side d)) ∧
        ∀ v ∈ rows.getD d [], v.arm.occurrence.val.root = root := by
  dsimp only
  let r := publicRead i root
  let q := cursor fr s
  let o := RingFullPathPairs.stage i r rev os
  obtain ⟨w,hit,_⟩ := o.source_exact (f := origin i root) (likeAt i r rev .R)
    (RingOccurrenceStereo.rank_total (RingChemicalGraphProof.ready ok _) rev os)
    q (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  have found := RingStereoSphereInventory.reading_exact i r rev os .R q
  rw [show RingFullPathPairs.stageWords i r rev os .R q = some w from hit] at found
  obtain ⟨inv,got,_⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨rows,run,equal⟩ := Option.map_eq_some_iff.mp got
  refine ⟨rows,run,got.trans (congrArg some equal.symm),?_⟩
  intro d
  have initial : valid root (first r rev q) :=
    ⟨RingGroupedCentre.valid fr s,(fr.direction s).property.1,origin i root,rfl⟩
  obtain ⟨paths,dom⟩ := layers_project (step raw root r rev os) _ _ _ run
    (by simpa using initial) d
  have startEq : edge (first r rev q) = firstEdge side := start_edge root zero fr s side id
  change ((rows.getD d []).map edge).Perm (layersWith _ [edge (first r rev q)] d) at paths
  rw [startEq] at paths
  exact ⟨paths,by simpa [List.filterMap_map] using (paths.filterMap tag).trans (graph_donors side d),
    fun v hv => (dom v hv).2.1⟩

open RingEqualPathHandCounts (lastHand)
open PairedCyclopropylComparison (Hands visit fromGeometry?)
open private outside from TetraStereo.Examples.PairedCyclopropylEarlierTie
open private related_of_mem from TetraStereo.Engine.RingFullPathPairs
open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary

private def Parent {α : Type} (next : α → Option (List α)) (x y : α) :=
  ∃ ys, next x = some ys ∧ y ∈ ys

private def Reach {α : Type} (next : α → Option (List α)) (x : α) : Nat → α → Prop
  | 0,y => y = x
  | n+1,y => ∃ z, Reach next x n z ∧ Parent next z y

private theorem reached {α : Type} {f : α → Option (List α)} {x : α}
    (n : Nat) {row rows} (found : layers? f n row = some rows) (k : Nat)
    (dom : ∀ y ∈ row, Reach f x k y) (d : Nat) :
    ∀ y ∈ rows.getD d [], Reach f x (k+d) y := by
  induction n generalizing row rows k d with
  | zero =>
    cases row <;> simp [layers?] at found
    subst rows; simp
  | succ n ih =>
    cases row with
    | nil => simp [layers?] at found; subst rows; simp
    | cons a as =>
      simp only [layers?] at found
      obtain ⟨blocks,hb,rest⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨tail,ht,eq⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj eq
      cases d with
      | zero => exact dom
      | succ d =>
        have more (z : α) (hz : z ∈ blocks.flatten) : Reach f x (k+1) z := by
          obtain ⟨ys,listed,mem⟩ := List.mem_flatten.mp hz
          obtain ⟨parent,was,hit⟩ := related_of_mem (mapM_related
            (R := fun a ys => f a = some ys) (fun _ _ e => e) hb) listed
          exact ⟨parent,dom _ was,ys,hit,mem⟩
        simpa [Nat.add_assoc,Nat.add_comm 1 d] using ih ht (k+1) more d

private theorem childData {i : Input} {r : Reader i} {rev os} {x y : Visit i}
    (follow : Parent (next r rev os) x y) :
    y.arm ∈ i.certified.executableLocalizedRerootChildren x.arm ∧
      ∃ b, RingRetainedStereoRefinement.priority i r rev os y.arm = some b ∧
        y.path = x.path ++ [⟨b.deep,handAt i r rev y.arm⟩] := by
  obtain ⟨ys,hit,hy⟩ := follow
  unfold next nextWith at hit
  obtain ⟨c,mem,op⟩ := related_of_mem (mapM_related (R := fun c y =>
    ∃ b, RingRetainedStereoRefinement.priority i r rev os c = some b ∧
      y = (⟨c,x.path ++ [⟨b.deep,handAt i r rev c⟩]⟩ : Visit i)) (fun c u h => by
        obtain ⟨b,hb,eq⟩ := Option.bind_eq_some_iff.mp h
        exact ⟨b,hb,(Option.some.inj eq).symm⟩) hit) hy
  obtain ⟨b,hb,rfl⟩ := op
  exact ⟨mem,b,hb,rfl⟩

private theorem reach_hand {i : Input} {r : Reader i} {rev os q d} {v : Visit i}
    (walk : Reach (next r rev os) (first r rev q) d v) :
    lastHand v.path = handAt i r rev v.arm := by
  cases d with
  | zero => cases walk; rfl
  | succ d =>
    obtain ⟨z,_,follow⟩ := walk
    obtain ⟨_,b,_,p⟩ := childData follow
    simp [p,lastHand]

private theorem tag_match {p : EdgeHistory} {s : Bool} {v : Fin 5} (hit : tag p = some (s,v)) :
    p.2 = route s v := eq_of_beq (List.find?_some
      (p := fun z : Bool × Fin 5 => p.2 == route z.1 z.2) hit)

private theorem no_tag {p : EdgeHistory} (no : tag p = none) : ¬ ∃ s v, p.2 = route s v := by
  rintro ⟨s,v,path⟩
  have member : (s,v) ∈ [false,true].flatMap (fun b => (List.finRange 5).map (b,·)) :=
    List.mem_flatMap.mpr ⟨s,by cases s <;> simp,List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩⟩
  have absent := List.find?_eq_none.mp no (s,v) member
  simp [path] at absent

private theorem expected_side {side : Bool} {d : Nat} {sv : Bool × Fin 5}
    (hit : sv ∈ expected side d) : sv.1 = side := by
  unfold expected at hit
  split at hit <;> simp_all
  rcases hit with rfl | rfl <;> rfl

/-- The last signed edge seen at each actual row member is its physical donor
hand (reversed on reflection), or silence when its history is untagged. -/
theorem row_hand {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} (zero : root.val = 0) {side : Bool} {h : Hands}
    (reading : fromGeometry? (RingWrittenPHReadings.geometry i.spatial) side = some h)
    {rev : Bool} {os q rows fuel d} {v : Visit i}
    (run : layers? (next (publicRead i root) rev os) fuel [first (publicRead i root) rev q] = some rows)
    (tags : ((rows.getD d []).filterMap (tag ∘ edge)).Perm (expected side d))
    (member : v ∈ rows.getD d []) (on : v.arm.occurrence.val.root = root) :
    lastHand v.path = (tag (edge v)).map (fun sv => visit (if rev then h.mirror else h) sv.2) := by
  have walk := reached fuel run 0 (x := first (publicRead i root) rev q)
    (by intro y hy; simpa [Reach] using hy) d v member
  rw [reach_hand walk]
  cases hit : tag (edge v) with
  | none =>
    have off := no_tag hit
    have dead : publicRead i root v.arm.occurrence = some none := by
      unfold publicRead AntipodalCyclohexaneWords.publicRead RingActiveDistanceSchedule.frozen
      simp only [show (origin i root).val.root = root from rfl,on,ne_eq,not_true_eq_false,if_false]
      split
      · rename_i visible
        exact outside raw ok zero (q := v.arm.occurrence) ⟨on,visible⟩ off
      · rfl
    simp [handAt,dead,RingNestedActivePair.upper]
  | some sv =>
    obtain ⟨s,j⟩ := sv
    have isSide := expected_side (tags.mem_iff.mp (List.mem_filterMap.mpr ⟨v,member,hit⟩))
    change s = side at isSide
    subst s
    have path : history v.arm.occurrence = route side j := tag_match hit
    obtain ⟨q0,t,on0,_,_,_,uniq,read,cuts⟩ :=
      PairedCyclopropylSphereStore.donor_at_each_cut raw ok root zero side j
    obtain rfl := uniq _ on path
    have fin := (cuts (RingActiveDistanceSchedule.height i + 1) (by omega)).2
    rw [if_pos (by omega)] at fin
    have prior := congrFun (RingGlobalComparison.prior_exact (i := i) (a := root) (Or.inr ⟨rfl,rfl⟩)) v.arm.occurrence
    change RingSphereQueue.reader root _ v.arm.occurrence = publicRead i root v.arm.occurrence at prior
    rw [RingSphereQueue.reader,if_pos on0,fin] at prior
    have same := Option.some.inj (read.symm.trans (PairedCyclopropylComparison.physical_visits reading j))
    unfold handAt
    rw [←prior,same]
    cases rev <;> fin_cases j <;> rfl

private def midRoute (s detour : Bool) :=
  if detour then ((if s then 14 else 3) + 2) :: route s 0 else route s 1

private theorem mids : ∀ (s detour : Bool),
    ∀ e ∈ children molecule (firstEdge s), ∀ f ∈ children molecule e,
      tag f = some (s,if detour then 3 else 2) → e.2 = midRoute s detour := by decide +kernel

private theorem midData {i : Input} (raw : i.molecule = molecule) {root : i.certified.Atom}
    {r : Reader i} {rev os q s detour} {rows : List (List (Visit i))} {fuel} {v : Visit i}
    (init : valid root (first r rev q)) (base : edge (first r rev q) = firstEdge s)
    (run : layers? (next r rev os) fuel [first r rev q] = some rows) (mem : v ∈ rows.getD 2 [])
    (which : tag (edge v) = some (s, if detour then 3 else 2)) :
    ∃ (dir : RingRetainedChemicalPreorder.Direction i q.occurrence) (k : RingStereoSiblingPass.Branch)
      (midHand : Option RS) (tail : RingStereoSphereInventory.SignedPath), history dir.val = midRoute s detour ∧
      RingRetainedStereoRefinement.priority i r rev os ⟨dir.val,some q.occurrence⟩ = some k ∧
      v.path = ⟨[],handAt i r rev q⟩ :: ⟨k.deep,midHand⟩ :: tail := by
  have walk := reached fuel run 0 (x := first r rev q)
    (by intro y hy; simpa [Reach] using hy) 2 v mem
  obtain ⟨mid,⟨z,hz,hop⟩,last⟩ := walk
  change z = first r rev q at hz
  subst z
  obtain ⟨ms,hm,inMid⟩ := hop
  obtain ⟨ends,he,inEnd⟩ := last
  obtain ⟨firstKids,validMid⟩ := step raw root r rev os _ init _ hm
  obtain ⟨lastKids,_⟩ := step raw root r rev os _ (validMid mid inMid) _ he
  have ma := firstKids.mem_iff.mp (List.mem_map_of_mem (f := edge) inMid)
  rw [base] at ma
  have mb := lastKids.mem_iff.mp (List.mem_map_of_mem (f := edge) inEnd)
  have pm := mids s detour _ ma _ mb which
  obtain ⟨atMid,k,hk,midPath⟩ := childData ⟨ms,hm,inMid⟩
  obtain ⟨_,l,_,endPath⟩ := childData ⟨ends,he,inEnd⟩
  have seen := i.certified.executableLocalizedRerootChildren_previous q mid.arm atMid
  have intended := ((i.certified.executableLocalizedRerootChildren_mem_iff q mid.arm).mp atMid).2
  have adj := (i.certified.mem_localizedRerootNeighborFrames_iff q.occurrence.val mid.arm.occurrence.val).mp
    (i.certified.mem_localizedRerootNeighborFrames_of_mem_intended q _ intended)
  let dir : RingRetainedChemicalPreorder.Direction i q.occurrence := ⟨mid.arm.occurrence,adj.2⟩
  have same : mid.arm = ⟨dir.val,some q.occurrence⟩ := by
    change mid.arm = ⟨mid.arm.occurrence,some q.occurrence⟩
    rw [←seen]
  refine ⟨dir,k,handAt i r rev mid.arm,[⟨l.deep,handAt i r rev v.arm⟩],pm,same ▸ hk,?_⟩
  rw [endPath,midPath]
  rfl

/-- Native expansion gives both third-sphere visits the very same entry
edge. Their second edges are ranked at the actual entry focus by the public
staged rank reader; two atomic-number shells put direct before detour. -/
theorem shared_edges {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) (fr : RingNestedActivePair.Frame i (origin i root)) (slot : Fin 4)
    (side : Bool) (id : RingGroupedTrials.atom fr slot = if side then 14 else 3)
    {r : Reader i} {rev os rows fuel} {x y : Visit i}
    (run : layers? (next r rev os) fuel [first r rev (cursor fr slot)] = some rows)
    (mx : x ∈ rows.getD 2 []) (my : y ∈ rows.getD 2 [])
    (tx : tag (edge x) = some (side,2)) (ty : tag (edge y) = some (side,3)) :
    ∃ e direct detour tailA tailB, x.path = e :: direct :: tailA ∧ y.path = e :: detour :: tailB ∧
      detour.earlier.length = direct.earlier.length ∧ detour.earlier < direct.earlier := by
  let q := cursor fr slot
  have ini : valid root (first r rev q) :=
    ⟨RingGroupedCentre.valid fr slot,(fr.direction slot).property.1,origin i root,rfl⟩
  have base : edge (first r rev q) = firstEdge side := start_edge root zero fr slot side id
  obtain ⟨a,hi,hh,ta,pa,ha,xa⟩ := midData (detour := false) raw ini base run mx tx
  obtain ⟨b,lo,lh,tb,pb,hb,yb⟩ := midData (detour := true) raw ini base run my ty
  have senior := PairedCyclopropylPathOrder.shared_priority raw side b a (congrArg Prod.snd base) pa pb hb ha
  exact ⟨_,_,_,ta,tb,xa,yb,senior⟩


end TetraStereo.Examples.PairedCyclopropylDonorLayers
assert_kernel_only TetraStereo.Examples.PairedCyclopropylDonorLayers.native_layers
assert_kernel_only TetraStereo.Examples.PairedCyclopropylDonorLayers.row_hand
assert_kernel_only TetraStereo.Examples.PairedCyclopropylDonorLayers.shared_edges
