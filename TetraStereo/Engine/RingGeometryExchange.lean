import TetraStereo.Engine.RingOrientation

set_option autoImplicit false

namespace TetraStereo.Engine.RingGeometryExchange
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Expansion key? observation?)
open RingRetainedStereoRefinement (Derives Pass)
open RingRetainedReferenceGroup (Listing Hit)
open RingRetainedUnitPass (forOutput)
open RingRetainedStereoDecision (Reads)
open RingGroupedCentre (Arms cursor)
open RingActivePairReport (Slot)
attribute [local instance] lexOrd

private abbrev kids {i : Input} (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- A map on directed occurrences needs to match children only up to permutation.
The matched subtree retains the actual atomic, isotope and closure-origin observations. -/
structure Carrier (i j : Input) where
  image : Arm i → Arm j
  domain : Arm i → Prop
  below : ∀ q, domain q → ∀ c ∈ kids q, domain c
  children : ∀ q, domain q → ((kids q).map image).Perm (kids (image q))
  observation : ∀ q, domain q → observation? i q (kids q).isEmpty =
    observation? j (image q) (kids (image q)).isEmpty

private theorem expandRows {α β γ : Type} {xs : List α} {ys : List β} {get : α → Option β}
    (found : xs.mapM get = some ys) (rows : β → List γ) :
    ys.flatMap rows = xs.flatMap (fun q => (get q).toList.flatMap rows) := by
  have pairs := TerminalTie.mapM_forall₂ _ _ _ found
  clear found
  induction pairs with
  | nil => rfl
  | cons head _ ih => simp [head,ih]

private theorem matchRows {α β γ δ ε : Type} {e : α → β} {xs : List α} {ys : List β}
    {l : α → Option γ} {r : β → Option δ} {ls rs} (edges : (xs.map e).Perm ys)
    (left : xs.mapM l = some ls) (right : ys.mapM r = some rs)
    (a : γ → List ε) (b : δ → List ε)
    (each : ∀ x ∈ xs, ∀ {v w}, l x = some v → r (e x) = some w → (a v).Perm (b w)) :
    (ls.flatMap a).Perm (rs.flatMap b) := by
  rw [expandRows left a,expandRows right b]
  have target := edges.flatMap_right (fun q => (r q).toList.flatMap b)
  rw [List.flatMap_map] at target
  apply List.Perm.trans _ target
  apply List.Perm.flatMap_left
  intro x hx
  obtain ⟨v,_,hv⟩ := RingRetainedReferenceGroup.forInput left hx
  obtain ⟨w,_,hw⟩ := RingRetainedReferenceGroup.forInput right (edges.mem_iff.mp (List.mem_map.mpr ⟨x,hx,rfl⟩))
  simpa only [hv,hw,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,Function.comp_apply]
    using each x hx hv hw

private theorem matchChildren {α β γ : Type} {e : α → β} {xs : List α} {ys : List β}
    {l : α → Option γ} {r : β → Option γ} {ls rs} (edges : (xs.map e).Perm ys)
    (left : xs.mapM l = some ls) (right : ys.mapM r = some rs)
    (each : ∀ x ∈ xs, ∀ {v w}, l x = some v → r (e x) = some w → v = w) : ls.Perm rs := by
  simpa using matchRows edges left right (fun x => [x]) (fun x => [x])
    (fun x hx _ _ hv hw => List.Perm.of_eq (congrArg List.singleton (each x hx hv hw)))

private theorem childList {i : Input} {q : Arm i} {cs}
    (frame : i.certified.DeclarativeLocalizedRerootChildren q cs) : cs = kids q :=
  Option.some.inj (((i.certified.localizedRerootChildren?_eq_some_iff q cs).mpr frame).symm.trans
    ((i.certified.localizedRerootChildren?_eq_some_iff q _).mpr (i.certified.executableLocalizedRerootChildren_declarative q)))

theorem Carrier.constitution {i j} (c : Carrier i j) {q x y} (on : c.domain q)
    (left : Expansion i q x) (right : Expansion j (c.image q) y) : x = y := by
  induction left generalizing y with
  | @node q cs o ks frame obs look found sub ih =>
    cases right with
    | node frame' obs' look' found' sub' =>
      obtain rfl := childList frame
      obtain rfl := childList frame'
      obtain rfl := Option.some.inj (obs.symm.trans ((c.observation q on).trans obs'))
      have edges := c.children q on
      apply RingRetainedChemicalTrace.assemble_perm _ (matchChildren edges found found' ?_)
      · intro k hk
        obtain ⟨t,ht,got⟩ := forOutput found hk
        exact (sub t ht got).formed
      · intro t ht u v hu hv
        exact ih t ht hu (c.below q on t ht) (sub' _ (edges.mem_iff.mp (List.mem_map.mpr ⟨t,ht,rfl⟩)) hv)

/-- Frozen labels are observed at matched occurrences; their numerical atom
identifiers and position in the sibling enumeration can differ. -/
def Frozen {i j} (c : Carrier i j) (l : Reader i) (r : Reader j) :=
  ∀ q, c.domain q → l q.occurrence = r (c.image q).occurrence

private theorem rowsTransport {as bs sh de sh' de' : List Branch} (p : as.Perm bs)
    (l : Legal Branch.shallow as sh) (m : Legal Branch.deep as de)
    (r : Legal Branch.shallow bs sh') (s : Legal Branch.deep bs de')
    (formed : ∀ x ∈ as, RingRetainedChemicalTrace.Framed 2 x.levels) :
    rows sh de = rows sh' de' :=
  rows_unique l m ⟨r.perm.trans p.symm,r.descending⟩ ⟨s.perm.trans p.symm,s.descending⟩ formed

theorem Carrier.unit {i j l r} (c : Carrier i j) (same : Frozen c l r)
    {rev q x y} (on : c.domain q) (left : RingRetainedUnitPass.Reading i l rev q x)
    (right : RingRetainedUnitPass.Reading j r rev (c.image q) y) : x = y := by
  induction left generalizing y with
  | @node q k v _ _ _ key seen _ _ all sub sh de ih =>
    cases right with
    | node key' seen' _ _ all' sub' sh' de' =>
      obtain rfl := c.constitution on (RingRetainedChemicalTrace.key_source key) (RingRetainedChemicalTrace.key_source key')
      obtain rfl := Option.some.inj (seen.symm.trans ((same q on).trans seen'))
      have edges := c.children q on
      have perm := matchChildren edges all all' (fun t ht _ _ hu hv =>
        ih t ht hu (c.below q on t ht) (sub' _ (edges.mem_iff.mp (List.mem_map.mpr ⟨t,ht,rfl⟩)) hv))
      have eqn := rowsTransport perm sh de sh' de' (fun x hx => by
        obtain ⟨t,ht,get⟩ := forOutput all hx
        exact (sub t ht get).framed)
      unfold RingRetainedUnitPass.branch
      rw [eqn]

private theorem passTransport {i j l r P Q obs rev} (c : Carrier i j) (same : Frozen c l r)
    (before : ∀ q, c.domain q → ∀ x y, P q x → Q (c.image q) y → x = y)
    {q x y} (on : c.domain q) (left : Pass i P l obs rev q x)
    (right : Pass j Q r obs rev (c.image q) y) : x = y := by
  induction left generalizing y with
  | @node q p v _ _ _ prior seen _ all sub sh de ih =>
    cases right with
    | node prior' seen' _ all' sub' sh' de' =>
      obtain rfl := before q on _ _ prior prior'
      obtain rfl := Option.some.inj (seen.symm.trans ((same q on).trans seen'))
      have edges := c.children q on
      have perm := matchChildren edges all all' (fun t ht _ _ hu hv =>
        ih t ht hu (c.below q on t ht) (sub' _ (edges.mem_iff.mp (List.mem_map.mpr ⟨t,ht,rfl⟩)) hv))
      have eqn := rowsTransport perm sh de sh' de' (fun x hx => by
        obtain ⟨t,ht,get⟩ := forOutput all hx
        exact (sub t ht get).framed)
      unfold RingRetainedStereoRefinement.extend
      rw [eqn]

theorem Carrier.refinement {i j l r rev} (c : Carrier i j) (same : Frozen c l r) :
    ∀ os q, c.domain q → ∀ x y, Derives i l rev os q x → Derives j r rev os (c.image q) y → x = y
  | [],_,on,_,_,a,b => c.unit same on a b
  | _::os,_,on,_,_,a,b => passTransport c same (c.refinement same os) on a b

private def under (part : Branch × List Hit) : List Hit :=
  part.2.map fun h => {h with path := part.1.deep :: h.path}

theorem Carrier.hits {i j l r} (c : Carrier i j) (same : Frozen c l r) {q xs ys}
    (on : c.domain q) (left : Listing i l q xs) (right : Listing j r (c.image q) ys) : xs.Perm ys := by
  induction left generalizing ys with
  | @node q v parts seen _ lookup all rank below ih =>
    cases right with
    | node seen' _ _ all' rank' below' =>
      obtain rfl := Option.some.inj (seen.symm.trans ((same q on).trans seen'))
      apply List.Perm.append_left
      have edges := c.children q on
      apply matchRows edges all all' under under
      rintro t ht ⟨k,hs⟩ ⟨k',hs'⟩ hu hv
      have ht' := edges.mem_iff.mp (List.mem_map.mpr ⟨t,ht,rfl⟩)
      have active := c.below q on t ht
      obtain rfl := c.unit same active (rank t ht hu) (rank' _ ht' hv)
      exact (ih t ht hu active (below' _ ht' hv)).map _

theorem Carrier.priority {i j l r rev} (c : Carrier i j) (same : Frozen c l r) {q x y}
    (on : c.domain q) (left : Reads i l rev q x) (right : Reads j r rev (c.image q) y) :
    RingGroupedRanking.key x rev = RingGroupedRanking.key y rev := by
  have unit := c.unit same on left.unit right.unit
  have refs := RingRetainedReferenceGroup.references_perm (c.hits same on left.hits right.hits) rev
  have lo := c.refinement same _ _ on _ _ left.lower right.lower
  have localPair (s : RS) := c.refinement same _ _ on _ _ (left.paired s) (right.paired s)
  have fixed := c.refinement same _ _ on _ _ (left.fixed .R) (right.fixed .R)
  have localR : x.localR = y.localR := localPair .R
  have localS : x.localS = y.localS := localPair .S
  simp only [RingGroupedRanking.key,RingGroupedRanking.stereoKey,RingGroupedRanking.localKey,
    refs,localPair,RingRetainedStereoDecision.ArmProfile.bestPair,unit,lo,fixed,localR,localS]

/-- The selected atom must be carried to the selected atom at every occurrence,
including terminal copies. The map may be chosen separately for each mark. -/
def Marked {i j} (c : Carrier i j) (a b : Nat) :=
  ∀ q, c.domain q → RingGroupedMark.bit a q = RingGroupedMark.bit b (c.image q)

theorem Carrier.mark {i j l r a b rev} (c : Carrier i j) (same : Frozen c l r)
    (marked : Marked c a b) {q x y} (on : c.domain q)
    (left : RingGroupedMark.OnGeometry i l rev a q x)
    (right : RingGroupedMark.OnGeometry j r rev b (c.image q) y) : x = y := by
  induction left generalizing y with
  | @node q prior cs sh de before _ all sub shallow deep ih =>
    cases right with
    | node before' _ all' sub' shallow' deep' =>
      obtain rfl := c.refinement same _ _ on _ _ before before'
      have edges := c.children q on
      have perm := matchChildren edges all all' (fun t ht _ _ hu hv =>
        ih t ht hu (c.below q on t ht) (sub' _ (edges.mem_iff.mp (List.mem_map.mpr ⟨t,ht,rfl⟩)) hv))
      have eqn := rowsTransport perm shallow deep shallow' deep' (fun x hx => by
        obtain ⟨t,ht,get⟩ := forOutput all hx
        exact (sub t ht get).framed)
      unfold RingRetainedStereoRefinement.extend
      rw [eqn,marked q on]

/-- An exchange of two directed ligand subtrees, carrying primitive molecular
observations, frozen publications and the selected atom. -/
structure Exchange {i f} (fr : RingNestedActivePair.Frame i f) (read : Reader i)
    (mark j k : Slot) where
  carrier : Carrier i i
  atLigand : carrier.domain (cursor fr j)
  other : carrier.image (cursor fr j) = cursor fr k
  frozen : Frozen carrier read read
  selected : Marked carrier (RingGroupedTrials.atom fr mark) (RingGroupedTrials.atom fr mark)

theorem Exchange.equal_priorities {i f fr read} (arms : @Arms i f fr read) {s j k}
    (e : Exchange fr read s j k) (ready : RingGroupedStereo.Ready f read) :
    RingGroupedOrders.wins arms false (RingOrientation.markedWord fr read s) j =
      RingGroupedOrders.wins arms false (RingOrientation.markedWord fr read s) k := by
  have key := e.carrier.priority e.frozen e.atLigand (arms.source j) (e.other.symm ▸ arms.source k)
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready (RingGroupedTrials.atom fr s) (cursor fr j)
    (RingGroupedCentre.valid fr j) (fr.direction j).property.1
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready (RingGroupedTrials.atom fr s) (cursor fr k)
    (RingGroupedCentre.valid fr k) (fr.direction k).property.1
  have word := e.carrier.mark e.frozen e.selected e.atLigand (RingGroupedMark.arm_source hx).2
    (e.other.symm ▸ (RingGroupedMark.arm_source hy).2)
  apply Prod.ext key
  change RingOrientation.markedWord fr read s j = RingOrientation.markedWord fr read s k
  simp [RingOrientation.markedWord,hx,hy,word]

/-- One exchange per eligible mark suffices. Different marks can leave
different pairs tied. This directly forces refusal on the physical centre. -/
theorem refuse_of_exchanges {i f fr read a m} (d : @RingGroupedTrials.Decision i f fr read a m)
    (ready : RingGroupedStereo.Ready f read) (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (promoted : 3 ≤ (RingGroupedOrders.marks a).length)
    (exchanges : ∀ s ∈ RingGroupedOrders.marks a, ∃ j k, j ≠ k ∧ Nonempty (Exchange fr read s j k)) :
    d.letters = none := by
  apply (RingOrientation.refusal_iff d ready coordinates).mpr
  rw [RingOrientation.index,if_neg (by omega)]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
  obtain ⟨j,k,ne,⟨e⟩⟩ := exchanges s hs
  exact (RingOrientation.orientation_zero _).mpr (fun inj => ne (inj (e.equal_priorities a ready)))

end TetraStereo.Engine.RingGeometryExchange
assert_kernel_only TetraStereo.Engine.RingGeometryExchange.Carrier.refinement
assert_kernel_only TetraStereo.Engine.RingGeometryExchange.refuse_of_exchanges
