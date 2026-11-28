import TetraStereo.Examples.AntipodalCyclohexaneStore
import TetraStereo.Examples.DecalinRootWords

/-! Project each ranked visit to the histories on its two ends. A graph census
can then determine an entire signed word whenever at most one visit emits a bit. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneWords
open Engine OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingFullPathPairs (Oracle FullVisit)
open DecalinAuxiliary (History history)
open DecalinLigandOrder (layersWith censusWith trace_projection)
open AntipodalCyclohexaneHands (molecule route frameRow)
open AntipodalCyclohexaneHands.HistoryPriority (GraphFacts child_histories)
open private next from TetraStereo.Examples.AntipodalCyclohexaneHands
open private projected from TetraStereo.Examples.DecalinLigandOrder

abbrev EdgeHistory := History × History

def histories {i : Input} (q : Arm i) : EdgeHistory :=
  (q.previous?.elim [] history, history q.occurrence)

def children (m : RawMolecule) (p : EdgeHistory) : List EdgeHistory :=
  (next m p.1 p.2).map fun h => (p.2,h)

def Rooted {i : Input} (root : i.certified.Atom) (x : FullVisit i) : Prop :=
  i.certified.LocalizedRerootCursorValid x.cursor ∧ x.cursor.occurrence.val.root = root ∧
    ∃ p, x.cursor.previous? = some p

/-- Projection of one native expansion onto the written molecular histories. -/
theorem expansion_histories {m : RawMolecule} {i : Input} (raw : i.molecule = m) (written : GraphFacts m)
    (o : Oracle i) (bit : Arm i → Option Bool) (root : i.certified.Atom)
    (x : FullVisit i) (hx : Rooted root x) (ys : List (FullVisit i)) (ex : o.Expansion bit x ys) :
    (ys.map (fun v => histories v.cursor)).Perm (children m (histories x.cursor)) ∧ ∀ y ∈ ys, Rooted root y := by
  obtain ⟨v,onx,p,hp⟩ := hx
  have cursors : ys.map FullVisit.cursor = i.certified.executableLocalizedRerootChildren x.cursor := projected o bit ex
  have membership (y : FullVisit i) (hy : y ∈ ys) : y.cursor ∈ i.certified.executableLocalizedRerootChildren x.cursor :=
    cursors ▸ List.mem_map_of_mem hy
  have mapped := (child_histories written raw x.cursor p hp v).map (fun h => (history x.cursor.occurrence,h))
  constructor
  · have one : ys.map (fun v => histories v.cursor) =
        (ys.map FullVisit.cursor).map (fun c => (history x.cursor.occurrence,history c.occurrence)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro y hy
      simp [histories, i.certified.executableLocalizedRerootChildren_previous _ _ (membership y hy)]
    rw [one,cursors]
    simpa [children,histories,hp,List.map_map,Function.comp_def] using mapped
  · intro y hy
    have mem := membership y hy
    have frame := i.certified.executableLocalizedRerootChildren_declarative x.cursor
    exact ⟨i.certified.localizedRerootChild_valid _ _ _ frame mem,
      (i.certified.localizedRerootChildren_root_eq _ _ _ frame mem).trans onx,
      x.cursor.occurrence,i.certified.executableLocalizedRerootChildren_previous _ _ mem⟩

/-- The geometry and all earlier rankings may reorder a scan. A graph census
with zero or one emitted bit fixes the resulting word for every legal order. -/
theorem sparse_word {m : RawMolecule} {i : Input} (raw : i.molecule = m) (written : GraphFacts m)
    (o : Oracle i) (bit : Arm i → Option Bool) (label : History → Option Bool)
    (root : i.certified.Atom) (q : Arm i) (p : Site i) (prev : q.previous? = some p)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = root)
    (seen : ∀ c : Arm i, c.occurrence.val.root = root → bit c = label (history c.occurrence))
    (n : Nat) (closed : layersWith (children m) [histories q] n = [])
    (expected : List Bool) (small : expected.length ≤ 1)
    (census : (censusWith (children m) n [histories q]).filterMap (fun e => label e.2) = expected)
    {w : List Bool} (src : o.Source bit q w) : w = expected := by
  obtain ⟨out,walk,rfl⟩ := src
  have initial : Rooted root (Oracle.root bit q) := ⟨valid,on,p,prev⟩
  obtain ⟨ordered,domain⟩ := trace_projection (expansion_histories raw written o bit root) walk (by simpa using initial) n
    [histories q] (.refl _) closed
  have bits := ordered.filterMap (fun e => label e.2)
  rw [census,List.filterMap_map] at bits
  have actual := List.filterMap_congr (l := out) (f := fun x => bit x.cursor)
    (g := fun x => label (histories x.cursor).2) (fun x hx => seen _ (domain x hx).2.1)
  rw [actual]
  cases expected with
  | nil => exact bits.eq_nil
  | cons b tail =>
    have empty : tail = [] := by cases tail <;> simp_all
    subst tail
    exact List.perm_singleton.mp bits

def ringArm (r side : Fin 2) := if r.val = 0 then (if side.val = 0 then 1 else 5)
  else (if side.val = 0 then 4 else 2)

def emitted (r : Fin 2) (h seed : RS) (path : History) : Option Bool :=
  if path = route r 0 then some (h == seed)
  else if path = route r 1 then some (h.swap == seed) else none

private def first (r side : Fin 2) : EdgeHistory := ([3*r.val],[ringArm r side,3*r.val])

private theorem table : ∀ (r side : Fin 2) (h seed : RS),
    layersWith (children molecule) [first r side] 8 = [] ∧
    (censusWith (children molecule) 8 [first r side]).filterMap (fun e => emitted r h seed e.2) =
      [((if side.val = 0 then h else h.swap) == seed)] := by decide +kernel

open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open LocalizedGenericMarkedRecalculation (readback?)
open private start from TetraStereo.Examples.DecalinRootWords
open private rawFacts from TetraStereo.Examples.AntipodalCyclohexaneHands

abbrev publicRead (i : Input) (root : i.certified.Atom) :=
  RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) (origin i root)

/-- For either possible seed, reflection and earlier-stage ordering, the
entire signed sequence on each ring arm consists of the opposite carbon. -/
theorem ring_word {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (s : Fin 4) (side : Fin 2) (id : atom fr s = ringArm r side) (rev : Bool) (h : RS)
    (sense : readback? (RingWrittenPHReadings.geometry i.spatial) (frameRow r) = some h)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i (publicRead i root) rev os seed (cursor fr s) =
      some [((if side.val = 0 then (if rev then h.swap else h) else (if rev then h.swap else h).swap) == seed)] := by
  let o := RingFullPathPairs.stage i (publicRead i root) rev os
  let bit := RingFullPathPairs.likeAt i (publicRead i root) rev seed
  let g := if rev then h.swap else h
  have seen (c : Arm i) (on : c.occurrence.val.root = root) : bit c = emitted r g seed (history c.occurrence) := by
    change (RingFullPathPairs.handAt i _ rev c).map _ = _
    rw [AntipodalCyclohexaneStore.handAt_eq graph geom r atRoot c on h sense rev]
    unfold emitted
    cases rev <;> cases h <;> simp only [g,Bool.false_eq_true,if_false,if_true,RS.swap] <;> split_ifs <;> rfl
  have firstEdge : histories (cursor fr s) = first r side := by
    change ([root.val], DecalinLigandOrder.history (cursor fr s)) = _
    rw [start root fr s,id,atRoot]
    rfl
  obtain ⟨closed,census⟩ := table r side g seed
  rw [←firstEdge] at closed census
  obtain ⟨w,hit,sources⟩ := o.source_exact (f := origin i root) bit
    (RingOccurrenceStereo.rank_total (RingChemicalGraphProof.ready geom _) rev os)
    (cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  exact hit.trans (congrArg some (sparse_word graph rawFacts o bit _ root _ (origin i root) rfl
    (RingGroupedCentre.valid fr s) (fr.direction s).property.1 seen 8 closed _ (by simp) census ((sources w).mpr rfl)))

end TetraStereo.Examples.AntipodalCyclohexaneWords
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneWords.sparse_word
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneWords.ring_word
