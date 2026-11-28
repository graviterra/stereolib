import TetraStereo.Examples.DecalinAuxiliary

/-! The two opposite-carbon auxiliary occurrences of fully hydrogenated
cyclohexane-1,4-diol. The native constitutional comparison ranks the hydroxyl
oxygen, the incoming ring direction, the outgoing ring direction, and hydrogen
in that order on both routes. The coordinates enter only at the final determinant. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneHands
open OneCenter Engine
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open DecalinAuxiliary (History advance history child_history column)
open private column_eq head_and_kind from TetraStereo.Examples.DecalinAuxiliary
open private sourceNode from TetraStereo.Engine.RingRetainedChemicalCoverage
open private raw_adj bound from TetraStereo.Engine.RingAtomicNeighborOrder
open RingRetainedChemicalTrace
open private makeColumn from TetraStereo.Engine.RingRetainedChemicalTrace

/-- The same order of atoms and bonds as the public diol validation. -/
def molecule : RawMolecule := {
  atoms := (List.replicate 6 Element.C ++ ([.O,.H,.H,.H,.H,.H,.H,.O,.H,.H,.H,.H,.H,.H] : List Element)).map AtomSpec.aliphatic
  bonds := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6),(0,7),(6,8),(1,9),(1,10),
    (2,11),(2,12),(3,13),(3,14),(13,15),(4,16),(4,17),(5,18),(5,19)].map fun (a,b) => ⟨a,b,.single⟩ }

def opposite (r : Fin 2) := if r.val = 0 then 3 else 0
def frameRow (r : Fin 2) : List Nat := if r.val = 0 then [13,2,4,14] else [6,5,1,7]

def route (r s : Fin 2) : History :=
  if r.val = 0 then (if s.val = 0 then [3,2,1,0] else [3,4,5,0])
  else (if s.val = 0 then [0,5,4,3] else [0,1,2,3])

private def arms (r s : Fin 2) : List History :=
  let h := route r s
  let other := (route r ⟨1-s.val,by omega⟩)[1]?.getD 20
  [(if r.val = 0 then 13 else 6)::h,h.tail,other::h,(if r.val = 0 then 14 else 7)::h]

namespace HistoryPriority
private def z (m : RawMolecule) (h : History) := RingAtomicNeighborOrder.atomicNumber m (h.headD m.atomCount)

private def next (m : RawMolecule) (previous current : History) : List History :=
  match current with
  | [] => []
  | a :: t => if t.contains a then [] else
      ((m.writtenNeighbors a).filter fun n => previous.head? != some n).map (advance (a :: t))

def key (m : RawMolecule) (n : Nat) (previous current : History) : Key :=
  let o : Observation := ⟨z m current,0,0⟩
  let ks := match n with
    | 0 => []
    | k+1 => (next m previous current).map fun child => key m k current child
  ⟨o,column o ks .atomic,column o ks .duplicate,column o ks .mass⟩

theorem key_step {m : RawMolecule} (n : Nat) (p h : History) :
    key m (n+1) p h = assemble ⟨z m h,0,0⟩ ((next m p h).map (key m n h)) := by
  simp [key,assemble,column_eq]

def closed (m : RawMolecule) : Nat → History → History → Bool
  | 0,p,h => (next m p h).isEmpty
  | n+1,p,h => (next m p h).all (closed m n h)

/-- Finite graph integrity needed by the written-neighbor traversal. -/
def GraphFacts (m : RawMolecule) : Prop := ∀ a : Fin m.atomCount,
    (m.writtenNeighbors a.val).Nodup ∧
    ∀ b : Fin m.atomCount, (b.val ∈ m.writtenNeighbors a.val ↔ 0 < m.bondOrder a.val b.val) ∧
      (∀ n ∈ m.writtenNeighbors a.val, n < m.atomCount)

private theorem cut_neighbors {m : RawMolecule} {i : Input} (written : GraphFacts m) (graph : i.molecule = m)
    (atom focus : i.certified.Atom) :
    (((i.certified.moleculeGraph.neighborFinset atom).erase focus).toList.map Fin.val).Perm
      ((m.writtenNeighbors atom.val).filter (fun n => some focus.val != some n)) := by
  have atom' : atom.val < m.atomCount := graph ▸ bound i atom
  have nd := (Finset.nodup_toList ((i.certified.moleculeGraph.neighborFinset atom).erase focus)).map Fin.val_injective
  apply (List.perm_ext_iff_of_nodup nd ((written ⟨_,atom'⟩).1.filter _)).mpr
  intro n
  simp only [List.mem_map,List.mem_filter,Finset.mem_toList,Finset.mem_erase,
    MoleculeGraph.mem_neighborFinset,bne_iff_ne,ne_eq,Option.some.injEq]
  constructor
  · rintro ⟨b,⟨ne,adj⟩,rfl⟩
    have ab := (raw_adj i atom b).mp adj
    rw [graph] at ab
    exact ⟨((written ⟨_,atom'⟩).2 ⟨_,graph ▸ bound i b⟩).1.mpr ab,fun h => ne (Fin.ext h.symm)⟩
  · rintro ⟨mem,ne⟩
    have bound := ((written ⟨_,atom'⟩).2 ⟨_,atom'⟩).2 n mem
    have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
    rw [graph] at size

    let b : i.certified.Atom := ⟨n,by omega⟩
    refine ⟨b,⟨fun eq => ne (congrArg Fin.val eq.symm),(raw_adj i atom b).mpr ?_⟩,rfl⟩
    rw [graph]
    exact ((written ⟨_,atom'⟩).2 ⟨n,bound⟩).1.mp mem

theorem child_histories {m : RawMolecule} {i : Input} (written : GraphFacts m) (graph : i.molecule = m) (q : Arm i) (p : Site i)
    (prev : q.previous? = some p) (valid : i.certified.LocalizedRerootCursorValid q) :
    ((i.certified.executableLocalizedRerootChildren q).map fun c => history c.occurrence).Perm
      (next m (history p) (history q.occurrence)) := by
  let a := RingAllLigandTwoShell.siteAtom i q.occurrence
  let b := RingAllLigandTwoShell.siteAtom i p
  have ha := RingAllLigandTwoShell.site_current i q.occurrence
  have hb := RingAllLigandTwoShell.site_current i p
  obtain ⟨t,ht,kind⟩ := head_and_kind _ ha
  obtain ⟨u,hu,_⟩ := head_and_kind _ hb
  by_cases real : q.occurrence.val.node.provenance = .realAtom
  · have outside := kind.mp real
    have neighbor := i.certified.mem_localizedRerootNeighborFrames_symm p _ (by
      simpa [CertifiedLocalizedCIPInput.LocalizedRerootCursorValid,prev] using valid)
    let g := RingSecondShellIncidence.realGuard i i.single q p prev neighbor b a real ha hb
    have perm := (g.physical.map Fin.val).trans (cut_neighbors written graph a b)
    have eqs : ((i.certified.executableLocalizedRerootChildren q).map fun c => history c.occurrence) =
        ((i.certified.executableLocalizedRerootChildren q).map g.childAtom).map
          (fun w => advance (history q.occurrence) w.val) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c mem
      obtain ⟨w,cur,hist⟩ := child_history real ha mem
      have eq := Option.some.inj (cur.symm.trans (g.childCurrent c mem))
      simpa [eq] using hist
    rw [eqs,ht,hu]
    simp only [next,List.contains_iff_mem,if_neg outside,List.head?_cons]
    simpa only [List.map_map,Function.comp_def] using perm.map (advance (_ :: t))
  · have inside := not_imp_not.mpr kind.mpr real
    have leaf : q.occurrence.val.node.isDuplicateLeaf = true := by
      obtain ⟨_,_,rr|⟨d,dup,_⟩⟩ := sourceNode i (i.certified.carrierOccurrence_legitimate i.single q.occurrence)
      · contradiction
      · simp [OfficialCIPNode.isDuplicateLeaf,dup]
    have empty : i.certified.executableLocalizedRerootChildren q = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro c mem
      have x := (i.certified.executableLocalizedRerootChildren_mem_iff q c).mp mem
      have y := ((i.certified.mem_intendedLocalizedRerootChildFrames_iff q _).mp x.2).1
      simp_all
    simp [empty,ht,next,Classical.not_not.mp inside]

private theorem key_zero {m : RawMolecule} (p h : History) : key m 0 p h = assemble ⟨z m h,0,0⟩ [] := by
  simp [key,assemble,column_eq]

private theorem formed {m : RawMolecule} (n : Nat) (p h : History) : WellFormed (key m n p h) := by
  induction n generalizing p h with
  | zero => rw [key_zero]; exact assemble_framed _ [] (by simp)
  | succ n ih =>
    rw [key_step]
    apply assemble_framed
    intro k mem
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp mem
    exact ih _ _

open private source_children cursorKey read_valid from TetraStereo.Engine.RingAtomicProfileShape
open private assemble_atomic project from TetraStereo.Engine.RingAtomicMetricIndependence

private theorem node_data {m : RawMolecule} {i : Input} (graph : i.molecule = m)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q) :
    ∃ o, cursorKey i q = assemble o ((i.certified.executableLocalizedRerootChildren q).map (cursorKey i)) ∧
      o.atomic = z m (history q.occurrence) := by
  have read := read_valid valid
  obtain ⟨o,obs,src⟩ := source_children (key_source read) (List.Perm.refl _)
  have atA := RingAllLigandTwoShell.site_current i q.occurrence
  let a := RingAllLigandTwoShell.siteAtom i q.occurrence
  have raw := RingAtomicNeighborOrder.written i a
  have val := RingPyramidalConstitution.key_atomic atA raw read

  obtain ⟨t,hist,_⟩ := head_and_kind _ atA
  have oz : o.atomic = z m (history q.occurrence) := by
    rw [src] at val
    change o.atomic = (RingAtomicNeighborOrder.record i a).element.atomicNumber at val
    rw [hist]
    change o.atomic = RingAtomicNeighborOrder.atomicNumber m a.val
    rw [←graph,RingAtomicNeighborOrder.atomicNumber,raw]
    exact val
  exact ⟨o,src,oz⟩

theorem key_correspondence {m : RawMolecule} {i : Input} (written : GraphFacts m) (graph : i.molecule = m) (n : Nat)
    (q : Arm i) (p : Site i) (prev : q.previous? = some p)
    (valid : i.certified.LocalizedRerootCursorValid q)
    (done : closed m n (history p) (history q.occurrence) = true) :
    project (cursorKey i q) = project (key m n (history p) (history q.occurrence)) := by
  induction n generalizing q p with
  | zero =>
    obtain ⟨o,src,oz⟩ := node_data graph q valid
    have kids := child_histories written graph q p prev valid
    have no : next m (history p) (history q.occurrence) = [] := by simpa [closed] using done
    rw [no] at kids
    have nil := List.map_eq_nil_iff.mp kids.eq_nil
    rw [src,nil,List.map_nil,key_zero]
    exact Prod.ext oz (assemble_atomic _ _ [] [] oz rfl)
  | succ n ih =>
    obtain ⟨o,src,oz⟩ := node_data graph q valid
    have kids := child_histories written graph q p prev valid
    let cs := i.certified.executableLocalizedRerootChildren q
    let shadow (c : Arm i) := key m n (history q.occurrence) (history c.occurrence)
    have child (c : Arm i) (mem : c ∈ cs) : project (cursorKey i c) = project (shadow c) := by
      have pr := i.certified.executableLocalizedRerootChildren_previous q c mem
      have vc := i.certified.localizedRerootChild_valid q c _
        ((i.certified.localizedRerootChildren?_eq_some_iff _ _).mp
          (i.certified.localizedRerootChildren?_eq_some_executable q)) mem
      exact ih c q.occurrence pr vc ((List.all_eq_true.mp done) _
        (kids.mem_iff.mp (List.mem_map_of_mem mem)))
    have same : (cs.map (cursorKey i)).map project = (cs.map shadow).map project := by
      simp only [List.map_map]
      exact List.map_congr_left child
    have reorder : (cs.map shadow).Perm
        ((next m (history p) (history q.occurrence)).map (key m n (history q.occurrence))) := by
      simpa [cs,shadow,List.map_map,Function.comp_def] using kids.map (key m n (history q.occurrence))
    have eq := assemble_perm ⟨z m (history q.occurrence),0,0⟩ reorder (by
      intro k member
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp member
      exact formed n _ _)
    rw [src,key_step,←eq]
    exact Prod.ext oz (assemble_atomic _ _ _ _ oz same)


end HistoryPriority

open HistoryPriority (key closed)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem atomic_order : ∀ r s : Fin 2,
    let h := route r s
    ((arms r s).map fun d => (key molecule 12 h d).atomic.word).Pairwise (· > ·) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem closed_at_twelve : ∀ r s : Fin 2,
    (arms r s).all (closed molecule 12 (route r s)) = true := by decide +kernel

private theorem rawFacts : HistoryPriority.GraphFacts molecule := by
  unfold HistoryPriority.GraphFacts
  decide +kernel

open private cursorKey read_valid from TetraStereo.Engine.RingAtomicProfileShape
open private project from TetraStereo.Engine.RingAtomicMetricIndependence

open CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open private swap_middle from TetraStereo.Examples.DecalinPathSwap

private theorem physical_hand (g : Geometry) (r s : Fin 2) :
    readback? g ((arms r s).map (·.headD 20)) =
      (if s.val = 0 then readback? g (frameRow r) else (readback? g (frameRow r)).map RS.swap) := by
  fin_cases r <;> fin_cases s
  · rfl
  · exact swap_middle g 13 2 4 14
  · rfl
  · exact swap_middle g 6 5 1 7

private theorem graphRows (r : Fin 2) : (RingAtomicNeighborOrder.neighbors molecule (opposite r)).Perm (frameRow r) := by
  apply (RingStereoSiblingPass.legal_order _ _).perm.trans
  fin_cases r <;> decide +kernel

open RingActivePairReport (Slot)
open RingAtomicFramePriority (slotId)
open private frame_perm from TetraStereo.Examples.DecalinFrames

def ids (r s : Fin 2) := (arms r s).map (·.headD 20)

private theorem frame_facts : ∀ r s : Fin 2,
    let h := route r s
    h.headD 20 = opposite r ∧ h.headD 20 ∉ h.tail ∧
    (ids r s).Perm (frameRow r) ∧ (ids r s).map (advance h) = arms r s := by
  decide +kernel

private theorem at_route {i : Input} {f : Site i} (r s : Fin 2) (here : history f = route r s) :
    f.val.node.provenance = .realAtom ∧ (RingAllLigandTwoShell.siteAtom i f).val = opposite r := by
  obtain ⟨t,ht,kind⟩ := head_and_kind f (RingAllLigandTwoShell.site_current i f)
  have facts := frame_facts r s
  rw [←here,ht] at facts
  exact ⟨kind.mpr facts.2.1,facts.1⟩

private theorem lift_row {α β : Type} (f : α → β) {xs : List α} {ys : List β}
    (perm : ys.Perm (xs.map f)) : ∃ row : List α, ys = row.map f ∧ row.Perm xs := by
  change Relation.Comp (· = List.map f ·) List.Perm ys xs
  rw [List.eq_map_comp_perm]
  exact perm

theorem oriented {i : Input} (graph : i.molecule = molecule) {f : Site i}
    (r s : Fin 2) (here : history f = route r s) (fr : RingNestedActivePair.Frame i f) :
    Nonempty (RingConstitutionalHand.OrientationFrame fr (ids r s)) := by
  obtain ⟨real,atom⟩ := at_route r s here
  have focus := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f fr.center).mp fr.recognized
  have center : fr.center.val.val = opposite r := by
    simpa [RingAllLigandTwoShell.siteAtom,focus.2] using atom
  have all := frame_perm fr
  rw [graph,center] at all
  have phys := (frame_facts r s).2.2.1
  have canon := graphRows r
  have ids_perm : (ids r s).Perm ((List.finRange 4).map (slotId fr)) :=
    phys.trans (canon.symm.trans all.symm)
  obtain ⟨row,rowIds,perm⟩ := lift_row _ ids_perm
  let h := route r s
  let armHist (k : Slot) := advance h (slotId fr k)
  have rowH : row.map armHist = arms r s := by
    simpa [armHist,h,rowIds,List.map_map,Function.comp_def] using (frame_facts r s).2.2.2
  have keyEq (k : Slot) :
      (RingRetainedChemicalPreorder.keyFor (fr.direction k)).atomic.word =
        (key molecule 12 h (armHist k)).atomic.word := by
    have mem : fr.arm k ∈ i.certified.executableLocalizedRerootChildren ⟨f,none⟩ := List.get_mem ..
    obtain ⟨w,cur,ch⟩ := child_history (q := ⟨f,none⟩) real focus.2 mem
    have curr := RingAtomicFramePriority.slot_current fr k
    have val := RingAtomicFramePriority.slotNeighbor_val fr k
    have eqw := Option.some.inj (cur.symm.trans curr)
    have hchild : history (fr.direction k).val = armHist k := by
      simpa [here,eqw,val,armHist,h] using ch
    have hk : k ∈ row := perm.mem_iff.mpr (List.mem_finRange _)
    have present : armHist k ∈ arms r s := rowH ▸ List.mem_map_of_mem (f := armHist) hk
    have cl := List.all_eq_true.mp (closed_at_twelve r s) _ present
    let c := RingGroupedCentre.cursor fr k
    have v := RingGroupedCentre.valid fr k
    have proj := HistoryPriority.key_correspondence rawFacts graph 12 c f rfl v (by change closed molecule 12 (history f) (history (fr.direction k).val) = true; rwa [here,hchild])
    have eq := Option.some.inj ((read_valid v).symm.trans (RingRetainedChemicalPreorder.read_key (fr.direction k)))
    have hp := congrArg (fun p : Nat × Column => p.2.word) proj
    change (cursorKey i c).atomic.word = (key molecule 12 (history f) (history (fr.direction k).val)).atomic.word at hp
    rwa [eq,here,hchild] at hp
  have strictWords := atomic_order r s
  dsimp only at strictWords
  rw [←rowH,List.map_map] at strictWords
  have strict : row.Pairwise (fun a b => RingFullPathConstitution.word fr b < RingFullPathConstitution.word fr a) := by
    apply (List.pairwise_map.mp strictWords).imp
    intro a b lt
    apply List.Lex.rel
    simpa only [keyEq,Function.comp_apply] using lt
  have nd : (row.map (RingFullPathConstitution.word fr)).Nodup :=
    List.pairwise_map.mpr (strict.imp (fun h => ne_of_gt h))
  have inj := (List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp
    ((perm.map _).nodup_iff.mp nd)
  exact ⟨RingConstitutionalHand.DescendingFrame.ranked ⟨row,
    fun a b => inj a (List.mem_finRange _) b (List.mem_finRange _),
    ⟨perm,List.pairwise_map.mpr (strict.imp le_of_lt)⟩,rowIds.symm⟩⟩

/-- The completed public auxiliary at a three-bond occurrence: the first
route reads the opposite hydroxyl-bearing carbon frame directly and the second reverses it. -/
theorem public_state {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {f : Site i}
    (r s : Fin 2) (here : history f = route r s) :
    RingChemicalGraphProof.state i f = some
      (((if s.val = 0 then readback? (RingWrittenPHReadings.geometry i.spatial) (frameRow r)
         else (readback? (RingWrittenPHReadings.geometry i.spatial) (frameRow r)).map RS.swap)).map
        fun h => (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  obtain ⟨real,atom⟩ := at_route r s here
  let a := RingAllLigandTwoShell.siteAtom i f
  have current := RingAllLigandTwoShell.site_current i f
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph]
    rw [show a.val = opposite r from atom]
    exact (graphRows r).length_eq.trans (by unfold frameRow; split <;> rfl)
  let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have recg := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f c).mpr ⟨real,current⟩
  obtain ⟨fr,framed⟩ := RingGroupedGeometry.frame_exists recg
  obtain ⟨cert⟩ := oriented graph r s here fr
  have physical := RingConstitutionalHand.centre_read geom cert (RingChemicalGraphProof.ready geom f)
  rw [RingWrittenPHReadings.inputGeometry_eq] at physical
  rw [show readback? (RingWrittenPHReadings.geometry i.spatial) (ids r s) = _ from physical_hand _ r s] at physical
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) a degree
  have noP : RingPyramidalPublication.focusP i f = none := by
    simp [RingPyramidalPublication.focusP,real,current,a] at off ⊢
    exact off
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom f),
    RingFullPathPublication.publish?,framed]
  exact physical

private abbrev vertex {i : Input} (raw : i.molecule = molecule) (a : Fin 20) : i.certified.Atom :=
  (RingHydrogenSpelling.rawVertices i raw).symm a

private theorem three_steps {i : Input} (raw : i.molecule = molecule) (a b c d : Fin 20)
    (bond : 0 < molecule.bondOrder a.val b.val ∧ 0 < molecule.bondOrder b.val c.val ∧
      0 < molecule.bondOrder c.val d.val) (fresh : [d,c,b,a].Nodup) :
    ∃ q : Site i, history q = [d.val,c.val,b.val,a.val] := by
  let v := vertex raw
  have adj (u w : Fin 20) (ok : 0 < molecule.bondOrder u.val w.val) :
      i.certified.moleculeGraph.Adj (v u) (v w) := by
    rw [raw_adj,raw]
    exact ok
  have nodup : [v d,v c,v b,v a].Nodup :=
    fresh.map (RingHydrogenSpelling.rawVertices i raw).symm.injective
  have hd := List.nodup_cons.mp nodup
  have hc := List.nodup_cons.mp hd.2
  have hb := List.nodup_cons.mp hc.2
  let p := RingGraphPaths.Path.step (.step (.step .origin (adj a b bond.1) hb.1)
    (adj b c bond.2.1) hc.1) (adj c d bond.2.2) hd.1
  exact ⟨RingGraphPaths.site p,congrArg (List.map Fin.val) (RingGraphPaths.represents_site p).2.1⟩

/-- Each claimed history actually occurs in the original root's retained digraph. -/
theorem route_exists {i : Input} (raw : i.molecule = molecule) (r s : Fin 2) :
    ∃ q : Site i, history q = route r s := by
  fin_cases r <;> fin_cases s
  · exact three_steps raw 0 1 2 3 (by decide) (by decide)
  · exact three_steps raw 0 5 4 3 (by decide) (by decide)
  · exact three_steps raw 3 4 5 0 (by decide) (by decide)
  · exact three_steps raw 3 2 1 0 (by decide) (by decide)

open private calibrated from TetraStereo.Engine.RingRetainedAuxiliary
open private canonical_perm from TetraStereo.Examples.DecalinFrames

theorem nonflat {i : Input} (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2) :
    (readback? (RingWrittenPHReadings.geometry i.spatial) (frameRow r)).isSome = true := by
  let v := vertex raw ⟨opposite r,by unfold opposite; split <;> decide⟩
  have four : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw]
    exact (graphRows r).length_eq.trans (by unfold frameRow; split <;> rfl)
  let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
  have rows := canonical_perm i c
  rw [raw] at rows
  rw [← RingWrittenPHReadings.inputGeometry_eq]
  exact calibrated i geom c _ (rows.trans (graphRows r)).symm

/-- No auxiliary-hand equality can relate these two occurrences. Both sites
exist, and the coordinate gate itself excludes a flat opposite-carbon frame. -/
theorem opposite_states {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (r : Fin 2) :
    ∃ q t : Site i, history q = route r 0 ∧ history t = route r 1 ∧
      RingChemicalGraphProof.state i q ≠ RingChemicalGraphProof.state i t := by
  obtain ⟨q,hq⟩ := route_exists graph r 0
  obtain ⟨t,ht⟩ := route_exists graph r 1
  obtain ⟨hand,hh⟩ := Option.isSome_iff_exists.mp (nonflat graph geom r)
  refine ⟨q,t,hq,ht,?_⟩
  rw [public_state graph geom r 0 hq,public_state graph geom r 1 ht,hh]
  cases hand <;> decide

end TetraStereo.Examples.AntipodalCyclohexaneHands
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneHands.public_state
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneHands.opposite_states
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneHands.HistoryPriority.key_correspondence
