import TetraStereo.Examples.DecalinPathSwap
import TetraStereo.Engine.RingPyramidalPathProvenance
import TetraStereo.Engine.RingAtomicMetricIndependence
import TetraStereo.Engine.RingAtomicProfileShape

/-! Constitutional comparison at the far fusion atom of the two long decalin
routes. Histories distinguish a real return direction from a ring duplicate. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinAuxiliary
open DecalinFrames
abbrev History := List Nat
def advance (h : History) (w : Nat) := if h[1]? = some w then h.tail else w :: h
def z (h : History) := if h.headD 28 < 10 then 6 else 1

/-- Reroot the retained path tree locally. Going back on a real history removes
its head. All other bonds extend it, including a terminal ring closure. -/
def next (previous current : History) : List History :=
  match current with
  | [] => []
  | a :: t =>
    if t.contains a then [] else
    ((molecule.writtenNeighbors a).filter fun n => previous.head? != some n).map
      (advance (a :: t))

/-- The atomic numbers of each distance sphere in descending order.
Here the first differing sphere has extra atoms on exactly one side. -/
def rows (previous current : History) (depth : Nat) : List (List Nat) :=
  let rec go (front : List (History × History)) : Nat → List (List Nat)
    | 0 => []
    | n+1 => (List.replicate (front.countP (fun p => z p.2 == 6)) 6 ++ List.replicate (front.countP (fun p => z p.2 == 1)) 1) ::
        go (front.flatMap fun p => (next p.1 p.2).map fun q => (p.2,q)) n
  go [(previous,current)] depth

def route (root side : Fin 2) : History :=
  let h := if root.val = 0 then [1,3,5,4,2,0] else [0,2,4,5,3,1]
  if side.val = 0 then h else h.map DecalinPathSwap.exchange

def arms (r s : Fin 2) : List History :=
  let h := route r s
  let other := (route r ⟨1-s.val,by omega⟩)[1]?.getD 28
  [h.tail,other :: h,r.val :: h,(11-r.val) :: h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem sphere_order : ∀ r s : Fin 2,
    let h := route r s
    let dirs := arms r s
    ((next [] h).Perm dirs) ∧
    (dirs.map (fun d => rows h d 6)).Pairwise (· > ·) ∧
    rows h (dirs[0]?.getD []) 5 = rows h (dirs[1]?.getD []) 5 := by
  decide +kernel

open Engine.RingRetainedChemicalTrace
open private shallow deep byDescending makeColumn mergeLayers from TetraStereo.Engine.RingRetainedChemicalTrace


def sorted {α κ : Type} [LinearOrder κ] (f : α → κ) (xs : List α) :=
  let le (a b : α) := decide (f b ≤ f a)
  match xs with
  | [] => []
  | [a] => [a]
  | [a,b] => if le a b then [a,b] else [b,a]
  | [a,b,c] => if le a b then
      if le a c then (if le b c then [a,b,c] else [a,c,b]) else [c,a,b]
    else if le b c then (if le a c then [b,a,c] else [b,c,a]) else [c,b,a]
  | ys => byDescending f ys

private theorem sorted_eq {α κ : Type} [LinearOrder κ] (f : α → κ) (xs : List α) :
    byDescending f xs = sorted f xs := by
  rcases xs with _|⟨a,_|⟨b,_|⟨c,_|⟨d,ds⟩⟩⟩⟩
  all_goals first | rfl | simp [sorted,byDescending,List.mergeSort,List.MergeSort.Internal.splitInTwo,List.merge] <;> split_ifs <;> simp_all

def column (o : Observation) (ks : List Key) (s : Stage) : Column :=
  let a := sorted (shallow s) ks
  let b := sorted (deep s) ks
  let row (cs : List Key) := cs.map fun k => k.root.atStage s
  let levels := [row a,row b] :: b.foldr (fun k acc => mergeLayers (k.column s).levels acc) []
  ⟨[o.atStage s] :: levels.flatten,levels⟩

private theorem column_eq (o : Observation) (ks : List Key) (s : Stage) :
    makeColumn o ks s = column o ks s := by simp [makeColumn,column,sorted_eq]

def key (n : Nat) (previous current : History) : Key :=
  let o : Observation := ⟨z current,0,0⟩
  let ks := match n with
    | 0 => []
    | k+1 => (next previous current).map fun child => key k current child
  ⟨o,column o ks .atomic,column o ks .duplicate,column o ks .mass⟩

theorem key_step (n : Nat) (p h : History) :
    key (n+1) p h = assemble ⟨z h,0,0⟩ ((next p h).map (key n h)) := by
  simp [key,assemble,column_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem atomic_order : ∀ r s : Fin 2,
    let h := route r s
    ((arms r s).map fun d => (key 15 h d).atomic.word).Pairwise (· > ·) := by
  decide +kernel

def closed : Nat → History → History → Bool
  | 0,p,h => (next p h).isEmpty
  | n+1,p,h => (next p h).all (closed n h)

theorem key_stable {n : Nat} {p h : History} (hc : closed n p h = true) (more : Nat) :
    key (n+more) p h = key n p h := by
  induction n generalizing p h with
  | zero =>
    have empty : next p h = [] := by simpa [closed] using hc
    cases more <;> simp [key,empty]
  | succ n ih =>
    rw [Nat.succ_add,key_step,key_step]
    congr 1
    apply List.map_congr_left
    intro child mem
    exact ih ((List.all_eq_true.mp hc) child mem)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem closed_at_fifteen : ∀ r s : Fin 2,
    (arms r s).all (closed 15 (route r s)) = true := by decide +kernel

open OneCenter Engine
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open private classified from TetraStereo.Engine.RingPyramidalPathProvenance
open private parent_get from TetraStereo.Engine.RingSingleCycleOrigin

def history {i : Input} (q : Site i) := q.val.node.history.map Fin.val

theorem child_history {i : Input} {q c : Arm i} {a : i.certified.Atom}
    (real : q.occurrence.val.node.provenance = .realAtom)
    (current : q.occurrence.val.node.current? = some a)
    (hc : c ∈ i.certified.executableLocalizedRerootChildren q) :
    ∃ w : i.certified.Atom, c.occurrence.val.node.current? = some w ∧
      history c.occurrence = advance (history q.occurrence) w.val := by
  have src := (i.certified.executableLocalizedRerootChildren_mem_iff q c).mp hc
  obtain ⟨leaf,neighbor,_⟩ := (i.certified.mem_intendedLocalizedRerootChildFrames_iff q _).mp src.2
  have mem : c ∈ RingRetainedAuxiliary.frame i.certified q.occurrence := by
    apply (i.certified.executableLocalizedRerootChildren_mem_iff _ _).mpr
    refine ⟨src.1,(i.certified.mem_intendedLocalizedRerootChildFrames_iff _ _).mpr
      ⟨leaf,neighbor,?_⟩⟩
    intro _ contra
    contradiction
  obtain ⟨w,hw,_,fork⟩ := classified i.certified i.single q.occurrence a ⟨real,current⟩ _
    (i.certified.localizedRerootChildren?_eq_some_executable _) c mem
  refine ⟨w,hw,?_⟩
  have test : (history q.occurrence)[1]? = (q.occurrence.val.node.parent?).map Fin.val := by
    simp [history,List.getElem?_map,parent_get]
  rcases fork with ⟨cert,eq,_,parent,_⟩|⟨extend,parent,_⟩
  · rw [advance,test,parent]
    simp [history,eq,←cert.target_history_tail i.certified,List.map_tail]
  · have ne : q.occurrence.val.node.parent?.map Fin.val ≠ some w.val := by
      cases he : q.occurrence.val.node.parent? with
      | none => simp
      | some v => simpa using (fun e : v.val = w.val => parent (he.trans (congrArg some (Fin.ext e))))
    rw [advance,test,if_neg ne]
    simp [history,extend,OfficialCIPNode.extend_history]

open private sourceNode from TetraStereo.Engine.RingRetainedChemicalCoverage
open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder
open private atom_bound from TetraStereo.Examples.DecalinFrames

private theorem head_and_kind {i : Input} (q : Site i) {a : i.certified.Atom}
    (current : q.val.node.current? = some a) :
    ∃ t, history q = a.val :: t ∧
      (q.val.node.provenance = .realAtom ↔ a.val ∉ t) := by
  obtain ⟨v,hv,alt⟩ := sourceNode i (i.certified.carrierOccurrence_legitimate i.single q)
  have veq := Option.some.inj (hv.symm.trans current)
  subst v
  rcases alt with real|⟨d,dup,_,head,_,mem⟩
  · obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    obtain rfl := Option.some.inj (hv.symm.trans hb)
    have aux {h : List i.certified.Atom} {w : i.certified.Atom}
        (p : RingGraphPaths.Path i q.val.root h w) :
        ∃ t, h.map Fin.val = w.val :: t ∧ w.val ∉ t := by
      cases p with
      | origin => exact ⟨[],rfl,List.not_mem_nil⟩
      | step _ _ fresh =>
        exact ⟨_,rfl,fun m => by
          obtain ⟨u,hum,eq⟩ := List.mem_map.mp m
          exact fresh (Fin.ext eq ▸ hum)⟩
    obtain ⟨t,eq,ne⟩ := aux path
    exact ⟨t,eq,by simp [real,ne]⟩
  · cases h : q.val.node.history with
    | nil => simp [h] at head
    | cons v vs =>
      have eq : v = a := by simpa [h] using head
      have member : v.val ∈ vs.map Fin.val := List.mem_map_of_mem (by simpa [h,←eq] using mem)
      exact ⟨vs.map Fin.val,by simp [history,h,eq],by simp [dup,←eq,member]⟩

set_option maxRecDepth 100000 in
private theorem written : ∀ a : Fin 28,
    (molecule.writtenNeighbors a.val).Nodup ∧
    ∀ b : Fin 28, (b.val ∈ molecule.writtenNeighbors a.val ↔ 0 < molecule.bondOrder a.val b.val) ∧
      (∀ n ∈ molecule.writtenNeighbors a.val, n < 28) := by decide +kernel

private theorem cut_neighbors {i : Input} (graph : i.molecule = molecule)
    (atom focus : i.certified.Atom) :
    (((i.certified.moleculeGraph.neighborFinset atom).erase focus).toList.map Fin.val).Perm
      ((molecule.writtenNeighbors atom.val).filter (fun n => some focus.val != some n)) := by
  have atom' : atom.val < 28 := atom_bound graph _
  have nd := (Finset.nodup_toList ((i.certified.moleculeGraph.neighborFinset atom).erase focus)).map Fin.val_injective
  apply (List.perm_ext_iff_of_nodup nd ((written ⟨_,atom'⟩).1.filter _)).mpr
  intro n
  simp only [List.mem_map,List.mem_filter,Finset.mem_toList,Finset.mem_erase,
    MoleculeGraph.mem_neighborFinset,bne_iff_ne,ne_eq,Option.some.injEq]
  constructor
  · rintro ⟨b,⟨ne,adj⟩,rfl⟩
    have ab := (raw_adj i atom b).mp adj
    rw [graph] at ab
    exact ⟨((written ⟨_,atom'⟩).2 ⟨_,atom_bound graph b⟩).1.mpr ab,fun h => ne (Fin.ext h.symm)⟩
  · rintro ⟨mem,ne⟩
    have bound := ((written ⟨_,atom'⟩).2 0).2 n mem
    have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
    rw [graph] at size
    change _ = 28 at size
    let b : i.certified.Atom := ⟨n,by omega⟩
    refine ⟨b,⟨fun eq => ne (congrArg Fin.val eq.symm),(raw_adj i atom b).mpr ?_⟩,rfl⟩
    rw [graph]
    exact ((written ⟨_,atom'⟩).2 ⟨n,bound⟩).1.mp mem

theorem child_histories {i : Input} (graph : i.molecule = molecule) (q : Arm i) (p : Site i)
    (prev : q.previous? = some p) (valid : i.certified.LocalizedRerootCursorValid q) :
    ((i.certified.executableLocalizedRerootChildren q).map fun c => history c.occurrence).Perm
      (next (history p) (history q.occurrence)) := by
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
    have perm := (g.physical.map Fin.val).trans (cut_neighbors graph a b)
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

private theorem key_zero (p h : History) : key 0 p h = assemble ⟨z h,0,0⟩ [] := by
  simp [key,assemble,column_eq]

private theorem formed (n : Nat) (p h : History) : WellFormed (key n p h) := by
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

private theorem atomic_values : ∀ a : Fin 28,
    RingAtomicNeighborOrder.atomicNumber molecule a.val = (if a.val < 10 then 6 else 1) := by
  decide +kernel

private theorem node_data {i : Input} (graph : i.molecule = molecule)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q) :
    ∃ o, cursorKey i q = assemble o ((i.certified.executableLocalizedRerootChildren q).map (cursorKey i)) ∧
      o.atomic = z (history q.occurrence) := by
  have read := read_valid valid
  obtain ⟨o,obs,src⟩ := source_children (key_source read) (List.Perm.refl _)
  have atA := RingAllLigandTwoShell.site_current i q.occurrence
  let a := RingAllLigandTwoShell.siteAtom i q.occurrence
  have raw := RingAtomicNeighborOrder.written i a
  have val := RingPyramidalConstitution.key_atomic atA raw read
  have number := atomic_values ⟨a.val,atom_bound graph a⟩
  rw [←graph,RingAtomicNeighborOrder.atomicNumber,raw] at number
  obtain ⟨t,hist,_⟩ := head_and_kind _ atA
  have oz : o.atomic = z (history q.occurrence) := by
    rw [src] at val
    exact val.trans (by simpa [hist,z,a] using number)
  exact ⟨o,src,oz⟩

theorem key_correspondence {i : Input} (graph : i.molecule = molecule) (n : Nat)
    (q : Arm i) (p : Site i) (prev : q.previous? = some p)
    (valid : i.certified.LocalizedRerootCursorValid q)
    (done : closed n (history p) (history q.occurrence) = true) :
    project (cursorKey i q) = project (key n (history p) (history q.occurrence)) := by
  induction n generalizing q p with
  | zero =>
    obtain ⟨o,src,oz⟩ := node_data graph q valid
    have kids := child_histories graph q p prev valid
    have no : next (history p) (history q.occurrence) = [] := by simpa [closed] using done
    rw [no] at kids
    have nil := List.map_eq_nil_iff.mp kids.eq_nil
    rw [src,nil,List.map_nil,key_zero]
    exact Prod.ext oz (assemble_atomic _ _ [] [] oz rfl)
  | succ n ih =>
    obtain ⟨o,src,oz⟩ := node_data graph q valid
    have kids := child_histories graph q p prev valid
    let cs := i.certified.executableLocalizedRerootChildren q
    let shadow (c : Arm i) := key n (history q.occurrence) (history c.occurrence)
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
        ((next (history p) (history q.occurrence)).map (key n (history q.occurrence))) := by
      simpa [cs,shadow,List.map_map,Function.comp_def] using kids.map (key n (history q.occurrence))
    have eq := assemble_perm ⟨z (history q.occurrence),0,0⟩ reorder (by
      intro k member
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp member
      exact formed n _ _)
    rw [src,key_step,←eq]
    exact Prod.ext oz (assemble_atomic _ _ _ _ oz same)

open CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open private swap_middle from TetraStereo.Examples.DecalinPathSwap

private theorem cycle_three (g : Geometry) (a b c d : Nat) :
    readback? g [b,c,a,d] = readback? g [a,b,c,d] := by
  have turn (A B C D : CartesianPoint3) : CartesianPoint3.orientedVolume B C A D =
      CartesianPoint3.orientedVolume A B C D := by simp only [CartesianPoint3.orientedVolume]; ring
  simp only [readback?,List.mapM_cons,List.mapM_nil]
  cases g a <;> cases g b <;> cases g c <;> cases g d <;>
    first | rfl | (change descriptorOfOrientedVolume? (CartesianPoint3.orientedVolume _ _ _ _) = _
                   rw [turn]; rfl)

theorem physical_hand (g : Geometry) (r s : Fin 2) :
    readback? g ((arms r s).map (·.headD 28)) =
      (if s.val = 0 then readback? g (junctionRow (1-r.val))
       else (readback? g (junctionRow (1-r.val))).map RS.swap) := by
  fin_cases r <;> fin_cases s
  · exact cycle_three g 0 3 8 11
  · exact (cycle_three g 0 8 3 11).trans (swap_middle g 0 3 8 11)
  · exact cycle_three g 1 2 6 10
  · exact (cycle_three g 1 6 2 10).trans (swap_middle g 1 2 6 10)

open RingActivePairReport (Slot)
open RingAtomicFramePriority (slotId)
open private frame_perm graph_rows from TetraStereo.Examples.DecalinFrames

def ids (r s : Fin 2) := (arms r s).map (·.headD 28)

private theorem frame_facts : ∀ r s : Fin 2,
    let h := route r s
    h.headD 28 = 1-r.val ∧ h.headD 28 ∉ h.tail ∧
    (ids r s).Perm (junctionRow (1-r.val)) ∧ (ids r s).map (advance h) = arms r s := by
  decide +kernel

private theorem at_route {i : Input} {f : Site i} (r s : Fin 2) (here : history f = route r s) :
    f.val.node.provenance = .realAtom ∧ (RingAllLigandTwoShell.siteAtom i f).val = 1-r.val := by
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
  have center : fr.center.val.val = 1-r.val := by
    simpa [RingAllLigandTwoShell.siteAtom,focus.2] using atom
  have all := frame_perm fr
  rw [graph,center] at all
  have phys := (frame_facts r s).2.2.1
  have canon := graph_rows ⟨1-r.val,by omega⟩
  have ids_perm : (ids r s).Perm ((List.finRange 4).map (slotId fr)) :=
    phys.trans (canon.symm.trans all.symm)
  obtain ⟨row,rowIds,perm⟩ := lift_row _ ids_perm
  let h := route r s
  let armHist (k : Slot) := advance h (slotId fr k)
  have rowH : row.map armHist = arms r s := by
    simpa [armHist,h,rowIds,List.map_map,Function.comp_def] using (frame_facts r s).2.2.2
  have keyEq (k : Slot) :
      (RingRetainedChemicalPreorder.keyFor (fr.direction k)).atomic.word =
        (key 15 h (armHist k)).atomic.word := by
    have mem : fr.arm k ∈ i.certified.executableLocalizedRerootChildren ⟨f,none⟩ := List.get_mem ..
    obtain ⟨w,cur,ch⟩ := child_history (q := ⟨f,none⟩) real focus.2 mem
    have curr := RingAtomicFramePriority.slot_current fr k
    have val := RingAtomicFramePriority.slotNeighbor_val fr k
    have eqw := Option.some.inj (cur.symm.trans curr)
    have hchild : history (fr.direction k).val = armHist k := by
      simpa [here,eqw,val,armHist,h] using ch
    have hk : k ∈ row := perm.mem_iff.mpr (List.mem_finRange _)
    have present : armHist k ∈ arms r s := rowH ▸ List.mem_map_of_mem (f := armHist) hk
    have cl := List.all_eq_true.mp (closed_at_fifteen r s) _ present
    let c := RingGroupedCentre.cursor fr k
    have v := RingGroupedCentre.valid fr k
    have proj := key_correspondence graph 15 c f rfl v (by change closed 15 (history f) (history (fr.direction k).val) = true; rwa [here,hchild])
    have eq := Option.some.inj ((read_valid v).symm.trans (RingRetainedChemicalPreorder.read_key (fr.direction k)))
    have hp := congrArg (fun p : Nat × Column => p.2.word) proj
    change (cursorKey i c).atomic.word = (key 15 (history f) (history (fr.direction k).val)).atomic.word at hp
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

/-- The completed public auxiliary at a five-bond occurrence: the first
route reads the opposite fusion frame directly and the second reverses it. -/
theorem public_state {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {f : Site i}
    (r s : Fin 2) (here : history f = route r s) :
    RingChemicalGraphProof.state i f = some
      (((if s.val = 0 then readback? (RingWrittenPHReadings.geometry i.spatial) (junctionRow (1-r.val))
         else (readback? (RingWrittenPHReadings.geometry i.spatial) (junctionRow (1-r.val))).map RS.swap)).map
        fun h => (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  obtain ⟨real,atom⟩ := at_route r s here
  let a := RingAllLigandTwoShell.siteAtom i f
  have current := RingAllLigandTwoShell.site_current i f
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph]
    rw [show a.val = 1-r.val from atom]
    exact (graph_rows ⟨1-r.val,by omega⟩).length_eq.trans (by unfold junctionRow; split <;> rfl)
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

end TetraStereo.Examples.DecalinAuxiliary

assert_kernel_only TetraStereo.Examples.DecalinAuxiliary.sphere_order
assert_kernel_only TetraStereo.Examples.DecalinAuxiliary.public_state
