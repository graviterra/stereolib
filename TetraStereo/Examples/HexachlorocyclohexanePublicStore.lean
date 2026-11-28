import TetraStereo.Examples.AntipodalCyclohexaneHands
import TetraStereo.Examples.HexachlorocyclohexaneFamily

/-! Constitutional priority and both public auxiliary labels on the simple
carbon paths of fully written hexachlorocyclohexane. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace TetraStereo.Examples.HexachlorocyclohexanePublicStore
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open DecalinAuxiliary (History advance history child_history)
open BlueBookHexachlorocyclohexane (molecule site path order)
open HexachlorocyclohexaneFamily (fixedFrame)
open AntipodalCyclohexaneHands.HistoryPriority (key closed)
open RingRetainedChemicalTrace
open RingActivePairReport (Slot)
open RingAtomicFramePriority (slotId)
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private lift_row from TetraStereo.Examples.AntipodalCyclohexaneHands
open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary
open private cursorKey read_valid from TetraStereo.Engine.RingAtomicProfileShape
open private swap_middle from TetraStereo.Examples.DecalinPathSwap

def route (r : Fin 6) (cw : Bool) (k : Fin 5) : History := (path r cw k).reverse
def carbon (r : Fin 6) (cw : Bool) (k : Fin 5) := site r cw (k.val+1)
private def arms (r : Fin 6) (cw : Bool) (k : Fin 5) :=
  (order r cw k).map (advance (route r cw k))

private theorem rawFacts : AntipodalCyclohexaneHands.HistoryPriority.GraphFacts molecule := by
  unfold AntipodalCyclohexaneHands.HistoryPriority.GraphFacts
  decide +kernel

private theorem frame_facts : ∀ (r : Fin 6) (cw : Bool) (k : Fin 5),
    let h := route r cw k
    h.headD 18 = carbon r cw k ∧ h.headD 18 ∉ h.tail ∧
    (order r cw k).Perm (fixedFrame (carbon r cw k)) := by decide +kernel

private theorem graphRows (c : Nat) (hc : c < 6) :
    (RingAtomicNeighborOrder.neighbors molecule c).Perm (fixedFrame c) := by
  apply (RingStereoSiblingPass.legal_order _ _).perm.trans
  have table : ∀ c : Fin 6, ((List.range molecule.atomCount).filter fun n => 0 < molecule.bondOrder c.val n).Perm
      (fixedFrame c.val) := by decide +kernel
  exact table ⟨c,hc⟩

open private calibrated from TetraStereo.Engine.RingRetainedAuxiliary
open private canonical_perm from TetraStereo.Examples.DecalinFrames

theorem nonflat {i : Input} (raw : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (c : Fin 6) :
    (readback? (RingWrittenPHReadings.geometry i.spatial) (fixedFrame c.val)).isSome = true := by
  let v := (RingHydrogenSpelling.rawVertices i raw).symm ⟨c.val,by change c.val < 18; omega⟩
  have four : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw]
    exact (graphRows _ c.isLt).length_eq.trans rfl
  let center : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
  have rows := canonical_perm i center
  rw [raw] at rows
  rw [← RingWrittenPHReadings.inputGeometry_eq]
  exact calibrated i geom center _ (rows.trans (graphRows _ c.isLt)).symm

private theorem physical_hand (g : Geometry) (r : Fin 6) (cw : Bool) (k : Fin 5) :
    readback? g (order r cw k) =
      (if cw then readback? g (fixedFrame (carbon r cw k))
       else (readback? g (fixedFrame (carbon r cw k))).map RS.swap) := by
  have rows : ∀ (r : Fin 6) (cw : Bool) (k : Fin 5), let c := carbon r cw k
      order r cw k = if cw then fixedFrame c else [c+6,(c+1)%6,(c+5)%6,c+12] := by decide +kernel
  rw [rows]
  cases cw
  · exact swap_middle _ _ _ _ _
  · rfl

private def priorities (r : Fin 6) (cw : Bool) (k : Fin 5) : Bool :=
  let h := route r cw k
  let xs := arms r cw k
  xs.all (closed molecule 12 h) &&
    decide ((xs.map fun d => (key molecule 12 h d).atomic.word).Pairwise (· > ·))

private theorem priorities0 (cw : Bool) (k : Fin 5) : priorities 0 cw k = true := by
  cases cw <;> fin_cases k <;> decide +kernel

private theorem priorities1 (cw : Bool) (k : Fin 5) : priorities 1 cw k = true := by
  cases cw <;> fin_cases k <;> decide +kernel

private theorem priorities2 (cw : Bool) (k : Fin 5) : priorities 2 cw k = true := by
  cases cw <;> fin_cases k <;> decide +kernel

private theorem priorities3 (cw : Bool) (k : Fin 5) : priorities 3 cw k = true := by
  cases cw <;> fin_cases k <;> decide +kernel

private theorem priorities4 (cw : Bool) (k : Fin 5) : priorities 4 cw k = true := by
  cases cw <;> fin_cases k <;> decide +kernel

private theorem priorities5 (cw : Bool) (k : Fin 5) : priorities 5 cw k = true := by
  cases cw <;> fin_cases k <;> decide +kernel

private theorem table (r : Fin 6) (cw : Bool) (k : Fin 5) : priorities r cw k = true := by
  fin_cases r
  · exact priorities0 cw k
  · exact priorities1 cw k
  · exact priorities2 cw k
  · exact priorities3 cw k
  · exact priorities4 cw k
  · exact priorities5 cw k
/-- At offset k+1 the two carbon arms have equal atomic observations through
depth 4-k measured from their first atoms. At the next depth the incoming
route has real children where the outgoing route has reached the ring duplicate. -/
theorem first_atomic_difference : ∀ (r : Fin 6) (cw : Bool) (k : Fin 5),
    let h := route r cw k
    let prev := advance h (site r cw k.val)
    let next := advance h (site r cw (k.val+2))
    let word := fun depth direction => (key molecule depth h direction).atomic.word
    word (4-k.val) prev = word (4-k.val) next ∧ word (5-k.val) prev > word (5-k.val) next := by
  decide +kernel

private theorem at_route {i : Input} {f : Site i} (r : Fin 6) (cw : Bool) (k : Fin 5) (here : history f = route r cw k) :
    f.val.node.provenance = .realAtom ∧ (RingAllLigandTwoShell.siteAtom i f).val = carbon r cw k := by
  obtain ⟨t,ht,kind⟩ := head_and_kind f (RingAllLigandTwoShell.site_current i f)
  have facts := frame_facts r cw k
  rw [←here,ht] at facts
  exact ⟨kind.mpr facts.2.1,facts.1⟩

theorem oriented {i : Input} (graph : i.molecule = molecule) {f : Site i}
    (r : Fin 6) (cw : Bool) (k : Fin 5) (here : history f = route r cw k) (fr : RingNestedActivePair.Frame i f) :
    Nonempty (RingConstitutionalHand.OrientationFrame fr (order r cw k)) := by
  obtain ⟨real,atom⟩ := at_route r cw k here
  have focus := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f fr.center).mp fr.recognized
  have center : fr.center.val.val = carbon r cw k := by
    simpa [RingAllLigandTwoShell.siteAtom,focus.2] using atom
  have all := frame_perm fr
  rw [graph,center] at all
  have phys := (frame_facts r cw k).2.2
  have canon := graphRows (carbon r cw k) (Nat.mod_lt _ (by decide : 0 < 6))
  have ids_perm : (order r cw k).Perm ((List.finRange 4).map (slotId fr)) :=
    phys.trans (canon.symm.trans all.symm)
  obtain ⟨row,rowIds,perm⟩ := lift_row _ ids_perm
  let h := route r cw k
  let armHist (slot : Slot) := advance h (slotId fr slot)
  have rowH : row.map armHist = arms r cw k := by
    simpa [arms,armHist,h,List.map_map,Function.comp_def] using congrArg (List.map (advance h)) rowIds.symm
  have keyEq (slot : Slot) :
      (RingRetainedChemicalPreorder.keyFor (fr.direction slot)).atomic.word =
        (key molecule 12 h (armHist slot)).atomic.word := by
    have mem : fr.arm slot ∈ i.certified.executableLocalizedRerootChildren ⟨f,none⟩ := List.get_mem ..
    obtain ⟨w,cur,ch⟩ := child_history (q := ⟨f,none⟩) real focus.2 mem
    have curr := RingAtomicFramePriority.slot_current fr slot
    have val := RingAtomicFramePriority.slotNeighbor_val fr slot
    have eqw := Option.some.inj (cur.symm.trans curr)
    have hchild : history (fr.direction slot).val = armHist slot := by
      simpa [here,eqw,val,armHist,h] using ch
    have hk : slot ∈ row := perm.mem_iff.mpr (List.mem_finRange _)
    have present : armHist slot ∈ arms r cw k := rowH ▸ List.mem_map_of_mem (f := armHist) hk
    have cl := List.all_eq_true.mp ((Bool.and_eq_true_iff.mp (table r cw k)).1) _ present
    let c := RingGroupedCentre.cursor fr slot
    have v := RingGroupedCentre.valid fr slot
    have proj := AntipodalCyclohexaneHands.HistoryPriority.key_correspondence rawFacts graph 12 c f rfl v (by change closed molecule 12 (history f) (history (fr.direction slot).val) = true; rwa [here,hchild])
    have eq := Option.some.inj ((read_valid v).symm.trans (RingRetainedChemicalPreorder.read_key (fr.direction slot)))
    have hp := congrArg (fun p : Nat × Column => p.2.word) proj
    change (cursorKey i c).atomic.word = (key molecule 12 (history f) (history (fr.direction slot).val)).atomic.word at hp
    rwa [eq,here,hchild] at hp
  have strictWords := of_decide_eq_true ((Bool.and_eq_true_iff.mp (table r cw k)).2)
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

/-- The public auxiliary along either cyclic path reads the same local frame with the sign set by traversal direction. -/
theorem public_state {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {f : Site i}
    (r : Fin 6) (cw : Bool) (k : Fin 5) (here : history f = route r cw k) :
    RingChemicalGraphProof.state i f = some
      (((if cw then readback? (RingWrittenPHReadings.geometry i.spatial) (fixedFrame (carbon r cw k))
         else (readback? (RingWrittenPHReadings.geometry i.spatial) (fixedFrame (carbon r cw k))).map RS.swap)).map
        fun h => (LocalizedTetrahedralRSPseudoDescriptor.chiral h,
          LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap)) := by
  obtain ⟨real,atom⟩ := at_route r cw k here
  let a := RingAllLigandTwoShell.siteAtom i f
  have current := RingAllLigandTwoShell.site_current i f
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph]
    rw [show a.val = carbon r cw k from atom]
    exact (graphRows (carbon r cw k) (Nat.mod_lt _ (by decide : 0 < 6))).length_eq.trans rfl
  let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have recg := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f c).mpr ⟨real,current⟩
  obtain ⟨fr,framed⟩ := RingGroupedGeometry.frame_exists recg
  obtain ⟨cert⟩ := oriented graph r cw k here fr
  have physical := RingConstitutionalHand.centre_read geom cert (RingChemicalGraphProof.ready geom f)
  rw [RingWrittenPHReadings.inputGeometry_eq] at physical
  rw [show readback? (RingWrittenPHReadings.geometry i.spatial) (order r cw k) = _ from physical_hand _ r cw k] at physical
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) a degree
  have noP : RingPyramidalPublication.focusP i f = none := by
    simp [RingPyramidalPublication.focusP,real,current,a] at off ⊢
    exact off
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,noP,
    RingFullPathConstitution.fast_local geom (RingChemicalGraphProof.ready geom f),
    RingFullPathPublication.publish?,framed]
  exact physical


open RingGraphPaths (Path)
open RingGroupedReport (origin)
open RingActiveDistanceSchedule (frozen distance)
open HexachlorocyclohexaneFamily (hand directionHand forwardSite)
open private back from TetraStereo.Examples.HexachlorocyclohexaneFamily
open private raw_adj bound from TetraStereo.Engine.RingAtomicNeighborOrder

/-- Identify the root-to-carbon simple path, preserving its direction and offset. -/
def tag? (r : Fin 6) (h : List Nat) : Option (Bool × Fin 5) :=
  (([true,false] : List Bool).flatMap fun cw => (List.finRange 5).map (cw,·)).find?
    fun t => h == route r t.1 t.2

private theorem tag_some {r : Fin 6} {h : History} {cw : Bool} {k : Fin 5}
    (found : tag? r h = some (cw,k)) : h = route r cw k :=
  eq_of_beq (List.find?_some (p := fun (t : Bool × Fin 5) => h == route r t.1 t.2) found)

private theorem atom_bound {i : Input} (graph : i.molecule = molecule) (a : i.certified.Atom) : a.val < 18 := by
  simpa only [graph] using bound i a

private def incident (a : Nat) := (List.range molecule.atomCount).filter fun n => 0 < molecule.bondOrder a n

private theorem four_only {i : Input} (graph : i.molecule = molecule) (a : i.certified.Atom)
    (four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4) : a.val < 6 := by
  have test : ∀ n : Fin 18, (incident n.val).length = 4 → n.val < 6 := by decide +kernel
  rw [RingAtomicNeighborOrder.degree_eq,graph] at four
  exact test ⟨_,atom_bound graph a⟩ (((RingStereoSiblingPass.legal_order _ _).perm.length_eq).symm.trans four)

private theorem no_pyramids : ∀ a : Fin 18, RingAtomicNeighborOrder.neutralPyramidal molecule a.val = false := by
  decide +kernel

private def neighbors := molecule.writtenNeighbors

private theorem edges : ∀ a b : Fin 18, b.val ∈ neighbors a.val ↔ 0 < molecule.bondOrder a.val b.val := by
  decide +kernel
private def expand (h : List Nat) : List (List Nat) :=
  ((neighbors (h.headD 18)).filter fun b => !h.contains b).map (· :: h)

private def paths (r : Nat) : Nat → List (List Nat)
  | 0 => [[r]]
  | n+1 => (paths r n).flatMap expand

private theorem enumerated {i : Input} (graph : i.molecule = molecule) {r a h}
    (p : Path i r h a) :
    (h.map Fin.val).headD 18 = a.val ∧ h.map Fin.val ∈ paths r.val (h.length-1) := by
  induction p with
  | origin => exact ⟨rfl,List.mem_singleton_self _⟩
  | @step hist cur next prev edge fresh ih =>
    have positive : 0 < hist.length := by cases prev <;> simp
    have n : (next::hist).length - 1 = (hist.length - 1) + 1 := by simp; omega
    have adj := (raw_adj i cur next).mp edge
    rw [graph] at adj
    have outside : next.val ∉ hist.map Fin.val := by
      rintro h
      obtain ⟨b,mem,e⟩ := List.mem_map.mp h
      exact fresh (Fin.ext e ▸ mem)
    refine ⟨rfl,?_⟩
    rw [n,paths,List.mem_flatMap]
    exact ⟨_,ih.2,List.mem_map.mpr ⟨next.val,by
      rw [List.mem_filter,ih.1]
      exact ⟨(edges ⟨cur.val,atom_bound graph cur⟩ ⟨next.val,atom_bound graph next⟩).mpr adj,by simpa using outside⟩,rfl⟩⟩


private def scan (r : Fin 6) : Nat → List History → Bool
  | 0,_ => true
  | n+1,hs => hs.all (fun h => decide (6 ≤ h.headD 18) || h.headD 18 == r.val ||
      (tag? r h).isSome) && scan r n (hs.flatMap expand)

private theorem scan_covers (r : Fin 6) (fuel start : Nat)
    (yes : scan r fuel (paths r.val start) = true) {n : Nat} (within : n < fuel)
    {h : History} (mem : h ∈ paths r.val (start+n)) (c : h.headD 18 < 6)
    (other : h.headD 18 ≠ r.val) : (tag? r h).isSome = true := by
  induction fuel generalizing start n with
  | zero => omega
  | succ fuel ih =>
    have pair := Bool.and_eq_true_iff.mp yes
    cases n with
    | zero =>
      have hit := List.all_eq_true.mp pair.1 h (by simpa using mem)
      change (decide (6 ≤ h.headD 18) || h.headD 18 == r.val || (tag? r h).isSome) = true at hit
      simpa only [decide_eq_false (Nat.not_le.mpr c),beq_eq_false_iff_ne.mpr other,Bool.false_or] using hit
    | succ n =>
      apply ih (start+1) pair.2 (by omega : n < fuel)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using mem

private theorem scanned : ∀ r : Fin 6, scan r 18 [[r.val]] = true := by decide +kernel

private theorem outside {i : Input} (graph : i.molecule = molecule)
    {root : i.certified.Atom} (r : Fin 6) (atRoot : root.val = r.val)
    (q : Site i) (on : q.val.root = root) (other : q.val.node.current? ≠ some root)
    (off : tag? r (history q) = none) : RingChemicalGraphProof.state i q = some none := by
  apply (RingChemicalGraphProof.state_eq i q).trans
  apply RingChemicalGraphProof.skips
  rintro ⟨real,a,current,poss⟩
  obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
  have same : b = a := Option.some.inj (hb.symm.trans current)
  subst b
  rw [on] at path
  have hp : RingPyramidalPublication.phosphorus i a = false := by
    change (RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val && _) = false
    simp [graph,no_pyramids ⟨_,atom_bound graph a⟩]
  have four : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
    simpa [RingPyramidalPublication.eligible,hp] using poss
  obtain ⟨lastAtom,mem⟩ := enumerated graph path
  rw [atRoot] at mem
  have upper := RingGraphAuxiliaries.length_bound path
  have size := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  rw [graph] at size
  change _ = 18 at size
  have distinct : a.val ≠ r.val := fun h => other (current.trans (congrArg some (Fin.ext (h.trans atRoot.symm))))
  have hit := scan_covers r 18 0 (scanned r) (by omega : q.val.node.history.length-1 < 18)
    (by simpa using mem) (lastAtom ▸ four_only graph a four) (lastAtom ▸ distinct)
  change (tag? r (history q)).isSome = true at hit
  simp [off] at hit

/-- The actual frozen donor at any cursor of a named root, for an arbitrary
admitted coordinate table having the given five cyclic frame signs. -/
theorem handAt_tag {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom}
    (r : Fin 6) (atRoot : root.val = r.val) (q : Arm i) (on : q.occurrence.val.root = root)
    (p : Fin 32) (signs : ∀ k, readback? (RingWrittenPHReadings.geometry i.spatial)
      (fixedFrame (forwardSite r k)) = some (hand p k)) (rev : Bool) :
    RingFullPathPairs.handAt i (frozen (RingChemicalGraphProof.state i) (origin i root)) rev q =
      (tag? r (history q.occurrence)).map fun t =>
        if rev then (directionHand p t.1 t.2).swap else directionHand p t.1 t.2 := by
  cases found : tag? r (history q.occurrence) with
  | none =>
    have cell : frozen (RingChemicalGraphProof.state i) (origin i root) q.occurrence = some none := by
      unfold frozen
      split_ifs with foreign visible
      · exact (foreign on).elim
      · exact outside graph r atRoot q.occurrence on visible.2 found
      · rfl
    unfold RingFullPathPairs.handAt
    rw [cell]
    cases rev <;> rfl
  | some t =>
    obtain ⟨cw,k⟩ := t
    have here := tag_some found
    have info : ∀ (r : Fin 6) (cw : Bool) (k : Fin 5), 1 < (route r cw k).length ∧
        carbon r cw k ≠ r.val ∧ carbon r cw k = forwardSite r (if cw then k else back k) := by decide +kernel
    have f := info r cw k
    have d : (history q.occurrence).length = distance q.occurrence + 1 := by
      simpa only [history,List.length_map,distance] using
        i.certified.carrierOccurrence_history_length_eq_address_succ q.occurrence
    rw [here] at d
    have off : q.occurrence.val.node.current? ≠ some root := by
      intro eqn
      have a := (at_route r cw k here).2
      rw [Option.some.inj ((RingAllLigandTwoShell.site_current i q.occurrence).symm.trans eqn),atRoot] at a
      exact f.2.1 a.symm
    have active : frozen (RingChemicalGraphProof.state i) (origin i root) q.occurrence =
        RingChemicalGraphProof.state i q.occurrence := by
      change (if q.occurrence.val.root ≠ root then _ else if 0 < distance q.occurrence ∧ _ then _ else _) = _
      rw [if_neg (not_not_intro on),if_pos ⟨by have := f.1; omega,off⟩]
    unfold RingFullPathPairs.handAt
    rw [active,public_state graph geom r cw k here,f.2.2,signs]
    cases cw <;> cases rev <;> simp [directionHand] <;> rfl

end TetraStereo.Examples.HexachlorocyclohexanePublicStore
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicStore.public_state
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicStore.handAt_tag
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicStore.first_atomic_difference
