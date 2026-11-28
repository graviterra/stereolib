import TetraStereo.Examples.AntipodalCyclohexaneHands
import TetraStereo.Engine.RingSecondShellDecision
import TetraStereo.Examples.PairedCyclopropylPaths
import TetraStereo.Examples.DecalinPathSwap

/-! Determine auxiliary hands from the first two atomic-number spheres of a
written molecular graph and the path by which the focus was reached. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylDonorStore
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame)
open RingAtomicFramePriority (slotId)
open RingAtomicNeighborOrder (atomicNumber neighbors)
open DecalinAuxiliary (history advance)
open private head_and_kind from TetraStereo.Examples.DecalinAuxiliary
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private lift_row from TetraStereo.Examples.AntipodalCyclohexaneHands
open private score_lt from TetraStereo.Engine.RingSecondShellDecision

/-- The previous atom leads back along the path. Other previously visited
atoms are terminal duplicate neighbors. A real neighbor contributes the
atomic numbers of its other physical neighbors. -/
def twoShells (m : RawMolecule) (path : List Nat) (id : Nat) : List (List Nat) :=
  [[atomicNumber m id], if id ∈ (advance path id).tail then []
    else RingSecondShellDecision.shell m (path.headD m.atomCount) id]

theorem slot_shells {i : Input} {q : Site i} (fr : Frame i q) (k : RingActivePairReport.Slot) :
    RingSecondShellDecision.score fr k = twoShells i.molecule (history q) (slotId fr k) := by
  have focus := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q fr.center).mp fr.recognized
  obtain ⟨past,hq,_⟩ := head_and_kind q focus.2
  have member : fr.arm k ∈ i.certified.executableLocalizedRerootChildren (⟨q,none⟩ : Arm i) := List.get_mem ..
  obtain ⟨w,hw,move⟩ := DecalinAuxiliary.child_history focus.1 focus.2 member
  have current := RingAtomicFramePriority.slot_current fr k
  change (fr.arm k).occurrence.val.node.current? = _ at current
  obtain rfl := Option.some.inj (hw.symm.trans current)
  have atomId := RingAtomicFramePriority.slotNeighbor_val fr k
  change _ = slotId fr k at atomId
  obtain ⟨t,ht,kind⟩ := head_and_kind (fr.arm k).occurrence hw
  change history (fr.arm k).occurrence = advance (history q) _ at move
  have tailEq := congrArg List.tail (ht.symm.trans move)
  simp only [List.tail_cons] at tailEq
  have decision : (fr.arm k).occurrence.val.node.provenance = .realAtom ↔
      slotId fr k ∉ (advance (history q) (slotId fr k)).tail := by
    simpa only [←atomId,←tailEq] using kind
  change [[atomicNumber i.molecule (slotId fr k)], if _ then _ else []] = _
  unfold twoShells
  by_cases real : (fr.arm k).occurrence.val.node.provenance = .realAtom
  · rw [if_pos real,if_neg (decision.mp real),hq]
    rfl
  · simp only [if_neg real,if_pos (Classical.not_not.mp (fun no => real (decision.mpr no)))]

/-- A descending physical row on the raw history determines the actual public
auxiliary at every admitted geometry. It needs neither a supplied priority
key nor an auxiliary descriptor at another center. -/
theorem state_from_graph {i : Input} {q : Site i}
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {id : Nat} {past row : List Nat} (atPath : history q = id :: past)
    (fresh : id ∉ past) (four : row.length = 4)
    (layout : row.Perm (neighbors i.molecule id))
    (desc : (row.map (twoShells i.molecule (id::past))).Pairwise (· > ·)) :
    ∃ h, readback? (RingWrittenPHReadings.geometry i.spatial) row = some h ∧
      RingChemicalGraphProof.state i q = some (some (.chiral h,.chiral h.swap)) := by
  let a := RingAllLigandTwoShell.siteAtom i q
  have current := RingAllLigandTwoShell.site_current i q
  obtain ⟨t,hq,kind⟩ := head_and_kind q current
  have eqs := List.cons.inj (hq.symm.trans atPath)
  have real := kind.mpr (by rwa [eqs.1,eqs.2])
  have deg : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,show a.val = id from eqs.1,←layout.length_eq,four]
  let c : i.certified.TetrahedralCenter := ⟨a,(i.certified.moleculeGraph.mem_tetrahedralCenterSet a).mpr deg⟩
  have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mpr ⟨real,current⟩
  obtain ⟨fr,framed⟩ := RingGroupedGeometry.frame_exists recognized
  have center := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q fr.center).mp fr.recognized
  have centerId := (congrArg Fin.val (Option.some.inj (center.2.symm.trans current))).trans eqs.1
  have all := frame_perm fr
  rw [centerId] at all
  obtain ⟨xs,ids,perm⟩ := lift_row (slotId fr) (layout.trans all.symm)
  have sorted : xs.Pairwise (fun u v => RingFullPathConstitution.word fr v < RingFullPathConstitution.word fr u) := by
    rw [ids,List.map_map] at desc
    apply (List.pairwise_map.mp desc).imp
    intro u v lt
    apply score_lt fr
    simpa only [slot_shells,atPath,Function.comp_apply] using lt
  have nd := List.pairwise_map.mpr (sorted.imp (fun h => ne_of_gt h))
  have inj := (List.nodup_map_iff_inj_on (List.nodup_finRange 4)).mp
    ((perm.map (RingFullPathConstitution.word fr)).nodup_iff.mp nd)
  have cert : RingConstitutionalHand.DescendingFrame fr row := ⟨xs,
    fun u v => inj u (List.mem_finRange _) v (List.mem_finRange _),
    ⟨perm,List.pairwise_map.mpr (sorted.imp le_of_lt)⟩,ids.symm⟩
  have someHand := RingGroupedGeometry.calibrated ok fr xs perm
  have rowAtoms : fr.atoms xs = row := ids.symm
  rw [rowAtoms,RingWrittenPHReadings.inputGeometry_eq] at someHand
  obtain ⟨h,seen⟩ := Option.isSome_iff_exists.mp someHand
  have hand := RingConstitutionalHand.centre_read ok cert.ranked (RingChemicalGraphProof.ready ok q)
  rw [RingWrittenPHReadings.inputGeometry_eq,seen] at hand
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) a deg
  have notP : RingPyramidalPublication.focusP i q = none := by
    simp [RingPyramidalPublication.focusP,real,current,a] at off ⊢
    exact off
  refine ⟨h,seen,?_⟩
  rw [RingChemicalGraphProof.state_eq,RingPyramidalPublication.publish,notP,
    RingFullPathConstitution.fast_local ok (RingChemicalGraphProof.ready ok q),
    RingFullPathPublication.publish?,framed]
  exact hand

open PairedCyclopropylPaths (route order molecule)
open private swap_middle from TetraStereo.Examples.DecalinPathSwap

open private sorted_eq from TetraStereo.Examples.DecalinAuxiliary

private def retainedKey (m : RawMolecule) (path : List Nat) (id : Nat) : List (List Nat) :=
  [[atomicNumber m id], if id ∈ (advance path id).tail then [] else
    DecalinAuxiliary.sorted (fun x : Nat => x)
      ((RingSecondShellDecision.adjacent m (path.headD m.atomCount) id).map (atomicNumber m))]

private theorem twoShells_eq (m : RawMolecule) (p : List Nat) : twoShells m p = retainedKey m p := by
  funext id
  unfold twoShells retainedKey
  rw [←sorted_eq]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem raw_rows (s : Bool) (k : Fin 5) :
    let p := route s k
    let id := p.headD molecule.atomCount
    p = id :: p.tail ∧ id ∉ p.tail ∧ (order s k).length = 4 ∧
      (order s k).Perm (neighbors molecule id) ∧
      ((order s k).map (twoShells molecule p)).Pairwise (· > ·) := by
  dsimp only
  rw [twoShells_eq]
  refine ⟨?_,?_,?_,List.Perm.trans ?_ (RingStereoSiblingPass.legal_order _ _).perm.symm,?_⟩
  all_goals cases s <;> fin_cases k <;> decide +kernel

/-- All ten donor occurrences publish the calibrated hand of their raw physical
row for every admitted coordinate table on the two-cyclopropyl graph. -/
theorem public_hand {i : Input} {q : Site i} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (side : Bool) (visit : Fin 5)
    (here : history q = route side visit) :
    ∃ h, readback? (RingWrittenPHReadings.geometry i.spatial) (order side visit) = some h ∧
      RingChemicalGraphProof.state i q = some (some (.chiral h,.chiral h.swap)) := by
  obtain ⟨path,fresh,four,layout,sorted⟩ := raw_rows side visit
  apply state_from_graph ok (here.trans path) fresh four
  · simpa only [graph] using layout
  · rw [graph,←path]
    exact sorted

/-- For either arm, the direct and detour visits switch hands at the exit
carbon and retain the same hand at the distal carbon. -/
theorem direct_detour {i : Input} {q r : Site i} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (side distal : Bool)
    (direct : history q = route side (if distal then 2 else 1))
    (detour : history r = route side (if distal then 4 else 3)) :
    ∃ h : RS, let other := if distal then h else h.swap
              RingChemicalGraphProof.state i q = some (some (.chiral h,.chiral h.swap)) ∧
              RingChemicalGraphProof.state i r = some (some (.chiral other,.chiral other.swap)) := by
  obtain ⟨h,sees,first⟩ := public_hand graph ok _ _ direct
  obtain ⟨t,also,last⟩ := public_hand graph ok _ _ detour
  refine ⟨h, first, ?_⟩
  cases distal with
  | false =>
    have switch : readback? (RingWrittenPHReadings.geometry i.spatial) (order side 3) =
        (readback? (RingWrittenPHReadings.geometry i.spatial) (order side 1)).map RS.swap := by
      cases side <;> exact swap_middle _ _ _ _ _
    simp only [Bool.false_eq_true,if_false] at sees also ⊢
    rw [switch,sees] at also
    exact (Option.some.inj also) ▸ last
  | true =>
    have same : order side 4 = order side 2 := by cases side <;> rfl
    simp only [if_true] at sees also ⊢
    rw [same,sees] at also
    exact (Option.some.inj also) ▸ last

end TetraStereo.Examples.PairedCyclopropylDonorStore
assert_kernel_only TetraStereo.Examples.PairedCyclopropylDonorStore.state_from_graph
assert_kernel_only TetraStereo.Examples.PairedCyclopropylDonorStore.public_hand
assert_kernel_only TetraStereo.Examples.PairedCyclopropylDonorStore.direct_detour
