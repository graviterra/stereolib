import TetraStereo.Examples.PairedCyclopropylComparison
import TetraStereo.Examples.PairedCyclopropylEarlierTie
import TetraStereo.Engine.RingUnmarkedExchange

/-! Identical coordinate-derived hand triples on the two cyclopropyl blocks
give a signed exchange on the complete frozen reader and a public root refusal. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylTiedRoot
open Engine OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Visible frozen)
open RingGroupedReport (origin)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open RingNestedActivePair (Frame)
open RingActivePairReport (Slot)
open PairedCyclopropylPaths (molecule route)
open PairedCyclopropylComparison (fromGeometry? public_visits)
open PairedCyclopropylEarlierTie (carrier exchange exchange_slot)
open DecalinAuxiliary (history)
open private aut index graph image image_history origin_fixed route_exchange outside
  from TetraStereo.Examples.PairedCyclopropylEarlierTie
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private repeatedWords from TetraStereo.Engine.RingUnmarkedExchange
attribute [local instance] lexOrd

def EqualHands (i : Input) : Prop :=
  fromGeometry? (RingWrittenPHReadings.geometry i.spatial) false =
    fromGeometry? (RingWrittenPHReadings.geometry i.spatial) true

private theorem visible_same {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (same : EqualHands i)
    (root : i.certified.Atom) (zero : root.val = 0) (q : Site i) (vis : Visible (origin i root) q) :
    RingChemicalGraphProof.state i q = RingChemicalGraphProof.state i (image raw q) := by
  have im := image_history raw q
  by_cases hit : ∃ s v, history q = route s v
  · obtain ⟨s,v,path⟩ := hit
    have there : history (image raw q) = route (!s) v := im.trans (by rw [path,route_exchange])
    obtain ⟨h,seen,cells⟩ := public_visits raw ok s
    obtain ⟨t,also,other⟩ := public_visits raw ok (!s)
    have both : fromGeometry? (RingWrittenPHReadings.geometry i.spatial) s =
        fromGeometry? (RingWrittenPHReadings.geometry i.spatial) (!s) := by
      cases s <;> first | exact same | exact same.symm
    obtain rfl := Option.some.inj (seen.symm.trans (both.trans also))
    rw [cells v q path,other v _ there]
  · have inv : ((history q).map exchange).map exchange = history q := by
      unfold history
      simp only [List.map_map]
      conv_rhs => rw [←List.map_id (q.val.node.history.map Fin.val),List.map_map]
      apply List.map_congr_left
      intro a _
      exact (graph (index i raw a)).2.1
    have off : ¬ ∃ s v, history (image raw q) = route s v := by
      rintro ⟨s,v,path⟩
      exact hit ⟨!s,v,inv.symm.trans (by rw [←im,path,route_exchange])⟩
    have vis' := (RingGeometryAutomorphism.visible (aut i raw) (origin i root) q).mpr vis
    change Visible (image raw (origin i root)) (image raw q) at vis'
    rw [origin_fixed raw root zero] at vis'
    rw [outside raw ok zero vis hit,outside raw ok zero vis' off]

theorem signed_frozen {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (same : EqualHands i)
    (root : i.certified.Atom) (zero : root.val = 0) :
    let read := frozen (RingChemicalGraphProof.state i) (origin i root)
    RingGeometryExchange.Frozen (carrier i raw) read read := by
  dsimp only
  intro q _
  have eqn := RingGeometryAutomorphism.frozen_transport (aut i raw) (origin i root) q.occurrence
    (visible_same raw ok same root zero)
  change _ = frozen _ (image raw (origin i root)) (image raw q.occurrence) at eqn
  rwa [origin_fixed raw root zero] at eqn

private def idAt : Slot → Nat := ![1,2,3,14]
private def record : Slot → AtomSpec := fun k => AtomSpec.aliphatic (![Element.F,.H,.C,.C] k)
private theorem rows : ((List.finRange 4).map idAt).Perm (RingAtomicNeighborOrder.neighbors molecule 0) ∧
    Function.Injective idAt ∧ (∀ k, molecule.atoms[idAt k]? = some (record k)) ∧
    (∀ s t, s ≠ t → (record s).element.atomicNumber = (record t).element.atomicNumber → s = 2 ∨ s = 3) := by
  refine ⟨List.Perm.trans ?_ (RingStereoSiblingPass.legal_order _ _).perm.symm,?_⟩
  all_goals decide +kernel

private theorem layout {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) (fr : Frame i (origin i root)) :
    ∃ e : Equiv.Perm Slot, ∀ k, atom fr (e k) = idAt k := by
  have cur := ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  have cen : root = fr.center.val := Option.some.inj cur
  have phys := frame_perm fr
  rw [raw,←cen,zero] at phys
  have perm := rows.1.trans phys.symm
  change ((List.finRange 4).map idAt).Perm ((List.finRange 4).map (atom fr)) at perm
  have each (k : Slot) : ∃ s, atom fr s = idAt k := by
    obtain ⟨s,_,eqn⟩ := List.mem_map.mp (perm.mem_iff.mp (List.mem_map_of_mem (List.mem_finRange k)))
    exact ⟨s,eqn⟩
  choose sel slot using each
  have inj : Function.Injective sel := fun a b h => rows.2.1 ((slot a).symm.trans (h ▸ slot b))
  exact ⟨Equiv.ofBijective sel ⟨inj,Finite.surjective_of_injective inj⟩,slot⟩

private theorem few {i : Input} (raw : i.molecule = molecule) {root : i.certified.Atom}
    (fr : Frame i (origin i root)) (e : Equiv.Perm Slot) (ids : ∀ k, atom fr (e k) = idAt k) :
    (RingUnmarkedExchange.repeated fr).length < 3 := by
  let cs (k : Slot) := RingRetainedChemicalPreorder.keyFor (fr.direction (e k))
  have native (k : Slot) := RingRetainedChemicalPreorder.read_key (fr.direction (e k))
  have formed (k : Slot) := (RingRetainedChemicalTrace.key_source (native k)).formed
  have z (k : Slot) : (cs k).root.atomic = (record k).element.atomicNumber := by
    apply RingPyramidalConstitution.key_atomic (q := cursor fr (e k))
      (a := (RingAtomicFramePriority.slotNeighbor fr (e k)).val)
    · exact RingAtomicFramePriority.slot_current fr _
    · rw [RingAtomicFramePriority.slotNeighbor_val,raw]
      change molecule.atoms[atom fr (e k)]? = _
      rw [ids]; exact rows.2.2.1 k
    · exact native k
  let both : Finset Slot := {e 2,e 3}
  have sub : (RingUnmarkedExchange.repeated fr).toFinset ⊆ both := by
    intro s mem
    obtain ⟨k,rfl⟩ := e.surjective s
    have m := List.mem_toFinset.mp mem
    obtain ⟨_,test⟩ := List.mem_filter.mp m
    obtain ⟨v,_,h⟩ := List.any_eq_true.mp test
    obtain ⟨j,rfl⟩ := e.surjective v
    have ne : k ≠ j := fun eq => (bne_iff_ne.mp (Bool.and_eq_true_iff.mp h).1) (congrArg e eq)
    have words : RingFullPathConstitution.word fr (e k) = RingFullPathConstitution.word fr (e j) := by
      simpa using (beq_iff_eq.mp (Bool.and_eq_true_iff.mp h).2)
    have atomic : (cs k).root.atomic = (cs j).root.atomic := by
      apply le_antisymm <;> apply Nat.le_of_not_gt
      · exact fun lt => (ne_of_lt (RingPyramidalConstitution.word_lt_of_Z (formed j) (formed k) lt)) words.symm
      · exact fun lt => (ne_of_lt (RingPyramidalConstitution.word_lt_of_Z (formed k) (formed j) lt)) words
    rw [z,z] at atomic
    rcases rows.2.2.2 k j ne atomic with h|h <;> simp [both,h]
  have card := Finset.card_le_card sub
  have nd : (RingUnmarkedExchange.repeated fr).Nodup := by
    unfold RingUnmarkedExchange.repeated repeatedWords
    exact (List.nodup_finRange 4).filter _
  rw [List.toFinset_card_of_nodup nd] at card
  exact lt_of_le_of_lt card (by simp [both,e.injective.ne (show (2 : Slot) ≠ 3 by decide)])

theorem public_refusal {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (same : EqualHands i)
    (root : i.certified.Atom) (zero : root.val = 0) :
    RingChemicalGraphProof.state i (origin i root) = some none := by
  have deg : Fintype.card (i.certified.moleculeGraph.Neighbor root) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,raw,zero]
    exact rows.1.length_eq.symm.trans (by decide)
  let c : i.certified.TetrahedralCenter := ⟨root,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr deg⟩
  have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff (origin i root) c).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recognized
  obtain ⟨e,ids⟩ := layout raw root zero fr
  have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) root deg
  have noP : RingPyramidalPublication.focusP i (origin i root) = none := by
    change (if True then (some root).filter (RingPyramidalPublication.phosphorus i) else none) = none
    simp [off]
  apply RingUnmarkedExchange.state_refusal fr ok noP (few raw fr e ids) (e.injective.ne (show (2 : Slot) ≠ 3 by decide))
    (carrier i raw) _ (exchange_slot raw root zero fr (e 2) (e 3) (by rw [ids,ids]; rfl)) (signed_frozen raw ok same root zero)
  intro p hp
  obtain rfl := Option.some.inj hp
  exact (fr.direction (e 2)).property.1.symm

end TetraStereo.Examples.PairedCyclopropylTiedRoot
assert_kernel_only TetraStereo.Examples.PairedCyclopropylTiedRoot.signed_frozen
assert_kernel_only TetraStereo.Examples.PairedCyclopropylTiedRoot.public_refusal
