import TetraStereo.Examples.PairedCyclopropylPublic
import TetraStereo.Examples.PairedCyclopropylTiedRoot

/-! Signed exchange, identical physical hand triples, and central refusal
describe exactly the same admitted placements of this written graph. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylExchangeClass
open Engine OneCenter
open LocalizedChemicalRing (Input)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open RingNestedActivePair (Frame)
open PairedCyclopropylPaths (molecule)
open PairedCyclopropylTiedRoot (EqualHands)
open private idAt layout few from TetraStereo.Examples.PairedCyclopropylTiedRoot
open private root_nonflat from TetraStereo.Examples.PairedCyclopropylPublic

/-- Any carrier preserving the signed frozen cells and taking the actual
first carbon ligand to the second, on an actual frame of the central carbon. -/
def SignedExchange (i : Input) (root : i.certified.Atom) : Prop :=
  ∃ (fr : Frame i (origin i root)) (a b : Fin 4) (c : RingGeometryExchange.Carrier i i),
    atom fr a = 3 ∧ atom fr b = 14 ∧ c.domain (cursor fr a) ∧ c.image (cursor fr a) = cursor fr b ∧
    let read := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) (origin i root)
    RingGeometryExchange.Frozen c read read

private theorem degree {i : Input} (raw : i.molecule = molecule) (root : i.certified.Atom)
    (zero : root.val = 0) : Fintype.card (i.certified.moleculeGraph.Neighbor root) = 4 := by
  rw [RingAtomicNeighborOrder.degree_eq,raw,zero,PairedCyclopropylRoot.neighbors0.length_eq]
  rfl

theorem refusal_iff_hands {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0) :
    RingChemicalGraphProof.root i root = some none ↔ EqualHands i := by
  obtain ⟨a,ha,_⟩ := PairedCyclopropylComparison.public_visits raw ok false
  obtain ⟨b,hb,_⟩ := PairedCyclopropylComparison.public_visits raw ok true
  obtain ⟨c,hc⟩ := root_nonflat raw ok root zero
  rw [(PairedCyclopropylPublic.central raw ok root zero).1]
  by_cases same : a = b
  · simp [PairedCyclopropylPublic.central?,ha,hb,hc,PairedCyclopropylRoot.outcome,EqualHands,same]
  · simp [PairedCyclopropylPublic.central?,ha,hb,hc,PairedCyclopropylRoot.outcome,EqualHands,same]
    split <;> simp

theorem exchange_iff_refusal {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0) :
    SignedExchange i root ↔ RingChemicalGraphProof.root i root = some none := by
  have deg := degree raw root zero
  constructor
  · rintro ⟨fr,a,b,c,ha,hb,dom,target,frozen⟩
    have ne : a ≠ b := by rintro rfl; omega
    obtain ⟨e,ids⟩ := layout raw root zero fr
    have off := RingHydrogenLeafGeometry.notP_of_degree_four (i := i) root deg
    have noP : RingPyramidalPublication.focusP i (origin i root) = none := by
      change (if True then (some root).filter (RingPyramidalPublication.phosphorus i) else none) = none
      simp [off]
    rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
    exact RingUnmarkedExchange.state_refusal fr ok noP (few raw fr e ids) ne c dom target frozen
  · intro refused
    have hands := (refusal_iff_hands raw ok root zero).mp refused
    let t : i.certified.TetrahedralCenter := ⟨root,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr deg⟩
    have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff (origin i root) t).mpr ⟨rfl,rfl⟩
    obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists recognized
    obtain ⟨e,ids⟩ := layout raw root zero fr
    refine ⟨fr,e 2,e 3,PairedCyclopropylEarlierTie.carrier i raw,ids 2,ids 3,?_,
      PairedCyclopropylEarlierTie.exchange_slot raw root zero fr (e 2) (e 3) (by rw [ids,ids]; rfl),
      PairedCyclopropylTiedRoot.signed_frozen raw ok hands root zero⟩
    intro p hp
    obtain rfl := Option.some.inj hp
    exact (fr.direction (e 2)).property.1.symm

theorem exchange_iff_hands {i : Input} (raw : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom) (zero : root.val = 0) :
    SignedExchange i root ↔ EqualHands i :=
  (exchange_iff_refusal raw ok root zero).trans (refusal_iff_hands raw ok root zero)

end TetraStereo.Examples.PairedCyclopropylExchangeClass
assert_kernel_only TetraStereo.Examples.PairedCyclopropylExchangeClass.exchange_iff_hands
assert_kernel_only TetraStereo.Examples.PairedCyclopropylExchangeClass.exchange_iff_refusal
