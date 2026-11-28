import TetraStereo.Examples.PairedCyclopropylCensus
import TetraStereo.Examples.PairedCyclopropylDonorLayers
import TetraStereo.Examples.PairedCyclopropylRoot
import TetraStereo.Examples.PairedCyclopropylPeripheral

/-! From the written graph and the admitted coordinates to the central
carbon's public descriptor, through every signed donor occurrence. -/
set_option autoImplicit false
namespace TetraStereo.Examples.PairedCyclopropylPublic
open Engine OneCenter LocalizedGenericMarkedRecalculation CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingWrittenPHReadings (geometry)
open RingGroupedReport (origin)
open PairedCyclopropylPaths (molecule)
open PairedCyclopropylComparison (Hands fromGeometry? public_visits)
open PairedCyclopropylRoot (rootFrame outcome ArmCensus)
open PairedCyclopropylDonorLayers (native_layers row_hand shared_edges edge tag)
open private lift_row from TetraStereo.Examples.AntipodalCyclohexaneHands

theorem arm_census {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (v : i.certified.Atom) (zero : v.val = 0) (h : Bool → Hands)
    (read : ∀ s, fromGeometry? (geometry i.spatial) s = some (h s)) : ArmCensus v h := by
  intro fr slot side rev id os _
  obtain ⟨rows,run,inv,pop⟩ := native_layers graph ok v zero fr slot side id rev os
  refine ⟨_,inv,PairedCyclopropylCensus.assemble side _ rows (tag ∘ edge) RingStereoSphereInventory.Visit.path
    (fun n => (pop n).2.1) ?_ ?_⟩
  · intro n x member
    exact row_hand graph ok zero (read side) run (pop n).2.1 member ((pop n).2.2 x member)
  · intro x mx y my hx hy
    exact shared_edges graph v zero fr slot side id run mx my hx hy

private theorem root_nonflat {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom) (zero : v.val = 0) :
    ∃ c, readback? (geometry i.spatial) rootFrame = some c := by
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph,zero,PairedCyclopropylRoot.neighbors0.length_eq]
    rfl
  let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr degree⟩
  have hr := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff (origin i v) c).mpr ⟨rfl,rfl⟩
  obtain ⟨fr,_⟩ := RingGroupedGeometry.frame_exists hr
  obtain ⟨row,ids,perm⟩ := lift_row (RingAtomicFramePriority.slotId fr) (PairedCyclopropylRoot.frameIds graph zero fr).symm
  have seen := RingGroupedGeometry.calibrated ok fr row perm
  rwa [show fr.atoms row = rootFrame from ids.symm,RingWrittenPHReadings.inputGeometry_eq,Option.isSome_iff_exists] at seen

/-- Seven oriented volumes of written physical neighbors determine the C1
label pair or refusal. An admitted placement supplies all seven readings. -/
def central? (g : SpatialConfiguration) : Option (Option RingNestedActivePair.Labels) := do
  let a ← fromGeometry? (geometry g) false
  let b ← fromGeometry? (geometry g) true
  let c ← readback? (geometry g) rootFrame
  return outcome a b c

theorem central {i : Input} (graph : i.molecule = molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom) (zero : v.val = 0) :
    RingChemicalGraphProof.root i v = central? i.spatial ∧ (central? i.spatial).isSome = true := by
  obtain ⟨a,ha,_⟩ := public_visits graph ok false
  obtain ⟨b,hb,_⟩ := public_visits graph ok true
  obtain ⟨c,hc⟩ := root_nonflat graph ok v zero
  let h := fun s : Bool => if s then b else a
  have all (s : Bool) : fromGeometry? (geometry i.spatial) s = some (h s) := by cases s <;> assumption
  have answer := PairedCyclopropylRoot.root graph ok v zero h (arm_census graph ok v zero h all) c hc
  simpa [central?,ha,hb,hc,h] using (And.intro answer (by rfl : (some (outcome a b c)).isSome = true))

/-- Independent coordinate formula for the raw request. The central carbon
uses both triples of donor hands. Peripheral carbons use a single oriented
volume. A requested atom outside the 25-atom graph fails the request. -/
def predicted (g : SpatialConfiguration) (ids : List Nat) : Option RingGroupedReport.Report := do
  let labels ← central? g
  ids.mapM (PairedCyclopropylPeripheral.expectedRow? g labels)

/-- Every admitted geometry on this written scaffold and every requested atom
list, including the empty list, repetitions and invalid indices. -/
theorem raw_report (g : SpatialConfiguration) {i : Input}
    (admission : LocalizedChemicalRing.admitRawSpatial? molecule g = some i)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule g ids = predicted g ids := by
  obtain ⟨graph,space⟩ := RingChemicalReport.admission_fields admission
  subst g
  obtain ⟨labels,seen⟩ := Option.isSome_iff_exists.mp
    (central graph ok (PairedCyclopropylPaths.atom i graph 0) rfl).2
  simpa [predicted,seen] using PairedCyclopropylPeripheral.raw_agreement i graph ok labels
    (fun v zero => (central graph ok v zero).1.trans seen) ids

end TetraStereo.Examples.PairedCyclopropylPublic
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPublic.central
assert_kernel_only TetraStereo.Examples.PairedCyclopropylPublic.raw_report
