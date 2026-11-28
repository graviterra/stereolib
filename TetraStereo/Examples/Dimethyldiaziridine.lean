import TetraStereo.Engine.RingPyramidalTwoShell
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Explicit-hydrogen 1,2-dimethyldiaziridine. The methyl groups on opposite
sides of the ring define the trans coordinate example. -/
set_option autoImplicit false
namespace TetraStereo.Engine.Dimethyldiaziridine
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingAtomicNeighborOrder (neighbors)
open RingSecondShellDecision (signature)
open private row? from TetraStereo.Engine.RingChemicalReport
attribute [local instance] lexOrd
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def molecule : RawMolecule := {
  atoms := ([.N,.N,.C,.C,.C] ++ List.replicate 8 .H : List Element).map AtomSpec.aliphatic
  bonds := [(0,1),(0,2),(1,2),(0,3),(1,4),(2,5),(2,6),(3,7),(3,8),(3,9),
    (4,10),(4,11),(4,12)].map fun (a,b) => ⟨a,b,.single⟩ }

/-- Rational coordinate model. Multiplying every z coordinate by -1 reflects the scaffold. -/
def geometry (z : Int) : SpatialConfiguration := ⟨[
  ⟨0,0,0⟩,⟨2,0,0⟩,⟨1,2,0⟩,⟨-1,-1,2*z⟩,⟨3,-1,-2*z⟩,
  ⟨1,3,z⟩,⟨1,3,-z⟩,⟨-2,-1,2*z⟩,⟨-1,-2,2*z⟩,⟨-1,-1,3*z⟩,
  ⟨4,-1,-2*z⟩,⟨3,-2,-2*z⟩,⟨3,-1,-3*z⟩]⟩

def nitrogen (second : Bool) : Nat := if second then 1 else 0

def priorityRow (second : Bool) : List Nat := if second then [0,2,4] else [1,2,3]

/-- The directly attached nitrogen wins at sphere one. Removing the incoming bond
leaves [N,H,H] on the ring carbon and [H,H,H] on the methyl carbon. -/
theorem atomic_rows (b : Bool) :
    (priorityRow b).map (signature molecule (nitrogen b)) =
      [[[7],[6,6]],[[6],[7,1,1]],[[6],[1,1,1]]] := by
  have shells (a : Nat) (xs : List Nat)
      (eq : (RingSecondShellDecision.adjacent molecule (nitrogen b) a).map
        (RingAtomicNeighborOrder.atomicNumber molecule) = xs)
      (sorted : xs.Pairwise (· ≥ ·)) :
      RingSecondShellDecision.shell molecule (nitrogen b) a = xs := by
    unfold RingSecondShellDecision.shell
    rw [eq]
    exact List.mergeSort_eq_self (r := (· ≥ ·)) sorted
  cases b <;> simp only [priorityRow,if_false,if_true,Bool.false_eq_true,List.map_cons,List.map_nil,signature]
  all_goals
    rw [shells _ [6,6] (by decide +kernel) (by decide),
      shells _ [7,1,1] (by decide +kernel) (by decide),shells _ [1,1,1] (by decide +kernel) (by decide)]
    rfl

private theorem rank (b : Bool) :
    (neighbors molecule (nitrogen b)).Perm (priorityRow b) ∧
    ((priorityRow b).map (signature molecule (nitrogen b))).Pairwise (· > ·) := by
  constructor
  · apply (RingStereoSiblingPass.legal_order _ _).perm.trans
    cases b <;> decide +kernel
  · rw [atomic_rows]
    decide +kernel

def predicted (g : SpatialConfiguration) (b : Bool) : Option RingNestedActivePair.Labels :=
  (readback? (RingWrittenPHReadings.geometry g) (priorityRow b ++ [nitrogen b])).map
    fun h => (.chiral h,.chiral h.swap)

theorem trans_readings (b : Bool) :
    predicted (geometry 1) b = some (.chiral .S,.chiral .R) ∧
    predicted (geometry (-1)) b = some (.chiral .R,.chiral .S) := by
  cases b <;> decide +kernel

private theorem selected {i : Input} (a : i.certified.Atom) (b : Bool) (idx : a.val = nitrogen b)
    (graph : i.molecule = molecule) (recognized : RingPyramidalNitrogen.constrainedRaw molecule (nitrogen b) = true) :
    RingPyramidalPublication.phosphorus i a = true := by
  have ng : RingPyramidalNitrogen.constrained i a = true := by
    simp only [RingPyramidalNitrogen.constrained,graph,idx,recognized]
  have card : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph,idx,(rank b).1.length_eq]
    cases b <;> rfl
  cases b <;> simp [RingPyramidalPublication.phosphorus,ng,card,graph,idx,nitrogen,molecule,AtomSpec.aliphatic]

private theorem raw_of_recognized (g : SpatialConfiguration) {i : Input}
    (admission : LocalizedChemicalRing.admitRawSpatial? molecule g = some i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (recognized : ∀ b, RingPyramidalNitrogen.constrainedRaw molecule (nitrogen b) = true) :
    RingHydrogenReport.fromRaw? molecule g [0,1] = some [(0,predicted g false),(1,predicted g true)] := by
  obtain ⟨graph,spatial⟩ := RingChemicalReport.admission_fields admission
  have bound (b : Bool) : nitrogen b < i.certified.certified.input.molecule.atomCount := by
    rw [i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,graph]
    cases b <;> decide
  let n (b : Bool) : i.certified.Atom := ⟨nitrogen b,bound b⟩
  have closed : RingHydrogenCompletion.plan i.molecule = [] := by rw [graph]; decide +kernel
  have root (b : Bool) := RingPyramidalTwoShell.root_of_graph_order valid (n b)
    (selected (n b) b rfl graph (recognized b)) (priorityRow b)
    (by simpa only [graph,n] using (rank b).1)
    (by simpa only [graph,n] using (rank b).2)
  simp only [RingWrittenPHReadings.inputGeometry_eq,spatial] at root
  rw [← graph,← spatial,show [0,1] = [n false,n true].map Fin.val from rfl,
    RingWrittenPHReadings.fromRaw_closed_report i closed valid]
  unfold RingChemicalReport.report?
  simp only [List.mapM_cons,List.mapM_nil,row?,root,Option.map_some,bind,pure]
  rw [spatial]
  rfl

private def transGeometry (mirror : Bool) := geometry (if mirror then -1 else 1)

private theorem admitted (mirror : Bool) :
    (LocalizedChemicalRing.admitRawSpatial? molecule (transGeometry mirror)).isSome = true := by
  cases mirror <;> decide +kernel

private def sample (mirror : Bool) : Input :=
  (LocalizedChemicalRing.admitRawSpatial? molecule (transGeometry mirror)).get (admitted mirror)

private def adjacent (i : Input) (a : i.certified.Atom) :=
  (List.finRange _).filter fun b => decide (i.certified.moleculeGraph.Adj a b)

private theorem canonical (i : Input) (c : i.certified.TetrahedralCenter) :
    i.certified.canonicalNeighborList c = adjacent i c.val := by
  apply (Finset.sortedLT_sort _).eq_of_mem_iff
  · exact ((List.sortedLT_finRange _).pairwise.sublist (List.filter_sublist ..)).sortedLT
  · intro v
    simp [adjacent,Finset.mem_sort,MoleculeGraph.mem_neighborFinset]

private def volume (i : Input) (xs : List i.certified.Atom) : Option ℚ := do
  let a ← i.certified.spatialPointAt? (← xs[0]?)
  let b ← i.certified.spatialPointAt? (← xs[1]?)
  let c ← i.certified.spatialPointAt? (← xs[2]?)
  let d ← i.certified.spatialPointAt? (← xs[3]?)
  return CartesianPoint3.orientedVolume a b c d

open private raw_adj from TetraStereo.Engine.RingAtomicNeighborOrder

private theorem gate_of_rows (i : Input) (good : ∀ a : i.certified.Atom, (adjacent i a).length = 4 →
    ((volume i (adjacent i a)).any (· != 0)) = true) :
    LocalizedChemicalRing.coordinatesAdmitted i = true := by
  apply decide_eq_true
  intro c
  let z : i.certified.TetrahedralCenter := c
  have four := i.certified.canonicalNeighborList_length z
  have nonflat := good z.1 (canonical i z ▸ four)
  rw [← canonical i z] at nonflat
  have eqn : volume i (i.certified.canonicalNeighborList z) =
      LocalizedActualPhysicalBranchDecision.coordinateVolume? i.certified c := by
    unfold volume LocalizedActualPhysicalBranchDecision.coordinateVolume?
    simp only [List.getElem?_eq_getElem (by omega : 0 < (i.certified.canonicalNeighborList z).length),
      List.getElem?_eq_getElem (by omega : 1 < (i.certified.canonicalNeighborList z).length),
      List.getElem?_eq_getElem (by omega : 2 < (i.certified.canonicalNeighborList z).length),
      List.getElem?_eq_getElem (by omega : 3 < (i.certified.canonicalNeighborList z).length)]
    rfl
  rw [eqn] at nonflat
  unfold LocalizedChemicalRingPhysicalAdmission.centerAdmitted
  change (match LocalizedActualPhysicalBranchDecision.coordinateVolume? i.certified c with
    | none => false | some v => decide (v ≠ 0)) = true
  cases h : LocalizedActualPhysicalBranchDecision.coordinateVolume? i.certified c with
  | none => rw [h] at nonflat; contradiction
  | some v => simpa only [h,Option.any_some,bne_iff_ne,decide_eq_true_eq] using nonflat

private def writtenNeighbors (m : RawMolecule) {k : Nat} (a : Fin k) :=
  (List.finRange k).filter fun b => decide (0 < m.bondOrder a.val b.val)

private def writtenVolume (g : SpatialConfiguration) {k : Nat} (xs : List (Fin k)) : Option ℚ := do
  let a ← g.positions[(← xs[0]?).val]?
  let b ← g.positions[(← xs[1]?).val]?
  let c ← g.positions[(← xs[2]?).val]?
  let d ← g.positions[(← xs[3]?).val]?
  return CartesianPoint3.orientedVolume a b c d

private def Nonflat (k : Nat) (m : RawMolecule) (g : SpatialConfiguration) : Prop :=
  ∀ a : Fin k, (writtenNeighbors m a).length = 4 →
    ((writtenVolume g (writtenNeighbors m a)).any (· != 0)) = true

private theorem gate_of_written (i : Input) (ok : Nonflat i.molecule.atomCount i.molecule i.spatial) :
    LocalizedChemicalRing.coordinatesAdmitted i = true := by
  apply gate_of_rows
  simp only [adjacent,raw_adj,volume,CertifiedLocalizedCIPInput.spatialPointAt?,
    i.spatial_eq,Option.bind_some,pure,bind]
  change Nonflat i.certified.certified.input.molecule.atomCount i.molecule i.spatial
  rwa [i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]

private theorem gate (mirror : Bool) : LocalizedChemicalRing.coordinatesAdmitted (sample mirror) = true := by
  apply gate_of_written
  obtain ⟨graph,spatial⟩ := RingChemicalReport.admission_fields (Option.some_get (admitted mirror)).symm
  change (sample mirror).molecule = molecule at graph
  change (sample mirror).spatial = transGeometry mirror at spatial
  rw [graph,spatial]
  unfold Nonflat
  cases mirror <;> decide +kernel

/-- Both raw nitrogen assignments for every admitted realization of the closed scaffold. -/
theorem raw (g : SpatialConfiguration) {i : Input}
    (admission : LocalizedChemicalRing.admitRawSpatial? molecule g = some i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingHydrogenReport.fromRaw? molecule g [0,1] = some [(0,predicted g false),(1,predicted g true)] := by
  apply raw_of_recognized g admission valid
  intro b
  have hit : RingDialkyldiaziridine.constrainedRaw molecule (nitrogen b) = true := by
    letI : NeZero molecule.atomCount := ⟨by decide⟩
    cases b <;>
      simp only [RingDialkyldiaziridine.constrainedRaw,
        dif_pos (by decide : 0 < molecule.atomCount),dif_pos (by decide : 1 < molecule.atomCount),
        nitrogen,Bool.false_eq_true,if_false,if_true,RingDialkyldiaziridine.test,decide_eq_true_eq]
    · refine ⟨?_,1,?_,?_,?_,2,?_,?_,?_,?_,3,?_,?_,?_,?_,4,?_,?_,?_,?_,?_⟩ <;> first | decide +kernel | unfold RingDialkyldiaziridine.Alkyl; decide +kernel
    · refine ⟨?_,0,?_,?_,?_,2,?_,?_,?_,?_,4,?_,?_,?_,?_,3,?_,?_,?_,?_,?_⟩ <;> first | decide +kernel | unfold RingDialkyldiaziridine.Alkyl; decide +kernel
  simp [RingPyramidalNitrogen.constrainedRaw,hit]

/-- The public raw report assigns both nitrogens S for the written trans model
and both R after reflection. Structural and coordinate admission are proved. -/
theorem trans_and_mirror :
    RingHydrogenReport.fromRaw? molecule (geometry 1) [0,1] =
      some [(0,some (.chiral .S,.chiral .R)),(1,some (.chiral .S,.chiral .R))] ∧
    RingHydrogenReport.fromRaw? molecule (geometry (-1)) [0,1] =
      some [(0,some (.chiral .R,.chiral .S)),(1,some (.chiral .R,.chiral .S))] := by
  have both (b : Bool) := raw (transGeometry b) (Option.some_get (admitted b)).symm (gate b)
  exact ⟨by simpa only [transGeometry,Bool.false_eq_true,if_false,(trans_readings false).1,
      (trans_readings true).1] using both false,
    by simpa only [transGeometry,if_true,(trans_readings false).2,(trans_readings true).2] using both true⟩

end TetraStereo.Engine.Dimethyldiaziridine
assert_kernel_only TetraStereo.Engine.Dimethyldiaziridine.atomic_rows
assert_kernel_only TetraStereo.Engine.Dimethyldiaziridine.trans_readings
assert_kernel_only TetraStereo.Engine.Dimethyldiaziridine.raw
assert_kernel_only TetraStereo.Engine.Dimethyldiaziridine.trans_and_mirror
