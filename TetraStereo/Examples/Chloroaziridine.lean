import TetraStereo.Engine.RingPyramidalTwoShell
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Nitrogen stereochemistry of the experimentally resolved mono- and
gem-dimethyl N-chloroaziridines. The two-shell order follows from the physical
bonds. Only the four coordinates in that order enter the predicted descriptor. -/
set_option autoImplicit false
namespace TetraStereo.Engine.Chloroaziridine
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingAtomicNeighborOrder (neighbors)
open RingSecondShellDecision (signature)
open private row? from TetraStereo.Engine.RingChemicalReport
attribute [local instance] lexOrd
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- N0, the substituted ring carbon C1, ring CH₂ C2 and Cl3 are common to both
graphs. Slot 5 is hydrogen in the monomethyl compound and carbon in the dimethyl compound. -/
def molecule (dimethyl : Bool) : RawMolecule := {
  atoms := ([.N,.C,.C,.Cl,.C,if dimethyl then .C else .H] ++
    List.replicate (if dimethyl then 8 else 5) .H : List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(0,2),(0,3),(1,2),(1,4),(1,5),(2,6),(2,7),(4,8),(4,9),(4,10)] ++
    if dimethyl then [(5,11),(5,12),(5,13)] else []).map fun (a,b) => ⟨a,b,.single⟩ }

private def columns (d : Bool) (id : Nat) :=
  (RingSecondShellDecision.adjacent (molecule d) 0 id).map (RingAtomicNeighborOrder.atomicNumber (molecule d))

private theorem sorted {xs : List Nat} (h : xs.Pairwise (· ≥ ·)) : RingAtomicSecondShell.sorted xs = xs :=
  List.mergeSort_eq_self (r := (· ≥ ·)) h

/-- Independent atomic-number rows, excluding the bond back to N. -/
theorem atomic_rows (d : Bool) :
    [3,1,2].map (signature (molecule d) 0) =
      [[[17],[]],[[6],if d then [6,6,6] else [6,6,1]],[[6],[6,1,1]]] := by
  have cl : columns d 3 = [] := by cases d <;> decide +kernel
  have sub : columns d 1 = (if d then [6,6,6] else [6,6,1]) := by cases d <;> decide +kernel
  have ch : columns d 2 = [6,1,1] := by cases d <;> decide +kernel
  unfold columns at cl sub ch
  have orderSub : (if d then [6,6,6] else [6,6,1]).Pairwise (· ≥ ·) := by cases d <;> decide
  simp only [List.map_cons,List.map_nil,signature,RingSecondShellDecision.shell,cl,sub,ch,
    sorted orderSub,sorted (by decide : ([] : List Nat).Pairwise (· ≥ ·)),
    sorted (by decide : [6,1,1].Pairwise (· ≥ ·))]
  rfl

private theorem rank (d : Bool) :
    (neighbors (molecule d) 0).Perm [3,1,2] ∧
    ([3,1,2].map (signature (molecule d) 0)).Pairwise (· > ·) := by
  constructor
  · apply (RingStereoSiblingPass.legal_order _ _).perm.trans
    cases d <;> decide +kernel
  · rw [atomic_rows]
    cases d <;> decide +kernel

private theorem recognized (d : Bool) :
    RingChloroaziridineNitrogen.constrainedRaw (molecule d) 0 = true := by
  cases d <;> decide +kernel

private theorem selected {i : Input} (a : i.certified.Atom) (idx : a.val = 0)
    (d : Bool) (graph : i.molecule = molecule d) : RingPyramidalPublication.phosphorus i a = true := by
  have ng : RingPyramidalNitrogen.constrained i a = true := by
    simp [RingPyramidalNitrogen.constrained,RingPyramidalNitrogen.constrainedRaw,graph,idx,recognized]
  have card : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
    rw [RingAtomicNeighborOrder.degree_eq,graph,idx]
    exact (rank d).1.length_eq
  simp [RingPyramidalPublication.phosphorus,ng,card,graph,idx,molecule,AtomSpec.aliphatic]

def predicted (g : SpatialConfiguration) : Option RingNestedActivePair.Labels :=
  (readback? (RingWrittenPHReadings.geometry g) [3,1,2,0]).map fun h => (.chiral h,.chiral h.swap)

/-- Every admitted coordinate realization returns the signed Cl, substituted-C,
CH₂, phantom reading. The nitrogen outcome requires no auxiliary hypothesis. -/
theorem raw (d : Bool) (g : SpatialConfiguration) {i : Input}
    (admission : LocalizedChemicalRing.admitRawSpatial? (molecule d) g = some i)
    (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingHydrogenReport.fromRaw? (molecule d) g [0] = some [(0,predicted g)] := by
  obtain ⟨graph,spatial⟩ := RingChemicalReport.admission_fields admission
  have hb : 0 < i.certified.certified.input.molecule.atomCount := by
    rw [i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,graph]
    cases d <;> decide
  let n : i.certified.Atom := ⟨0,hb⟩
  have closed : RingHydrogenCompletion.plan i.molecule = [] := by
    rw [graph]
    cases d <;> decide +kernel
  obtain ⟨perm,strict⟩ := rank d
  have root := RingPyramidalTwoShell.root_of_graph_order valid n (selected n rfl d graph) [3,1,2]
    (by simpa only [graph,n] using perm) (by simpa only [graph,n] using strict)
  simp only [List.cons_append,List.nil_append,RingWrittenPHReadings.inputGeometry_eq,spatial] at root
  rw [← graph,← spatial,show [0] = [n].map Fin.val from rfl,
    RingWrittenPHReadings.fromRaw_closed_report i closed valid]
  unfold RingChemicalReport.report?
  simp only [List.mapM_cons,List.mapM_nil,row?,root,Option.map_some,bind,pure]
  rw [spatial]
  rfl

end TetraStereo.Engine.Chloroaziridine
assert_kernel_only TetraStereo.Engine.Chloroaziridine.atomic_rows
assert_kernel_only TetraStereo.Engine.Chloroaziridine.raw
