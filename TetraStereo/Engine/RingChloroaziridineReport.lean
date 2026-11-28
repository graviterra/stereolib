import TetraStereo.Engine.RingChloroaziridineOrder
import TetraStereo.Engine.RingChloroaziridineHydrogen
import TetraStereo.Engine.RingPyramidalTwoShell
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Read the N-chloroaziridine nitrogen on the physical heavy-atom frame.
The two-shell priorities can be checked on a hydrogen-completed graph, while
the physical hand is read on the four original heavy atoms. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingChloroaziridineReport
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingOxaziridineNitrogen (atomIs)
open RingAtomicNeighborOrder (neighbors)
open RingSecondShellDecision (signature)
open private row? from TetraStereo.Engine.RingChemicalReport
attribute [local instance] lexOrd

def Row (m : RawMolecule) (n cl c d : Nat) : Prop :=
  (neighbors m n).Perm [cl,c,d] ∧ ([cl,c,d].map (signature m n)).Pairwise (· > ·) ∧
    atomIs m cl .Cl = true ∧ atomIs m c .C = true ∧ atomIs m d .C = true

def reading (g : SpatialConfiguration) (n cl c d : Nat) : Option RingNestedActivePair.Labels :=
  (readback? (RingWrittenPHReadings.geometry g) [cl,c,d,n]).map fun h => (.chiral h,.chiral h.swap)

private theorem nitrogen {m : RawMolecule} {n : Nat} (hit : RingChloroaziridineNitrogen.constrainedRaw m n = true) :
    atomIs m n .N = true := by
  unfold RingChloroaziridineNitrogen.constrainedRaw at hit
  split at hit
  · exact (of_decide_eq_true hit).1
  · contradiction

private theorem closed_row {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (closed : RingHydrogenCompletion.plan i.molecule = []) (a : i.certified.Atom)
    (motif : RingChloroaziridineNitrogen.constrained i a = true)
    {cl c d : Nat} (r : Row i.molecule a.val cl c d) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial [a.val] = some [(a.val,reading i.spatial a.val cl c d)] := by
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
    rw [RingAtomicNeighborOrder.degree_eq]
    exact r.1.length_eq
  have record := nitrogen motif
  have selected : RingPyramidalPublication.phosphorus i a = true := by
    cases w : i.molecule.atoms[a.val]? with
    | none => simp [atomIs,w] at record
    | some atom =>
      have fields : (atom.element = .N ∧ atom.charge = 0) ∧ atom.aromatic = false := by
        simpa [atomIs,w] using record
      have raw : RingChloroaziridineNitrogen.constrainedRaw i.molecule a.val = true := motif
      simp [RingPyramidalPublication.phosphorus,w,fields.1.1,fields.1.2,fields.2,degree,
        RingPyramidalNitrogen.constrained,RingPyramidalNitrogen.constrainedRaw,raw]
  have h := RingPyramidalTwoShell.root_of_graph_order geom a selected [cl,c,d] r.1 r.2.1
  simp only [List.cons_append,List.nil_append,RingWrittenPHReadings.inputGeometry_eq] at h
  rw [show [a.val] = [a].map Fin.val from rfl,RingWrittenPHReadings.fromRaw_closed_report i closed geom]
  unfold RingChemicalReport.report?
  simp only [List.mapM_cons,List.mapM_nil,row?,h,Option.map_some,bind,pure]
  rfl

private theorem original {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : RingHydrogenCompletion.Certified m g out pos) {n : Nat} {z : Element}
    (heavy : z ≠ .H) (record : atomIs out n z = true) : n < m.atomCount := by
  by_contra! added
  by_cases valid : n < out.atoms.length
  · simp [atomIs,cert.fresh_atom added valid,AtomSpec.aliphatic,Ne.symm heavy] at record
  · simp [atomIs,List.getElem?_eq_none (Nat.le_of_not_lt valid)] at record

/-- Every placement considered by the public raw API gives the same nitrogen
answer even when hydrogens elsewhere have more than one placement. -/
theorem raw_of_row {m out : RawMolecule} {g pos : SpatialConfiguration} {src base : Input}
    (admit : LocalizedChemicalRing.admitRawSpatial? m g = some src)
    (sourceGeom : LocalizedChemicalRing.coordinatesAdmitted src = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (prepared : LocalizedChemicalRing.admitRawSpatial? out pos = some base)
    (baseGeom : LocalizedChemicalRing.coordinatesAdmitted base = true)
    {n cl c d : Nat} (motif : RingChloroaziridineNitrogen.constrainedRaw out n = true)
    (r : Row out n cl c d) :
    RingHydrogenReport.fromRaw? m g [n] = some [(n,reading g n cl c d)] := by
  have cert := RingHydrogenCompletion.prepare?_certified done
  have nlt := original cert (by decide : Element.N ≠ .H) (nitrogen motif)
  have clt := original cert (by decide : Element.Cl ≠ .H) r.2.2.1
  have ct := original cert (by decide : Element.C ≠ .H) r.2.2.2.1
  have dt := original cert (by decide : Element.C ≠ .H) r.2.2.2.2
  rw [RingSpatialTransport.public_search admit sourceGeom done [n] (by simpa using nlt)]
  apply (RingHydrogenReport.search?_iff ..).mpr
  intro points hp
  let x : SpatialConfiguration := ⟨points⟩
  have hx : x ∈ RingPyramidalChoices.variants m g out pos := List.mem_map.mpr ⟨points,hp,rfl⟩
  obtain ⟨j,aj,gj⟩ := RingSpatialTransport.variant_admission cert prepared hx
  obtain ⟨jm,jg⟩ := RingChemicalReport.admission_fields aj
  let a : j.certified.Atom := ⟨n,by
    rw [j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1,jm]
    exact Nat.lt_of_lt_of_le nlt cert.atomCount_le⟩
  have result := closed_row (gj.trans baseGeom) (jm ▸ RingHydrogenCompletion.prepare?_closed done) a
    (by simpa [RingChloroaziridineNitrogen.constrained,jm,a] using motif)
    (cl := cl) (c := c) (d := d) (by simpa only [jm,a] using r)
  simp only [jm,jg,a,RingHydrogenReport.fromRaw_closed_eq (RingHydrogenCompletion.prepare?_closed done)] at result
  have fixed (idx : Nat) (h : idx < m.atomCount) : x.positions[idx]? = g.positions[idx]? :=
    (RingPyramidalChoices.variants_original hx h).trans (cert.positions_getElem? h)
  have same : reading x n cl c d = reading g n cl c d := by
    simp only [reading,readback?,List.mapM_cons,List.mapM_nil,RingWrittenPHReadings.geometry,
      fixed cl clt,fixed c ct,fixed d dt,fixed n nlt]
  exact same ▸ result

/-- Starting from the original molecular graph, obtain the ranked heavy atoms
and the exact public answer. Neither a proposed priority nor a frozen store
is a hypothesis. The two coordinate-admission premises are the public gates. -/
theorem from_source {m out : RawMolecule} {g pos : SpatialConfiguration} {src base : Input}
    (admit : LocalizedChemicalRing.admitRawSpatial? m g = some src)
    (sourceGeom : LocalizedChemicalRing.coordinatesAdmitted src = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (prepared : LocalizedChemicalRing.admitRawSpatial? out pos = some base)
    (baseGeom : LocalizedChemicalRing.coordinatesAdmitted base = true)
    {n : Nat} (motif : RingChloroaziridineNitrogen.constrainedRaw m n = true)
    (valence : RingChloroaziridineHydrogen.NoExtraH m n) :
    ∃ cl c d, Row out n cl c d ∧ RingHydrogenReport.fromRaw? m g [n] = some [(n,reading g n cl c d)] := by
  have recognized := RingChloroaziridineHydrogen.recognized (RingHydrogenCompletion.prepare?_certified done)
    n valence motif
  obtain ⟨cl,c,d,row⟩ := RingChloroaziridineOrder.descending_row_with_roles_of_constrained out n recognized
  exact ⟨cl,c,d,row,raw_of_row admit sourceGeom done prepared baseGeom recognized row⟩

end TetraStereo.Engine.RingChloroaziridineReport
assert_kernel_only TetraStereo.Engine.RingChloroaziridineReport.raw_of_row
assert_kernel_only TetraStereo.Engine.RingChloroaziridineReport.from_source
