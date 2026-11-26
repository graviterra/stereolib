import TetraStereo.Engine.RingOxaziridineHydrogen
import TetraStereo.Engine.RingOxaziridinePublication
import TetraStereo.Engine.RingOxaziridineRootOrder
import TetraStereo.Engine.RingPyramidalTwoShell
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Molecular nitrogen assignments from graph recognition through public readback. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridineReport
open OneCenter LocalizedGenericMarkedRecalculation
open private row? from TetraStereo.Engine.RingChemicalReport
open LocalizedChemicalRing (Input)
open RingOxaziridineNitrogen (atomIs)
open RingAtomicNeighborOrder (neighbors)
open RingSecondShellDecision (signature)
attribute [local instance] lexOrd

/-- The three physical IDs are in priority order and name the ring oxygen,
its bonded ring carbon and the external N-alkyl carbon. -/
def Roles (m : RawMolecule) (n o c k : Nat) : Prop :=
  (neighbors m n).Perm [o,c,k] ∧ ([o,c,k].map (signature m n)).Pairwise (· > ·) ∧
    atomIs m o .O = true ∧ atomIs m c .C = true ∧ atomIs m k .C = true ∧ m.bondOrder o c = 1

def reading (g : SpatialConfiguration) (n o c k : Nat) : Option RingNestedActivePair.Labels :=
  (readback? (RingWrittenPHReadings.geometry g) [o,c,k,n]).map fun h => (.chiral h,.chiral h.swap)

/-- Graph recognition supplies its own priority order on *every* admitted geometry.
A flat N is a completed refusal. No local priorities, stores or hands are inputs. -/
theorem root {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (motif : RingOxaziridineNitrogen.constrained i a = true) :
    ∃ o c k, Roles i.molecule a.val o c k ∧
      RingChemicalGraphProof.root i a = some (reading i.spatial a.val o c k) := by
  obtain ⟨o,c,k,p,s,roles⟩ := RingOxaziridineRootOrder.descending_row_with_roles_of_constrained
    i.molecule a.val motif
  refine ⟨o,c,k,⟨p,s,roles⟩,?_⟩
  simpa only [List.cons_append,List.nil_append,RingWrittenPHReadings.inputGeometry_eq,reading] using
    RingPyramidalTwoShell.root_of_graph_order geom a
      (RingOxaziridinePublication.motif_selected a motif) [o,c,k] p s

private theorem raw_of_roles {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (closed : RingHydrogenCompletion.plan i.molecule = []) (a : i.certified.Atom)
    (motif : RingOxaziridineNitrogen.constrained i a = true) {o c k : Nat}
    (h : Roles i.molecule a.val o c k) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial [a.val] =
        some [(a.val,reading i.spatial a.val o c k)] := by
  have hit := RingPyramidalTwoShell.root_of_graph_order geom a
    (RingOxaziridinePublication.motif_selected a motif) [o,c,k] h.1 h.2.1
  simp only [List.cons_append,List.nil_append,RingWrittenPHReadings.inputGeometry_eq] at hit
  rw [show [a.val] = [a].map Fin.val from rfl,RingWrittenPHReadings.fromRaw_closed_report i closed geom]
  unfold RingChemicalReport.report?
  simp only [List.mapM_cons,List.mapM_nil]
  simp only [row?,hit,Option.map_some,bind,pure]
  rfl

/-- On a fully written molecule the raw API returns the actual physical row. -/
theorem raw {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (closed : RingHydrogenCompletion.plan i.molecule = []) (a : i.certified.Atom)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    ∃ o c k, Roles i.molecule a.val o c k ∧
      RingHydrogenReport.fromRaw? i.molecule i.spatial [a.val] =
        some [(a.val,reading i.spatial a.val o c k)] := by
  obtain ⟨o,c,k,roles,_⟩ := root geom a motif
  exact ⟨o,c,k,roles,raw_of_roles geom closed a motif roles⟩

private theorem original {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : RingHydrogenCompletion.Certified m g out pos) {n : Nat} {z : Element}
    (heavy : z ≠ .H) (record : atomIs out n z = true) : n < m.atomCount := by
  by_contra! added
  by_cases valid : n < out.atoms.length
  · have fresh := cert.fresh_atom added valid
    simp [RingOxaziridineNitrogen.atomIs,fresh,AtomSpec.aliphatic,Ne.symm heavy] at record
  · simp [RingOxaziridineNitrogen.atomIs,List.getElem?_eq_none (Nat.le_of_not_lt valid)] at record

/-- Ordinary-H completion can introduce ambiguous pyramidal placements elsewhere.
Every generated placement still gives the same nitrogen descriptor because its
four physical points are original heavy atoms. -/
theorem raw_implicit {m out : RawMolecule} {g pos : SpatialConfiguration} {src base : Input}
    (admit : LocalizedChemicalRing.admitRawSpatial? m g = some src)
    (sourceGeom : LocalizedChemicalRing.coordinatesAdmitted src = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (prepared : LocalizedChemicalRing.admitRawSpatial? out pos = some base)
    (baseGeom : LocalizedChemicalRing.coordinatesAdmitted base = true)
    (n : Nat) (motif : RingOxaziridineNitrogen.constrainedRaw out n = true) :
    ∃ o c k, Roles out n o c k ∧ RingHydrogenReport.fromRaw? m g [n] = some [(n,reading g n o c k)] := by
  obtain ⟨o,c,k,p,s,roles⟩ := RingOxaziridineRootOrder.descending_row_with_roles_of_constrained out n motif
  have certified := RingHydrogenCompletion.prepare?_certified done
  have bounded : n < out.atomCount := by
    by_contra! h
    simp [RingOxaziridineNitrogen.constrainedRaw,Nat.not_lt.mpr h] at motif
  obtain ⟨bm,_⟩ := RingChemicalReport.admission_fields prepared
  let nb : base.certified.Atom := ⟨n,by
    rw [base.molecule.toSemanticMolecule?_atomCount _ base.agreement.1,bm]; exact bounded⟩
  have hn : atomIs out n .N = true := by
    have mb : RingOxaziridineNitrogen.constrained base nb = true := by
      simpa [RingOxaziridineNitrogen.constrained,bm,nb] using motif
    simpa only [bm,nb] using (RingOxaziridinePublication.motif_gates nb mb).1
  have nlt := original certified (by decide : Element.N ≠ .H) hn
  have olt := original certified (by decide : Element.O ≠ .H) roles.1
  have clt := original certified (by decide : Element.C ≠ .H) roles.2.1
  have klt := original certified (by decide : Element.C ≠ .H) roles.2.2.1
  refine ⟨o,c,k,⟨p,s,roles⟩,?_⟩
  rw [RingSpatialTransport.public_search admit sourceGeom done [n] (by simpa using nlt)]
  apply (RingHydrogenReport.search?_iff ..).mpr
  intro points hp
  let x : SpatialConfiguration := ⟨points⟩
  have hx : x ∈ RingPyramidalChoices.variants m g out pos := List.mem_map.mpr ⟨points,hp,rfl⟩
  obtain ⟨j,aj,gj⟩ := RingSpatialTransport.variant_admission certified prepared hx
  obtain ⟨jm,jg⟩ := RingChemicalReport.admission_fields aj
  let atom : j.certified.Atom := ⟨n,by
    rw [j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1,jm]; exact bounded⟩
  have result := raw_of_roles (gj.trans baseGeom) (jm ▸ RingHydrogenCompletion.prepare?_closed done)
    atom (by simpa [RingOxaziridineNitrogen.constrained,jm,atom] using motif)
    (o := o) (c := c) (k := k) (by simpa [jm,atom,Roles] using And.intro p (And.intro s roles))
  simp only [jm,jg,atom,RingHydrogenReport.fromRaw_closed_eq (RingHydrogenCompletion.prepare?_closed done)] at result
  have fixed (idx : Nat) (h : idx < m.atomCount) : x.positions[idx]? = g.positions[idx]? :=
    (RingPyramidalChoices.variants_original hx h).trans (certified.positions_getElem? h)
  have eqRead : reading x n o c k = reading g n o c k := by
    simp only [reading,readback?,List.mapM_cons,List.mapM_nil,RingWrittenPHReadings.geometry,
      fixed o olt,fixed c clt,fixed k klt,fixed n nlt]
  exact eqRead ▸ result

/-- A source motif persists through completion when neither ring heteroatom
receives an added hydrogen. All other hydrogen placements are unrestricted. -/
theorem from_source {m out : RawMolecule} {g pos : SpatialConfiguration} {src base : Input}
    (admit : LocalizedChemicalRing.admitRawSpatial? m g = some src)
    (sourceGeom : LocalizedChemicalRing.coordinatesAdmitted src = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (prepared : LocalizedChemicalRing.admitRawSpatial? out pos = some base)
    (baseGeom : LocalizedChemicalRing.coordinatesAdmitted base = true)
    (n : Nat) (motif : RingOxaziridineNitrogen.constrainedRaw m n = true)
    (valence : RingOxaziridineHydrogen.NoRingHydrogens m n) :
    ∃ o c k, Roles out n o c k ∧ RingHydrogenReport.fromRaw? m g [n] = some [(n,reading g n o c k)] :=
  raw_implicit admit sourceGeom done prepared baseGeom n
    (RingOxaziridineHydrogen.constrainedRaw_preserved (RingHydrogenCompletion.prepare?_certified done) n valence motif)

end TetraStereo.Engine.RingOxaziridineReport
assert_kernel_only TetraStereo.Engine.RingOxaziridineReport.root
assert_kernel_only TetraStereo.Engine.RingOxaziridineReport.raw
assert_kernel_only TetraStereo.Engine.RingOxaziridineReport.raw_implicit
assert_kernel_only TetraStereo.Engine.RingOxaziridineReport.from_source
