import TetraStereo.Engine.RingChloroaziridineOrder
import TetraStereo.Engine.RingDiaziridineSelection
import TetraStereo.Engine.RingPyramidalTwoShell
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Rule 1a orders the three ligands at an N-alkoxy-2,2,3-trimethylaziridine
nitrogen. The two competing ring carbons expose three versus two outward
carbons; their written hydrogen counts do not enter the comparison. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAlkoxyaziridineOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingOxaziridineNitrogen (atomIs)
open RingAtomicNeighborOrder (atomicNumber neighbors)
open RingSecondShellDecision (adjacent shell signature)
open private atomic_of_good sorted_desc shell_mem from TetraStereo.Engine.RingOxaziridineRootOrder
open private carbon_compare mem_adj from TetraStereo.Engine.RingChloroaziridineOrder

/-- Exact outward carbon identities; all other outward neighbors are hydrogen.
The list does not include the incoming nitrogen. -/
structure CarbonShell (m : RawMolecule) (n a : Nat) (carbons : List Nat) : Prop where
  distinct : carbons.Nodup
  present : ∀ c ∈ carbons, c ∈ adjacent m n a ∧ atomicNumber m c = 6
  others : ∀ c ∈ adjacent m n a, c ∉ carbons → atomicNumber m c = 1

private theorem counted {m : RawMolecule} {n a : Nat} {cs : List Nat} (data : CarbonShell m n a cs) :
    (shell m n a).count 6 = cs.length := by
  let atoms := adjacent m n a
  have nd : atoms.Nodup := List.nodup_range.filter _
  have perm : (atoms.filter fun c => atomicNumber m c == 6).Perm cs := by
    apply (List.perm_ext_iff_of_nodup (nd.filter _) data.distinct).mpr
    intro c
    simp only [List.mem_filter,beq_iff_eq]
    constructor
    · rintro ⟨h,z⟩
      by_contra miss
      have := data.others c h miss
      omega
    · exact data.present c
  unfold shell RingAtomicSecondShell.sorted
  rw [(List.mergeSort_perm _ _).count_eq]
  change (atoms.map (atomicNumber m)).count 6 = _
  rw [List.count_eq_countP,List.countP_map,List.countP_eq_length_filter]
  exact perm.length_eq

private theorem capped {m : RawMolecule} {n a : Nat} {cs : List Nat} (data : CarbonShell m n a cs) :
    ∀ z ∈ shell m n a, z ≤ 6 := by
  intro z h
  obtain ⟨v,hv,rfl⟩ := (shell_mem ..).mp h
  by_cases inc : v ∈ cs
  · exact (data.present v inc).2.le
  · rw [data.others v hv inc]; decide

structure SiteRoles (m : RawMolecule) (n o gem mono : Nat) : Prop where
  row : (neighbors m n).Perm [o,gem,mono]
  oxygen : atomIs m o .O = true
  gemCarbon : atomIs m gem .C = true
  monoCarbon : atomIs m mono .C = true
  gemShell : ∃ x y, CarbonShell m n gem [mono,x,y]
  monoShell : ∃ z, CarbonShell m n mono [gem,z]

theorem descending {m : RawMolecule} {n o gem mono : Nat} (roles : SiteRoles m n o gem mono) :
    ([o,gem,mono].map (signature m n)).Pairwise (· > ·) := by
  obtain ⟨x,y,gs⟩ := roles.gemShell
  obtain ⟨z,ms⟩ := roles.monoShell
  have go : atomicNumber m o = 8 := atomic_of_good m _ _ roles.oxygen
  have gg : atomicNumber m gem = 6 := atomic_of_good m _ _ roles.gemCarbon
  have gm : atomicNumber m mono = 6 := atomic_of_good m _ _ roles.monoCarbon
  have shellLt : shell m n mono < shell m n gem :=
    carbon_compare _ _ (sorted_desc _) (capped ms) (by rw [counted gs,counted ms]; exact Nat.lt_succ_self 2)
  have mg : signature m n mono < signature m n gem := by
    simp only [signature,gm,gg]
    exact List.Lex.cons (List.Lex.rel shellLt)
  have og : signature m n gem < signature m n o := by
    simp only [signature,gg,go]
    exact List.Lex.rel (List.Lex.rel (by decide : (6 : Nat) < 8))
  simpa [List.pairwise_cons] using And.intro (And.intro og (lt_trans mg og)) mg


private theorem atom_of_recognized {m : RawMolecule} {n : Nat}
    (motif : RingAlkoxyaziridineNitrogen.constrainedRaw m n = true) : atomIs m n .N = true := by
  unfold RingAlkoxyaziridineNitrogen.constrainedRaw at motif
  split at motif
  · exact (of_decide_eq_true motif).1
  · contradiction

theorem roles_of_recognized {m : RawMolecule} {n : Nat}
    (motif : RingAlkoxyaziridineNitrogen.constrainedRaw m n = true) :
    ∃ o gem mono, SiteRoles m n o gem mono := by
  unfold RingAlkoxyaziridineNitrogen.constrainedRaw at motif
  split at motif
  next bound =>
    obtain ⟨gn,o,go,no,c,gc,nc,d,gd,cd,nd,edge,ns,x,y,xy,xd,yd,mx,my,cs,z,zc,mz,ds,_⟩ :=
      of_decide_eq_true motif
    dsimp only at no nc nd edge ns cs ds
    have zn : atomicNumber m n = 7 := atomic_of_good m _ _ gn
    have unequal {u v : Fin m.atomCount} (ne : u ≠ v) : u.val ≠ v.val := fun eq => ne (Fin.ext eq)
    have oc {v : Fin m.atomCount} (gv : atomIs m v.val .C = true) : o.val ≠ v.val := by
      intro eq
      have eqn := congrArg (atomicNumber m) eq
      rw [atomic_of_good m _ _ go,atomic_of_good m _ _ gv] at eqn
      contradiction
    have carbon {a v : Fin m.atomCount} (gv : atomIs m v.val .C = true) (ed : m.bondOrder a.val v.val = 1) :
        v.val ∈ adjacent m n a.val ∧ atomicNumber m v.val = 6 := by
      have six : atomicNumber m v.val = 6 := atomic_of_good m _ _ gv
      refine ⟨mem_adj.mpr ⟨v.isLt,?_,by rw [ed]; decide⟩,six⟩
      intro eq
      rw [eq,zn] at six
      contradiction
    refine ⟨o.val,c.val,d.val,RingDiaziridineSelection.neighbors_perm (oc gc) (oc gd) (unequal cd) no nc nd ns,
      go,gc,gd,⟨x.val,y.val,?_,?_,?_⟩,⟨z.val,?_,?_,?_⟩⟩
    · simp [unequal xd.symm,unequal yd.symm,unequal xy]
    · intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl|rfl
      · exact carbon gd edge
      · exact carbon mx.1 mx.2.1
      · exact carbon my.1 my.2.1
    · intro v adj missed
      obtain ⟨hv,notN,bond⟩ := mem_adj.mp adj
      rcases cs ⟨v,hv⟩ bond with eq|eq|eq|eq
      · exact (notN (congrArg Fin.val eq)).elim
      all_goals
        have h := congrArg Fin.val eq
        dsimp only at h
        exact (missed (by simp [h])).elim
    · simp [unequal zc.symm]
    · intro v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl|rfl
      · exact carbon gc ((m.bondOrder_symm _ _).trans edge)
      · exact carbon mz.1 mz.2.1
    · intro v adj missed
      obtain ⟨hv,notN,bond⟩ := mem_adj.mp adj
      rcases ds ⟨v,hv⟩ bond with eq|eq|eq|hg
      · exact (notN (congrArg Fin.val eq)).elim
      · have h := congrArg Fin.val eq
        dsimp only at h
        exact (missed (by simp [h])).elim
      · have h := congrArg Fin.val eq
        dsimp only at h
        exact (missed (by simp [h])).elim
      · exact atomic_of_good m _ _ hg
  next => contradiction

theorem selected {i : Input} (n : i.certified.Atom)
    (motif : RingAlkoxyaziridineNitrogen.constrainedRaw i.molecule n.val = true) :
    RingPyramidalPublication.phosphorus i n = true := by
  obtain ⟨o,c,d,roles⟩ := roles_of_recognized motif
  have degree : Fintype.card (i.certified.moleculeGraph.Neighbor n) = 3 :=
    (RingAtomicNeighborOrder.degree_eq i n).trans roles.row.length_eq
  have record := atom_of_recognized motif
  cases w : i.molecule.atoms[n.val]? with
  | none => simp [atomIs,w] at record
  | some atom =>
    have fields : (atom.element = .N ∧ atom.charge = 0) ∧ atom.aromatic = false := by
      simpa [atomIs,w] using record
    simp [RingPyramidalPublication.phosphorus,w,fields.1.1,fields.1.2,fields.2,degree,
      RingPyramidalNitrogen.constrained,RingPyramidalNitrogen.constrainedRaw,motif]

open LocalizedGenericMarkedRecalculation (readback?)

theorem root_of_recognized {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (n : i.certified.Atom) (motif : RingAlkoxyaziridineNitrogen.constrainedRaw i.molecule n.val = true)
    {o gem mono : Nat} (roles : SiteRoles i.molecule n.val o gem mono) :
    RingChemicalGraphProof.root i n = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        [o,gem,mono,n.val]).map fun h => (.chiral h,.chiral h.swap)) :=
  RingPyramidalTwoShell.root_of_graph_order geom n (selected n motif) _ roles.row (descending roles)

/-- The hand is read using only the four original heavy-atom coordinates. -/
def labels (g : SpatialConfiguration) (n o gem mono : Nat) : Option RingNestedActivePair.Labels :=
  (readback? (RingWrittenPHReadings.geometry g) [o,gem,mono,n]).map fun h => (.chiral h,.chiral h.swap)

open private row? from TetraStereo.Engine.RingChemicalReport

theorem closed_row {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (closed : RingHydrogenCompletion.plan i.molecule = []) (n : i.certified.Atom)
    (motif : RingAlkoxyaziridineNitrogen.constrainedRaw i.molecule n.val = true)
    {o c k : Nat} (r : SiteRoles i.molecule n.val o c k) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial [n.val] = some [(n.val,labels i.spatial n.val o c k)] := by
  have h := root_of_recognized geom n motif r
  rw [RingWrittenPHReadings.inputGeometry_eq] at h
  rw [show [n.val] = [n].map Fin.val from rfl,RingWrittenPHReadings.fromRaw_closed_report i closed geom]
  unfold RingChemicalReport.report?
  simp only [List.mapM_cons,List.mapM_nil,row?,h,Option.map_some,bind,pure]
  rfl

private theorem original {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : RingHydrogenCompletion.Certified m g out pos) {n : Nat} {z : Element}
    (heavy : z ≠ .H) (h : atomIs out n z = true) : n < m.atomCount := by
  by_contra! fresh
  have lt : n < out.atomCount := by
    by_contra! absent
    simp [atomIs,List.getElem?_eq_none (by exact absent : out.atoms.length ≤ n)] at h
  have newAtom := cert.fresh_atom fresh lt
  simp [atomIs,newAtom,AtomSpec.aliphatic,Ne.symm heavy] at h

/-- Read the fully public raw nitrogen row from its constitutional roles, for
any admitted hydrogen preparation and all generated placements. -/
theorem raw {m out : RawMolecule} {g pos : SpatialConfiguration} {src base : Input}
    (admit : LocalizedChemicalRing.admitRawSpatial? m g = some src)
    (sourceGeom : LocalizedChemicalRing.coordinatesAdmitted src = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (prepared : LocalizedChemicalRing.admitRawSpatial? out pos = some base)
    (baseGeom : LocalizedChemicalRing.coordinatesAdmitted base = true) {n : Nat}
    (motif : RingAlkoxyaziridineNitrogen.constrainedRaw out n = true) :
    ∃ o c k, SiteRoles out n o c k ∧ RingHydrogenReport.fromRaw? m g [n] = some [(n,labels g n o c k)] := by
  obtain ⟨o,c,k,r⟩ := roles_of_recognized motif
  refine ⟨o,c,k,r,?_⟩
  have cert := RingHydrogenCompletion.prepare?_certified done
  have nlt := original cert (by decide : Element.N ≠ .H) (atom_of_recognized motif)
  have olt := original cert (by decide : Element.O ≠ .H) r.oxygen
  have clt := original cert (by decide : Element.C ≠ .H) r.gemCarbon
  have klt := original cert (by decide : Element.C ≠ .H) r.monoCarbon
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
    (by simpa [jm,a] using motif) (o := o) (c := c) (k := k) (by simpa only [jm,a] using r)
  simp only [jm,jg,a,RingHydrogenReport.fromRaw_closed_eq (RingHydrogenCompletion.prepare?_closed done)] at result
  have fixed (idx : Nat) (old : idx < m.atomCount) : x.positions[idx]? = g.positions[idx]? :=
    (RingPyramidalChoices.variants_original hx old).trans (cert.positions_getElem? old)
  have same : labels x n o c k = labels g n o c k := by
    simp only [labels,readback?,List.mapM_cons,List.mapM_nil,RingWrittenPHReadings.geometry,
      fixed n nlt,fixed o olt,fixed c clt,fixed k klt]
  exact same ▸ result


end TetraStereo.Engine.RingAlkoxyaziridineOrder
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineOrder.descending
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineOrder.roles_of_recognized
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineOrder.selected
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineOrder.root_of_recognized
assert_kernel_only TetraStereo.Engine.RingAlkoxyaziridineOrder.raw
