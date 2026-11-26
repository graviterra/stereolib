import TetraStereo.Engine.RingSpatialTransport
import TetraStereo.Engine.RingHydrogenNeighbors

set_option autoImplicit false
namespace TetraStereo.Engine.RingSpatialTransport
open OneCenter RingPyramidalChoices
open RingGroupedReport (Report)
open LocalizedChemicalRing (Input)
open LocalizedActualPhysicalBranchDecision (actualCanonicalMolecule)

theorem centers_unmoved {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : RingHydrogenCompletion.Certified m g out pos) (i : Input) (hm : i.molecule = out)
    (c : (actualCanonicalMolecule i.certified).Center) (k : Fin 4) :
    ∀ s ∈ sites m g out pos, s.hydrogen ≠ centerIds i c k := by
  intro s hs
  let lig := (actualCanonicalMolecule i.certified).ligandAtomAt c k
  exact Ne.symm (selected_hydrogen_ne_tetra_ligand cert hs i hm c
    ⟨lig,(actualCanonicalMolecule i.certified).ligandAtomAt_adj c k⟩)

/-- All P–H variants have exactly the base geometry’s tetrahedral coordinate
admission status. No per-placement structural or physical witness is required. -/
theorem variant_admission {m out : RawMolecule} {g pos x : SpatialConfiguration}
    (cert : RingHydrogenCompletion.Certified m g out pos)
    {i : Input} (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (hx : x ∈ variants m g out pos) :
    ∃ j, LocalizedChemicalRing.admitRawSpatial? out x = some j ∧
      LocalizedChemicalRing.coordinatesAdmitted j = LocalizedChemicalRing.coordinatesAdmitted i := by
  obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields base
  have full : x.positions.length = size i := (variants_positions_length hx).trans (hg ▸ full_original i)
  refine ⟨atGeometry i x full,hm ▸ admit_atGeometry i x full,coordinates_of_same_ligands full ?_⟩
  intro c k
  rw [hg]
  exact variants_getElem?_of_not_site hx (centers_unmoved cert i hm c k)

/-- Once the ordinary completion is admitted, *every* combination of missing
phosphorus hands produces a unique raw report on the original IDs. -/
theorem variants_total {m out : RawMolecule} {g pos : SpatialConfiguration}
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    {i : Input} (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (bounds : ∀ k ∈ ids, k < m.atomCount) :
    ∀ x ∈ variants m g out pos, ∃! rows, RingChemicalReport.fromRaw? out x ids = some rows := by
  have cert := RingHydrogenCompletion.prepare?_certified done
  intro x hx
  obtain ⟨j,admit,same⟩ := variant_admission cert base hx
  exact RingChemicalReport.fromRaw_closed_total admit (same.trans geom)
    ((variants_positions_length hx).trans cert.positions_length)
    (RingHydrogenCompletion.prepare?_closed done) ids (fun k hk => (bounds k hk).trans_le cert.atomCount_le)

/-- No possible placement failed: an outer refusal is equivalent to two fully
computed row lists disagreeing. The competing geometries and both row lists are witnesses. -/
theorem search_none_iff_disagree {m out : RawMolecule} {g pos : SpatialConfiguration}
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    {i : Input} (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (bounds : ∀ k ∈ ids, k < m.atomCount) :
    RingHydrogenReport.search? (fun ps => RingChemicalReport.fromRaw? out ⟨ps⟩ ids)
        (sites m g out pos) pos.positions = none ↔
      ∃ x ∈ variants m g out pos, ∃ y ∈ variants m g out pos, ∃ r s : Report,
        RingChemicalReport.fromRaw? out x ids = some r ∧
        RingChemicalReport.fromRaw? out y ids = some s ∧ r ≠ s := by
  have member (ps) (hp : ps ∈ choices (sites m g out pos) pos.positions) :
      (⟨ps⟩ : SpatialConfiguration) ∈ variants m g out pos := List.mem_map.mpr ⟨ps,hp,rfl⟩
  constructor
  · intro absent
    obtain ⟨ps,hps⟩ := choices_exists (sites m g out pos) pos.positions
    have hx := member _ hps
    obtain ⟨r,hr,_⟩ := variants_total done base geom ids bounds _ hx
    by_contra no
    have uniform (qs) (hq : qs ∈ choices (sites m g out pos) pos.positions) :
        RingChemicalReport.fromRaw? out ⟨qs⟩ ids = some r := by
      have hy := member _ hq
      obtain ⟨s,hs,_⟩ := variants_total done base geom ids bounds _ hy
      by_cases e : r = s
      · simpa only [e] using hs
      · exact (no ⟨_,hx,_,hy,r,s,hr,hs,e⟩).elim
    have someRows := (RingHydrogenReport.search?_iff _ _ _ r).mpr uniform
    rw [absent] at someRows
    contradiction
  · rintro ⟨x,hx,y,hy,r,s,hr,hs,ne⟩
    obtain ⟨ps,hp,rfl⟩ := List.mem_map.mp hx
    obtain ⟨qs,hq,rfl⟩ := List.mem_map.mp hy
    cases got : RingHydrogenReport.search? _ (sites m g out pos) pos.positions with
    | none => rfl
    | some rows =>
      have all := (RingHydrogenReport.search?_iff _ _ _ _).mp got
      exact (ne ((Option.some.inj (hr.symm.trans (all _ hp))).trans
        (Option.some.inj ((all _ hq).symm.trans hs)))).elim

private theorem sites_of_closed {m out : RawMolecule} {g pos : SpatialConfiguration}
    (closed : RingHydrogenCompletion.plan m = []) : sites m g out pos = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro s hs
  obtain ⟨p,_,h⟩ := sites_valid hs
  have parent := h.hydrogen_parent
  simp [RingHydrogenCompletion.addedParents,closed] at parent

theorem public_search {m out : RawMolecule} {g pos : SpatialConfiguration} {source : Input}
    (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (geom : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (ids : List Nat) (bounds : ∀ n ∈ ids, n < m.atomCount) :
    RingHydrogenReport.fromRaw? m g ids =
      RingHydrogenReport.search? (fun ps => RingChemicalReport.fromRaw? out ⟨ps⟩ ids)
        (sites m g out pos) pos.positions := by
  obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields hs
  by_cases closed : RingHydrogenCompletion.plan m = []
  · have cert := RingHydrogenCompletion.prepare?_certified done
    have head := RingHydrogenCompletion.prepare?_of_complete m g closed
      (RingChemicalReport.closed_certificate m g cert.input_admissible cert.input_positions closed)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (done.symm.trans head))
    rw [RingHydrogenReport.fromRaw_closed_eq closed,sites_of_closed closed]
    rfl
  · simp [RingHydrogenReport.fromRaw?,RingHydrogenReport.preparedGeometry?,
      RingHydrogenReport.preparedSource?,closed,hs,hm,hg,geom,guard,done]
    rw [if_pos bounds]
    rfl

/-- With the source and its standard completion admitted, outer none has an
exact molecular explanation: two possible P–H hand assignments give different
complete reports on the requested original atoms. -/
theorem fromRaw_none_iff_disagree {m out : RawMolecule} {g pos : SpatialConfiguration}
    {source i : Input} (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (hsGeom : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (bounds : ∀ k ∈ ids, k < m.atomCount) :
    RingHydrogenReport.fromRaw? m g ids = none ↔
      ∃ x ∈ variants m g out pos, ∃ y ∈ variants m g out pos, ∃ r s : Report,
        RingHydrogenReport.Graph RingPopulationReport.Correct (out,x) ids r ∧
        RingHydrogenReport.Graph RingPopulationReport.Correct (out,y) ids s ∧ r ≠ s := by
  rw [public_search hs hsGeom done ids bounds,search_none_iff_disagree done base geom ids bounds]
  simp only [RingHydrogenReport.Graph,RingPopulationReport.fromRaw_iff]

end TetraStereo.Engine.RingSpatialTransport

assert_kernel_only TetraStereo.Engine.RingSpatialTransport.fromRaw_none_iff_disagree
