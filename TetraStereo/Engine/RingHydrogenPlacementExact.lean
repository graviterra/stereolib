import TetraStereo.Engine.RingCoordinateReportTransport
import TetraStereo.Engine.RingHydrogenReportDomain
import TetraStereo.Engine.RingPhysicalFrameBridge

set_option autoImplicit false
namespace TetraStereo.Engine.RingWrittenPHReadings
open OneCenter RingHydrogenCompletion RingPyramidalChoices RingSpatialTransport
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)

theorem variant_placement {m out : RawMolecule} {g pos x : SpatialConfiguration}
    (cert : Certified m g out pos) (hx : x ∈ variants m g out pos) : Placement m g out pos x := by
  refine ⟨variants_positions_length hx,fun _ hk => variants_getElem?_of_not_site hx hk,?_⟩
  intro s hs
  rcases (variants_site_frame cert hx hs).2.2.2 with ⟨h,vol⟩ | ⟨h,vol⟩
  · exact ⟨_,h,ne_of_gt vol⟩
  · exact ⟨_,h,ne_of_lt vol⟩

/-- Every admitted completed base graph accepts every nondegenerate written placement
of the selected terminal P hydrogens, with exactly the same coordinate-admission verdict. -/
theorem placement_admission {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (p : Placement m g out pos w) (cert : Certified m g out pos)
    {i : Input} (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i) :
    ∃ j, LocalizedChemicalRing.admitRawSpatial? out w = some j ∧
      LocalizedChemicalRing.coordinatesAdmitted j = LocalizedChemicalRing.coordinatesAdmitted i := by
  obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields base
  have full : w.positions.length = size i := p.full.trans (hg ▸ full_original i)
  refine ⟨atGeometry i w full,hm ▸ admit_atGeometry i w full,coordinates_of_same_ligands full ?_⟩
  intro c k
  rw [hg]
  exact p.fixed _ (centers_unmoved cert i hm c k)

/-- Explicit and generated placements share the same domain for the full native raw query. -/
theorem placement_total {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (p : Placement m g out pos w) (done : prepare? m g = some (out,pos))
    {i : Input} (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (bounds : ∀ k ∈ ids, k < out.atomCount) :
    ∃! rows, RingHydrogenReport.fromRaw? out w ids = some rows := by
  have cert := prepare?_certified done
  obtain ⟨j,admit,ok⟩ := placement_admission p cert base
  rw [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)]
  exact RingChemicalReport.fromRaw_closed_total admit (ok.trans geom)
    (p.full.trans cert.positions_length) (prepare?_closed done) ids bounds

/-- Agreement of all independently evaluated explicit placements forces the omitted-input
API to return that very report. This direction requires no invariance hypothesis. -/
theorem fromRaw_of_all_written {m out : RawMolecule} {g pos : SpatialConfiguration} {source : Input}
    (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (hsGeom : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (done : prepare? m g = some (out,pos)) (ids : List Nat) (bounds : ∀ k ∈ ids, k < m.atomCount)
    (rows : Report) (all : ∀ w, Placement m g out pos w → RingHydrogenReport.fromRaw? out w ids = some rows) :
    RingHydrogenReport.fromRaw? m g ids = some rows := by
  rw [public_search hs hsGeom done ids bounds, RingHydrogenReport.search?_iff]
  intro ps mem
  have actual := all ⟨ps⟩ (variant_placement (prepare?_certified done) (List.mem_map.mpr ⟨ps,mem,rfl⟩))
  simpa only [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)] using actual

/-- A raw ambiguity has two fully written, nondegenerate witnesses on the identical completed
molecule. Both conflicting reports are returned by the public raw API itself. -/
theorem ambiguity_has_written_witnesses {m out : RawMolecule} {g pos : SpatialConfiguration}
    {source i : Input} (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (hsGeom : LocalizedChemicalRing.coordinatesAdmitted source = true)
    (done : prepare? m g = some (out,pos)) (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (bounds : ∀ k ∈ ids, k < m.atomCount)
    (ambiguous : RingHydrogenReport.fromRaw? m g ids = none) :
    ∃ x y, Placement m g out pos x ∧ Placement m g out pos y ∧ ∃ r s : Report,
      RingHydrogenReport.fromRaw? out x ids = some r ∧ RingHydrogenReport.fromRaw? out y ids = some s ∧ r ≠ s := by
  rw [public_search hs hsGeom done ids bounds,search_none_iff_disagree done base geom ids bounds] at ambiguous
  obtain ⟨x,hx,y,hy,r,s,rx,sy,diff⟩ := ambiguous
  refine ⟨x,y,variant_placement (prepare?_certified done) hx,variant_placement (prepare?_certified done) hy,r,s,?_,?_,diff⟩
  · rwa [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)]
  · rwa [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)]

theorem inputGeometry_eq (i : Input) :
    LocalizedChemicalRingPhysicalSense.inputGeometry i.certified = geometry i.spatial := by
  funext n
  unfold LocalizedChemicalRingPhysicalSense.inputGeometry geometry
  split
  · simp [CertifiedLocalizedCIPInput.spatialPointAt?,i.spatial_eq]
  · rename_i h
    exact (List.getElem?_eq_none (by have len := full_original i; unfold size at len; omega)).symm

theorem fromRaw_closed_report (i : Input) (closed : plan i.molecule = [])
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (as : List i.certified.Atom) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial (as.map Fin.val) = RingChemicalReport.report? i as := by
  have resolved := (RingMolecularReport.resolve_iff i (as.map Fin.val) as).mpr rfl
  simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,readmit,
    RingChemicalReport.forAtoms?,resolved,prepared_closed i closed,admit]

end TetraStereo.Engine.RingWrittenPHReadings
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.ambiguity_has_written_witnesses

namespace TetraStereo.Engine.RingWrittenPHReadings
open OneCenter RingHydrogenCompletion RingPyramidalChoices RingSpatialTransport RingFrameTransport
open LocalizedChemicalRing (Input)
open LocalizedGenericMarkedRecalculation
open LocalizedActualPhysicalBranchDecision LocalizedChemicalRingPhysicalAdmission
open CertifiedLocalizedCIPInput (descriptorOfOrientedVolume?)

theorem pointVolume_readback (w : SpatialConfiguration) (ids : Fin 4 → Nat) :
    readback? (geometry w) (order ids 1) = (pointVolume w ids).bind descriptorOfOrientedVolume? := by
  unfold pointVolume readback? order geometry
  simp only [Equiv.Perm.one_apply,List.mapM_cons,List.mapM_nil]
  cases w.positions[ids 0]? <;> cases w.positions[ids 1]? <;>
    cases w.positions[ids 2]? <;> cases w.positions[ids 3]? <;> rfl

theorem centerAdmitted_readback (i : Input) (c : (actualCanonicalMolecule i.certified).Center) :
    centerAdmitted i.certified c =
      (readback? (geometry i.spatial) (order (centerIds i c) 1)).isSome := by
  rw [pointVolume_readback,←coordinateVolume_eq]
  unfold centerAdmitted
  cases coordinateVolume? i.certified c with
  | none => rfl
  | some v =>
    simp only [Option.bind_some]
    unfold descriptorOfOrientedVolume?
    split_ifs <;> simp_all <;> linarith

theorem coordinates_of_physicalAgreement (i : Input) (x : SpatialConfiguration)
    (full : x.positions.length = size i) (same : PhysicalAgreement i i.spatial x) :
    LocalizedChemicalRing.coordinatesAdmitted (atGeometry i x full) =
      LocalizedChemicalRing.coordinatesAdmitted i := by
  have center (c : (actualCanonicalMolecule i.certified).Center) :
      centerAdmitted (atGeometry i x full).certified c = centerAdmitted i.certified c := by
    rw [centerAdmitted_readback (atGeometry i x full),centerAdmitted_readback i]
    have read := same.tetra c
      (Equiv.ofBijective (i.certified.canonicalLigandNeighbor c)
        (i.certified.canonicalLigandNeighbor_bijective c)) false 1
    simp only [RingPhysicalFrameBridge.oriented_false] at read
    exact congrArg Option.isSome read.symm
  unfold LocalizedChemicalRing.coordinatesAdmitted allCentersAdmitted
  congr 1
  apply propext
  constructor <;> intro h c
  · exact (center c) ▸ h c
  · exact (center c).symm ▸ h c

theorem fromRaw_physicalAgreement (i : Input) (closed : plan i.molecule = [])
    (x : SpatialConfiguration) (full : x.positions.length = size i)
    (same : PhysicalAgreement i i.spatial x) (ids : List Nat) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids =
      RingHydrogenReport.fromRaw? i.molecule x ids := by
  let j := atGeometry i x full
  have geo := coordinates_of_physicalAgreement i x full same
  have closedj : plan j.molecule = [] := closed
  by_cases admitted : LocalizedChemicalRing.coordinatesAdmitted i = true
  · by_cases bounds : ∀ k ∈ ids, k < i.molecule.atomCount
    · have sizeEq := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
      let atoms : List i.certified.Atom := ids.attach.map fun k => ⟨k.val,by rw [sizeEq]; exact bounds _ k.property⟩
      have indices : atoms.map Fin.val = ids := by simp [atoms,List.map_map,Function.comp_def]
      rw [←indices,fromRaw_closed_report i closed admitted atoms]
      change RingChemicalReport.report? i atoms = RingHydrogenReport.fromRaw? j.molecule j.spatial (atoms.map Fin.val)
      apply Eq.trans (b := RingChemicalReport.report? j atoms)
      · rw [←reportG_input admitted,←reportG_input (geo.trans admitted),inputGeometry_eq i,inputGeometry_eq j]
        change reportG i (geometry i.spatial) atoms = reportG j (geometry x) atoms
        rw [reportG_reindex]
        exact reportG_transport atoms (fun q _ => RingPhysicalFrameBridge.siteAgree same q)
      · exact (fromRaw_closed_report j closedj (geo.trans admitted) atoms).symm
    · have off (z : SpatialConfiguration) : RingHydrogenReport.fromRaw? i.molecule z ids = none := by
        rw [RingHydrogenReport.fromRaw_closed_eq closed]
        cases found : RingChemicalReport.fromRaw? i.molecule z ids with
        | none => rfl
        | some rows => exact (bounds ((RingChemicalReport.fromRaw_domain_iff ..).mp ⟨rows,found⟩).1).elim
      rw [off i.spatial,off x]
  · have off (k : Input) (cl : plan k.molecule = []) (bad : LocalizedChemicalRing.coordinatesAdmitted k ≠ true) :
        RingHydrogenReport.fromRaw? k.molecule k.spatial ids = none := by
      rw [RingHydrogenReport.fromRaw_closed_eq cl]
      cases found : RingChemicalReport.fromRaw? k.molecule k.spatial ids with
      | none => rfl
      | some rows => exact (bad ((closed_domain k cl ids).mp ⟨rows,found⟩).2).elim
    exact (off i closed admitted).trans (off j closedj (fun h => admitted (geo ▸ h))).symm
end TetraStereo.Engine.RingWrittenPHReadings
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.fromRaw_physicalAgreement

namespace TetraStereo.Engine.RingWrittenPHReadings
open OneCenter RingHydrogenCompletion RingPyramidalChoices RingSpatialTransport
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report)

/-- A single generated geometry matches all public requests for a written placement.
Structural and geometric rejection are included. Only completion and the definition of
a nondegenerate written placement are premises. -/
theorem all_requests_represented {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (done : prepare? m g = some (out,pos)) (p : Placement m g out pos w) :
    ∃ x ∈ variants m g out pos, ∀ ids : List Nat,
      RingHydrogenReport.fromRaw? out w ids = RingHydrogenReport.fromRaw? out x ids := by
  have cert := prepare?_certified done
  have closed := prepare?_closed done
  cases hw : LocalizedChemicalRing.admitRawSpatial? out w with
  | some i =>
    obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields hw
    obtain ⟨x,hx,agree⟩ := represent_all_centers p cert i hm
    have len : x.positions.length = size i :=
      (variants_positions_length hx).trans (p.full.symm.trans (hg ▸ full_original i))
    have all := fromRaw_physicalAgreement i (hm ▸ closed) x len (hg ▸ agree)
    exact ⟨x,hx,by simpa only [hm,hg] using all⟩
  | none =>
    obtain ⟨ps,hps⟩ := choices_exists (sites m g out pos) pos.positions
    let x : SpatialConfiguration := ⟨ps⟩
    have hx : x ∈ variants m g out pos := List.mem_map.mpr ⟨ps,hps,rfl⟩
    have absent : LocalizedChemicalRing.admitRawSpatial? out x = none := by
      cases h : LocalizedChemicalRing.admitRawSpatial? out x with
      | none => rfl
      | some j =>
        obtain ⟨k,hk⟩ := (admission_iff_length h w).mpr (p.full.trans cert.positions_length)
        rw [hw] at hk
        contradiction
    refine ⟨x,hx,fun ids => ?_⟩
    simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,hw,absent]

theorem fromRaw_all_placements {m out : RawMolecule} {g pos : SpatialConfiguration}
    {source : Input} (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (geo : LocalizedChemicalRing.coordinatesAdmitted source = true) (done : prepare? m g = some (out,pos))
    (ids : List Nat) (bounds : ∀ k ∈ ids, k < m.atomCount) (rows : Report) :
    RingHydrogenReport.fromRaw? m g ids = some rows ↔
      ∀ w, Placement m g out pos w → RingHydrogenReport.fromRaw? out w ids = some rows := by
  refine ⟨?_,fromRaw_of_all_written hs geo done ids bounds rows⟩
  intro yes w p
  rw [public_search hs geo done ids bounds,RingHydrogenReport.search?_iff] at yes
  obtain ⟨x,hx,same⟩ := all_requests_represented done p
  rw [same ids,RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)]
  obtain ⟨ps,hps,rfl⟩ := List.mem_map.mp hx
  exact yes ps hps

end TetraStereo.Engine.RingWrittenPHReadings
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.all_requests_represented
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.fromRaw_all_placements

namespace TetraStereo.Engine.RingWrittenPHReadings
open OneCenter RingHydrogenCompletion RingPyramidalChoices RingSpatialTransport
open RingGroupedReport (Report)
open LocalizedChemicalRing (Input)

/-- Any successful request supplies the actual original admission, its coordinate check,
and bounds for every requested source ID, including when preparation uses the closed fast path. -/
private theorem source_of_success {m : RawMolecule} {g : SpatialConfiguration} {ids : List Nat}
    {rows : Report} (ok : RingHydrogenReport.fromRaw? m g ids = some rows) :
    ∃ s, LocalizedChemicalRing.admitRawSpatial? m g = some s ∧
      LocalizedChemicalRing.coordinatesAdmitted s = true ∧ (∀ n ∈ ids, n < m.atomCount) := by
  by_cases closed : plan m = []
  · rw [RingHydrogenReport.fromRaw_closed_eq closed] at ok
    obtain ⟨bound,s,i,hs,prep⟩ := (RingChemicalReport.fromRaw_domain_iff ..).mp ⟨rows,ok⟩
    exact ⟨s,hs,prep.1,bound⟩
  · obtain ⟨p,hp,_⟩ := (RingHydrogenReport.fromRaw_graph_iff ..).mp ok
    cases hs : LocalizedChemicalRing.admitRawSpatial? m g with
    | none => simp [RingHydrogenReport.preparedGeometry?,closed,hs] at hp
    | some s =>
      have hm := (RingChemicalReport.admission_fields hs).1
      simp only [RingHydrogenReport.preparedGeometry?,closed,List.isEmpty_iff,if_false,hs,
        Option.bind_some,RingHydrogenReport.preparedSource?,Option.bind_eq_bind,Option.bind_eq_some_iff] at hp
      by_cases geom : LocalizedChemicalRing.coordinatesAdmitted s = true
      · refine ⟨s,rfl,geom,?_⟩
        by_contra no
        simp [geom,hm,no,guard] at hp
      · simp [geom,guard] at hp

/-- Total raw specification. The original input passes admission and its atom IDs are in range. Every allowed written placement
must support the same population-selected graph derivation, at every recursive depth. -/
def WrittenPopulationReport (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (rows : Report) : Prop :=
  ∃ (source : Input) (out : RawMolecule) (pos : SpatialConfiguration),
    LocalizedChemicalRing.admitRawSpatial? m g = some source ∧
    LocalizedChemicalRing.coordinatesAdmitted source = true ∧ (∀ k ∈ ids, k < m.atomCount) ∧
    prepare? m g = some (out,pos) ∧ ∀ w, Placement m g out pos w →
      RingHydrogenReport.Graph RingPopulationReport.Correct (out,w) ids rows

theorem fromRaw_iff_written_population (m : RawMolecule) (g : SpatialConfiguration)
    (ids : List Nat) (rows : Report) :
    RingHydrogenReport.fromRaw? m g ids = some rows ↔ WrittenPopulationReport m g ids rows := by
  constructor
  · intro ok
    obtain ⟨s,hs,geom,bound⟩ := source_of_success ok
    obtain ⟨hm,hg⟩ := RingChemicalReport.admission_fields hs
    have length : g.positions.length = m.atomCount := by
      rw [← hm,← hg,← s.molecule.toSemanticMolecule?_atomCount _ s.agreement.1]
      exact full_original s
    obtain ⟨out,pos,done,_,_⟩ := RingHydrogenCertificate.prepare?_total m g (hm ▸ s.admissible) length
    refine ⟨s,out,pos,hs,geom,bound,done,?_⟩
    intro w p
    have computed := (fromRaw_all_placements hs geom done ids bound rows).mp ok w p
    rw [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)] at computed
    exact (RingPopulationReport.fromRaw_iff ..).mp computed
  · rintro ⟨s,out,pos,hs,geom,bound,done,all⟩
    apply (fromRaw_all_placements hs geom done ids bound rows).mpr
    intro w p
    rw [RingHydrogenReport.fromRaw_closed_eq (prepare?_closed done)]
    exact (RingPopulationReport.fromRaw_iff ..).mpr (all w p)

/-- On the admitted domain, and with valid original atom IDs, every outer refusal is a
genuine ambiguity among written nondegenerate placements, and every such ambiguity forces refusal. -/
theorem fromRaw_none_iff_written_conflict {m out : RawMolecule} {g pos : SpatialConfiguration}
    {source i : Input} (hs : LocalizedChemicalRing.admitRawSpatial? m g = some source)
    (geo : LocalizedChemicalRing.coordinatesAdmitted source = true) (done : prepare? m g = some (out,pos))
    (base : LocalizedChemicalRing.admitRawSpatial? out pos = some i)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ids : List Nat) (bounds : ∀ k ∈ ids, k < m.atomCount) :
    RingHydrogenReport.fromRaw? m g ids = none ↔
      ∃ x y, Placement m g out pos x ∧ Placement m g out pos y ∧ ∃ r s : Report,
        RingHydrogenReport.fromRaw? out x ids = some r ∧ RingHydrogenReport.fromRaw? out y ids = some s ∧ r ≠ s := by
  refine ⟨ambiguity_has_written_witnesses hs geo done base admit ids bounds,?_⟩
  rintro ⟨x,y,hx,hy,r,s,hr,hs',ne⟩
  cases found : RingHydrogenReport.fromRaw? m g ids with
  | none => rfl
  | some rows =>
    have all := (fromRaw_all_placements hs geo done ids bounds rows).mp found
    exact (ne ((Option.some.inj (hr.symm.trans (all x hx))).trans (Option.some.inj ((all y hy).symm.trans hs')))).elim

end TetraStereo.Engine.RingWrittenPHReadings
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.fromRaw_iff_written_population
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.fromRaw_none_iff_written_conflict
