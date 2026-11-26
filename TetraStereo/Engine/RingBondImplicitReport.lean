import TetraStereo.Engine.RingBondHydrogenSites
import TetraStereo.Engine.RingBondRecordAdmission
import TetraStereo.Engine.RingBondVariantReadback

/-! Full public report invariance under raw bond-table permutations, through
implicit hydrogen preparation and every independent pyramidal placement. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBondRecordOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingHydrogenCompletion (plan prepare?)
open RingPyramidalChoices (sites choices)
open RingHydrogenReport (search?)
variable {i j : Input}

private theorem added_report (i : Input) (ids : List Nat) {out : RawMolecule} {pos : SpatialConfiguration}
    (openPlan : plan i.molecule ≠ []) (done : prepare? i.molecule i.spatial = some (out,pos)) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids =
      if LocalizedChemicalRing.coordinatesAdmitted i && ids.all (fun n => decide (n < i.molecule.atomCount))
      then search? (fun ps => RingChemicalReport.fromRaw? out ⟨ps⟩ ids)
        (sites i.molecule i.spatial out pos) pos.positions else none := by
  have nonempty : (plan i.molecule).isEmpty = false := List.isEmpty_eq_false_iff.mpr openPlan
  cases geom : LocalizedChemicalRing.coordinatesAdmitted i <;>
    by_cases bounds : ∀ n ∈ ids, n < i.molecule.atomCount <;>
    simp [RingHydrogenReport.fromRaw?, RingHydrogenReport.preparedGeometry?, nonempty,
      RingSpatialTransport.readmit, RingHydrogenReport.preparedSource?, geom, bounds, done, guard]
  simp only [if_pos bounds, Option.bind_some]

private theorem coordinate_gate (p : Presentation i j) :
    LocalizedChemicalRing.coordinatesAdmitted i = LocalizedChemicalRing.coordinatesAdmitted j := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨RingRawRenumbering.coordinates (identityRenumbering p),
    RingRawRenumbering.coordinates (identityRenumbering p).symm⟩

private theorem all_reads {s t : RawMolecule} {ps qs : List RingHydrogenCompletion.Point}
    {x y : List RingPyramidalChoices.Site} (ids : List Nat)
    (families : (choices x ps).Perm (choices y qs))
    (same : ∀ g : SpatialConfiguration, RingChemicalReport.fromRaw? t g ids = RingChemicalReport.fromRaw? s g ids) :
    search? (fun points => RingChemicalReport.fromRaw? t ⟨points⟩ ids) y qs =
      search? (fun points => RingChemicalReport.fromRaw? s ⟨points⟩ ids) x ps := by
  apply Option.ext
  intro rows
  rw [RingHydrogenReport.search?_iff, RingHydrogenReport.search?_iff]
  simp only [same, families.mem_iff]

private theorem completed_readback {out out' : RawMolecule} {pos pos' : SpatialConfiguration}
    (p : Presentation i j)
    (left : prepare? i.molecule i.spatial = some (out,pos))
    (right : prepare? j.molecule j.spatial = some (out',pos'))
    (g : SpatialConfiguration) (ids : List Nat) :
    RingChemicalReport.fromRaw? out' g ids = RingChemicalReport.fromRaw? out g ids := by
  obtain ⟨atoms,bonds,_⟩ := prepared_records p left right
  have gates := RingBondAdmission.public_admission atoms bonds
    (RingHydrogenCompletion.prepare?_certified left).output_admissible
    (RingHydrogenCompletion.prepare?_certified right).output_admissible g
  cases hi : LocalizedChemicalRing.admitRawSpatial? out g with
  | none =>
    cases hj : LocalizedChemicalRing.admitRawSpatial? out' g with
    | none => simp [RingChemicalReport.fromRaw?,hi,hj]
    | some _ => simp [hi,hj] at gates
  | some u =>
    obtain ⟨v,hj⟩ := Option.isSome_iff_exists.mp (gates.mp (by simp [hi]))
    obtain ⟨um,_⟩ := RingChemicalReport.admission_fields hi
    obtain ⟨vm,_⟩ := RingChemicalReport.admission_fields hj
    have closed := RingHydrogenCompletion.prepare?_closed left
    have closed' := RingHydrogenCompletion.prepare?_closed right
    rw [← um] at atoms bonds closed
    rw [← vm] at atoms bonds closed'
    simpa only [um,vm] using RingBondVariantReadback.at_coordinates u v atoms bonds closed closed' g ids

/-- Independently admitted presentations may carry different written neighbor
orders. Every requested raw row is identical, even when additional hydrogens
must be placed on several pyramidal centers. -/
theorem implicit_raw_public (p : Presentation i j) (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial ids = RingHydrogenReport.fromRaw? i.molecule i.spatial ids := by
  have plans := plan_eq p
  by_cases closed : plan i.molecule = []
  · exact closed_raw_public p closed (plans.symm.trans closed) ids
  have other : plan j.molecule ≠ [] := plans ▸ closed
  have full (s : Input) := (RingSpatialTransport.full_original s).trans
    (s.molecule.toSemanticMolecule?_atomCount _ s.agreement.1)
  obtain ⟨out,pos,left,lc,_⟩ := RingHydrogenCertificate.prepare?_total _ _ i.admissible (full i)
  obtain ⟨out',pos',right,rc,_⟩ := RingHydrogenCertificate.prepare?_total _ _ j.admissible (full j)
  have families := RingBondHydrogenSites.choices_perm p lc rc (prepared_records p left right).2.2
  rw [added_report i ids closed left, added_report j ids other right, coordinate_gate p, raw_atomCount p,
    all_reads ids families (fun g => completed_readback p left right g ids)]

private theorem reject {m : RawMolecule} {g : SpatialConfiguration}
    (bad : LocalizedChemicalRing.admitRawSpatial? m g = none) (ids : List Nat) :
    RingHydrogenReport.fromRaw? m g ids = none := by
  cases empty : (plan m).isEmpty <;>
    simp [RingHydrogenReport.fromRaw?, RingHydrogenReport.preparedGeometry?, empty,
      RingHydrogenReport.search?, RingChemicalReport.fromRaw?, bad]

/-- No admission hypothesis is needed when the recorded neighbor-order table
is fixed. All coordinates and requests are quantified, including malformed
inputs and invalid IDs. -/
theorem raw_public {m n : RawMolecule} (atoms : m.atoms = n.atoms) (bonds : m.bonds.Perm n.bonds)
    (orders : m.neighborOrder = n.neighborOrder) (g : SpatialConfiguration) (ids : List Nat) :
    RingHydrogenReport.fromRaw? n g ids = RingHydrogenReport.fromRaw? m g ids := by
  have gates := RingBondRecordAdmission.public_admission atoms bonds orders g
  cases hi : LocalizedChemicalRing.admitRawSpatial? m g with
  | none =>
    cases hj : LocalizedChemicalRing.admitRawSpatial? n g with
    | none => rw [reject hi, reject hj]
    | some _ => simp [hi,hj] at gates
  | some u =>
    obtain ⟨v,hj⟩ := Option.isSome_iff_exists.mp (gates.symm.trans (by simp [hi]))
    obtain ⟨um,ug⟩ := RingChemicalReport.admission_fields hi
    obtain ⟨vm,vg⟩ := RingChemicalReport.admission_fields hj
    have p : Presentation u v := ⟨um ▸ vm ▸ atoms, um ▸ vm ▸ bonds, by rw [ug,vg]⟩
    simpa only [um,vm,ug,vg] using implicit_raw_public p ids

end TetraStereo.Engine.RingBondRecordOrder
assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.implicit_raw_public
assert_kernel_only TetraStereo.Engine.RingBondRecordOrder.raw_public
