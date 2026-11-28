import TetraStereo.Examples.HexachlorocyclohexanePublicReport
import TetraStereo.Engine.RingChemicalRenumbering

/-! Reports for the explicit hexachlorocyclohexane graph in target atom numbering. -/
set_option autoImplicit false
namespace TetraStereo.Examples.HexachlorocyclohexanePublicNumbering
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input coordinatesAdmitted)
open RingRawRenumbering (AtomMap)
open RingReportRenumber (renameId)
open RingWrittenPHReadings (geometry)
open BlueBookHexachlorocyclohexane (molecule)
open private closed size_bound from TetraStereo.Examples.HexachlorocyclohexanePublicReport
variable {i j : Input}

private theorem inverse (r : AtomMap i j) (n : Nat) :
    renameId r (renameId r.symm n) = n := by
  have sizes : i.certified.certified.input.molecule.atomCount = j.certified.certified.input.molecule.atomCount := by
    simpa using Fintype.card_congr r.atoms
  by_cases h : n < j.certified.certified.input.molecule.atomCount
  · let v : j.certified.Atom := ⟨n,h⟩
    change renameId r (renameId r.symm v.val) = v.val
    simp [RingRawRenumbering.AtomMap.symm]
  · have hn : ¬ n < i.certified.certified.input.molecule.atomCount := by omega
    simp [renameId,h,hn]

/-- Evaluate the six cyclic frames from target coordinates. Translate queries
back to the canonical ring numbering and restore each reported target ID. -/
def expected? (r : AtomMap i j) (ids : List Nat) : Option RingGroupedReport.Report :=
  let g := fun n => geometry j.spatial (renameId r n)
  ((ids.map (renameId r.symm)).mapM (HexachlorocyclohexanePublicReport.expectedRow? g)).map
    (List.map r.renameRow)

theorem raw_agreement (r : AtomMap i j) (raw : i.molecule = molecule)
    (geom : coordinatesAdmitted i = true) (cl : RingHydrogenCompletion.plan j.molecule = [])
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial ids = expected? r ids := by
  have points : geometry i.spatial = fun n => geometry j.spatial (renameId r n) := by
    funext n
    simpa only [RingWrittenPHReadings.inputGeometry_eq] using RingReportRenumber.geometry_id r n
  have mapped : (ids.map (renameId r.symm)).map (renameId r) = ids := by
    simp [List.map_map,Function.comp_def,inverse]
  have report := RingReportRenumber.closed_raw_report r (raw ▸ closed) cl (ids.map (renameId r.symm))
  rw [mapped,raw,HexachlorocyclohexanePublicReport.raw_agreement i raw geom] at report
  simpa only [HexachlorocyclohexanePublicReport.expected?,expected?,points] using report

/-- Recover the cyclic frames by matching full atom records, pairwise bond
orders, and the supplied coordinates. Bond list order is immaterial. -/
def searched? (i j : Input) (ids : List Nat) : Option RingGroupedReport.Report := do
  let r ← RingRawRenumbering.find? i j
  expected? r.toAtomMap ids

theorem searched_agreement (raw : i.molecule = molecule)
    (geom : coordinatesAdmitted i = true) (cl : RingHydrogenCompletion.plan j.molecule = [])
    (found : (RingRawRenumbering.find? i j).isSome = true) (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial ids = searched? i j ids := by
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp found
  simpa [searched?,hr] using raw_agreement r.toAtomMap raw geom cl ids

open private closed_reject from TetraStereo.Engine.RingChemicalRenumbering

private theorem source_light (r : AtomMap i j) (raw : i.molecule = molecule) {s : Input}
    (prepared : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (j.molecule,j.spatial))
    (n : Nat) : (s.molecule.atoms[n]?).map RingPyramidalChoices.eligibleAtom ≠ some true := by
  intro lit
  obtain ⟨a,ha,yes⟩ := Option.map_eq_some_iff.mp lit
  have hn : n < s.molecule.atomCount := List.getElem?_eq_some_iff.mp ha |>.choose
  have cert := RingHydrogenCompletion.prepare?_certified prepared
  have hj := hn.trans_le cert.atomCount_le
  let v : j.certified.Atom := ⟨n,by rwa [j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1]⟩
  let u := r.atoms.symm v
  have hb : j.molecule.atoms[n]? = some (j.molecule.atoms[n]'hj) := List.getElem?_eq_getElem hj
  have el := (cert.atom_fields hn ha hb).1
  have records := r.records u
  have mapped : r.atoms u = v := r.atoms.apply_symm_apply _
  rw [mapped,raw] at records
  change (j.molecule.atoms[n]?).map _ = _ at records
  rw [hb] at records
  have atoms : ∀ k : Fin 18, ∃ t ∈ ([Element.C,.H,.Cl] : List Element),
      molecule.atoms[k.val]? = some (AtomSpec.aliphatic t) := by decide +kernel
  obtain ⟨t,ht,lookup⟩ := atoms ⟨u.val,size_bound raw u⟩
  rw [lookup] at records
  have eq := congrArg RingRawRenumbering.MolecularRecord.element (Option.some.inj records)
  change (j.molecule.atoms[n]'hj).element = t at eq
  have elem := el.symm.trans eq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp [RingPyramidalChoices.eligibleAtom,elem] at yes

/-- Read any original query after successful completion to the numbered hexachlorocyclohexane graph.
An out-of-range ID rejects the entire request even if completion added that ID. -/
theorem prepared_agreement (r : AtomMap i j) (raw : i.molecule = molecule)
    (geom : coordinatesAdmitted i = true) {s : Input} (sourceGeom : coordinatesAdmitted s = true)
    (prepared : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (j.molecule,j.spatial))
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial ids =
      if ids.all (· < s.molecule.atomCount) then expected? r ids else none := by
  have fixed : RingPyramidalChoices.sites s.molecule s.spatial j.molecule j.spatial = [] := by
    simp [RingPyramidalChoices.sites,RingPyramidalChoices.site?,source_light r raw prepared]
  by_cases ok : ids.all (· < s.molecule.atomCount) = true
  · rw [if_pos ok,RingHydrogenReport.fromRaw_materialized_eq (RingSpatialTransport.readmit s) sourceGeom
      prepared fixed ids (fun n hn => of_decide_eq_true (List.all_eq_true.mp ok n hn))]
    exact raw_agreement r raw geom (RingHydrogenCompletion.prepare?_closed prepared) ids
  · rw [if_neg ok]
    by_cases cl : RingHydrogenCompletion.plan s.molecule = []
    · exact closed_reject cl ids (fun h => ok (List.all_eq_true.mpr fun n hn => decide_eq_true (h.1 n hn)))
    · have bad : ¬ ∀ x ∈ ids, x < s.molecule.atomCount := fun h =>
        ok (List.all_eq_true.mpr fun n hn => decide_eq_true (h n hn))
      simp [RingHydrogenReport.fromRaw?,RingHydrogenReport.preparedGeometry?,cl,
        RingSpatialTransport.readmit s,RingHydrogenReport.preparedSource?,sourceGeom,bad]

end TetraStereo.Examples.HexachlorocyclohexanePublicNumbering
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicNumbering.raw_agreement
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicNumbering.searched_agreement
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicNumbering.prepared_agreement
