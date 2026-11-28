import TetraStereo.Examples.AntipodalCyclohexaneReport
import TetraStereo.Engine.RingChemicalRenumbering

/-! Reports for the explicit cyclohexane-1,4-diol graph in target atom numbering. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneNumbering
open Engine OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input coordinatesAdmitted)
open RingRawRenumbering (AtomMap)
open RingReportRenumber (renameId)
open RingWrittenPHReadings (geometry)
open AntipodalCyclohexaneHands (molecule frameRow)
open AntipodalCyclohexaneReport (label)
open private closed from TetraStereo.Examples.AntipodalCyclohexaneTransport
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

private theorem read (r : AtomMap i j) (f : Fin 2) :
    readback? (geometry i.spatial) (frameRow f) =
      readback? (geometry j.spatial) ((frameRow f).map (renameId r)) := by
  simpa [RingFrameTransport.senseOf,RingWrittenPHReadings.inputGeometry_eq] using
    RingReportRenumber.read_ids r false (frameRow f)

/-- Read the two ordered tetrahedra using the target's own coordinates and labels. -/
def expected? (r : AtomMap i j) (ids : List Nat) : Option RingGroupedReport.Report := do
  guard (ids.all (· < 20))
  let a ← readback? (geometry j.spatial) ((frameRow 0).map (renameId r))
  let b ← readback? (geometry j.spatial) ((frameRow 1).map (renameId r))
  return ids.map fun n => (n,if n = renameId r 0 ∨ n = renameId r 3 then some (label a b) else none)

open private index_bound from TetraStereo.Engine.RingChemicalRenumbering

theorem raw_agreement (r : AtomMap i j) (raw : i.molecule = molecule)
    (geom : coordinatesAdmitted i = true) (cl : RingHydrogenCompletion.plan j.molecule = [])
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial ids = expected? r ids := by
  have src : i.molecule.atomCount = 20 := by rw [raw]; rfl
  have counts : i.molecule.atomCount = j.molecule.atomCount := by
    rw [←i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1,
      ←j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1]
    simpa using Fintype.card_congr r.atoms
  have back (n : Nat) : decide (renameId r.symm n < 20) = decide (n < 20) := by
    have h := index_bound r.symm n
    rw [←counts,src] at h
    simp only [h]
  have selected (n k : Nat) : renameId r.symm n = k ↔ n = renameId r k :=
    ⟨fun h => (inverse r n).symm.trans (congrArg (renameId r) h),fun h => by
      subst n
      exact inverse r.symm k⟩
  have mapped : (ids.map (renameId r.symm)).map (renameId r) = ids := by
    simp [List.map_map,Function.comp_def,inverse]
  have report := RingReportRenumber.closed_raw_report r (raw ▸ closed) cl (ids.map (renameId r.symm))
  rw [mapped,raw,AntipodalCyclohexaneReport.raw_agreement i raw geom] at report
  rw [report]
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (AntipodalCyclohexaneHands.nonflat raw geom 0)
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (AntipodalCyclohexaneHands.nonflat raw geom 1)
  simp only [expected?,AntipodalCyclohexaneReport.expected?,←read r,ha,hb,List.all_map,
    Function.comp_def,back]
  by_cases ok : ids.all (· < 20) = true
  · simp [ok,List.map_map,Function.comp_def,RingRawRenumbering.AtomMap.renameRow,
      selected]
    intro n _
    exact inverse r n
  · simp [ok]

/-- Recover the two ordered rows by matching full atom records, pairwise bond
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

open private atom_bound from TetraStereo.Examples.AntipodalCyclohexaneTransport
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
  have atoms : ∀ k : Fin 20, ∃ t ∈ ([Element.C,.H,.O] : List Element),
      molecule.atoms[k.val]? = some (AtomSpec.aliphatic t) := by decide +kernel
  obtain ⟨t,ht,lookup⟩ := atoms ⟨u.val,atom_bound raw u⟩
  rw [lookup] at records
  have eq := congrArg RingRawRenumbering.MolecularRecord.element (Option.some.inj records)
  change (j.molecule.atoms[n]'hj).element = t at eq
  have elem := el.symm.trans eq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp [RingPyramidalChoices.eligibleAtom,elem] at yes

/-- Read any original query after successful completion to the numbered diol.
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

end TetraStereo.Examples.AntipodalCyclohexaneNumbering
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneNumbering.raw_agreement
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneNumbering.searched_agreement
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneNumbering.prepared_agreement
