import TetraStereo.Engine.RingChemicalRenumbering

/-! Transport a closed-graph report formula to a prepared and renumbered input. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPreparedReportFormula
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input coordinatesAdmitted)
open RingRawRenumbering (AtomMap)
open RingReportRenumber (renameId)
variable {i j : Input}

abbrev Formula := List Nat → Option RingGroupedReport.Report

def transport (r : AtomMap i j) (formula : Formula) (ids : List Nat) :=
  (formula (ids.map (renameId r.symm))).map (List.map r.renameRow)

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

theorem closed_agreement (r : AtomMap i j) (formula : Formula)
    (exactSource : ∀ ids, RingHydrogenReport.fromRaw? i.molecule i.spatial ids = formula ids)
    (cl : RingHydrogenCompletion.plan i.molecule = []) (cl' : RingHydrogenCompletion.plan j.molecule = [])
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? j.molecule j.spatial ids = transport r formula ids := by
  have report := RingReportRenumber.closed_raw_report r cl cl' (ids.map (renameId r.symm))
  simpa [transport,List.map_map,Function.comp_def,inverse,exactSource] using report

def NoChoiceElements (m : RawMolecule) : Prop :=
  ∀ a ∈ m.atoms, ¬ (a.element = .P ∨ a.element = .As ∨ a.element = .Sb)

open private closed_reject from TetraStereo.Engine.RingChemicalRenumbering

private theorem source_light (r : AtomMap i j) (light : NoChoiceElements i.molecule) {s : Input}
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
  rw [mapped] at records
  change (j.molecule.atoms[n]?).map _ = _ at records
  rw [hb] at records
  cases lookup : i.molecule.atoms[u.val]? with
  | none => simp [lookup] at records
  | some t =>
    rw [lookup] at records
    have eq := congrArg RingRawRenumbering.MolecularRecord.element (Option.some.inj records)
    change (j.molecule.atoms[n]'hj).element = t.element at eq
    have elem := el.symm.trans eq
    have off := light t (List.mem_of_getElem? lookup)
    simp [RingPyramidalChoices.eligibleAtom,elem,off] at yes

theorem prepared_agreement (r : AtomMap i j) (formula : Formula)
    (exactSource : ∀ ids, RingHydrogenReport.fromRaw? i.molecule i.spatial ids = formula ids)
    (clSource : RingHydrogenCompletion.plan i.molecule = []) (light : NoChoiceElements i.molecule) {s : Input} (sourceGeom : coordinatesAdmitted s = true)
    (prepared : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (j.molecule,j.spatial))
    (ids : List Nat) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial ids =
      if ids.all (· < s.molecule.atomCount) then transport r formula ids else none := by
  have fixed : RingPyramidalChoices.sites s.molecule s.spatial j.molecule j.spatial = [] := by
    simp [RingPyramidalChoices.sites,RingPyramidalChoices.site?,source_light r light prepared]
  by_cases ok : ids.all (· < s.molecule.atomCount) = true
  · rw [if_pos ok,RingHydrogenReport.fromRaw_materialized_eq (RingSpatialTransport.readmit s) sourceGeom
      prepared fixed ids (fun n hn => of_decide_eq_true (List.all_eq_true.mp ok n hn))]
    exact closed_agreement r formula exactSource clSource (RingHydrogenCompletion.prepare?_closed prepared) ids
  · rw [if_neg ok]
    by_cases cl : RingHydrogenCompletion.plan s.molecule = []
    · exact closed_reject cl ids (fun h => ok (List.all_eq_true.mpr fun n hn => decide_eq_true (h.1 n hn)))
    · have bad : ¬ ∀ x ∈ ids, x < s.molecule.atomCount := fun h =>
        ok (List.all_eq_true.mpr fun n hn => decide_eq_true (h n hn))
      simp [RingHydrogenReport.fromRaw?,RingHydrogenReport.preparedGeometry?,cl,
        RingSpatialTransport.readmit s,RingHydrogenReport.preparedSource?,sourceGeom,bad]

end TetraStereo.Engine.RingPreparedReportFormula
assert_kernel_only TetraStereo.Engine.RingPreparedReportFormula.closed_agreement
assert_kernel_only TetraStereo.Engine.RingPreparedReportFormula.prepared_agreement
