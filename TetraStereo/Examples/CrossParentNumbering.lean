import TetraStereo.Examples.CrossParentAllAtoms
import TetraStereo.Engine.RingPreparedReportFormula

/-! The count-based formula in the numbering of any matching prepared input. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentNumbering
open Engine OneCenter
open LocalizedChemicalRing (Input coordinatesAdmitted)
open RingRawRenumbering (AtomMap)
open CrossParentDonorStore (molecule)
open private closed from TetraStereo.Examples.CrossParentAllAtoms
variable {i j : Input}

def expected? (r : AtomMap i j) :=
  RingPreparedReportFormula.transport r (CrossParentAllAtoms.expected? i.spatial)

theorem raw_agreement (r : AtomMap i j) (raw : i.molecule = molecule)
    (ok : coordinatesAdmitted i = true) (closedTarget : RingHydrogenCompletion.plan j.molecule = [])
    (ids : List Nat) : RingHydrogenReport.fromRaw? j.molecule j.spatial ids = expected? r ids :=
  RingPreparedReportFormula.closed_agreement r _ (fun xs => raw ▸ CrossParentAllAtoms.raw_agreement i raw ok xs)
    (raw ▸ closed) closedTarget ids

private theorem light : RingPreparedReportFormula.NoChoiceElements molecule := by
  unfold RingPreparedReportFormula.NoChoiceElements
  decide +kernel

theorem prepared_agreement (r : AtomMap i j) (raw : i.molecule = molecule)
    (ok : coordinatesAdmitted i = true) {s : Input} (sourceGeom : coordinatesAdmitted s = true)
    (prepared : RingHydrogenCompletion.prepare? s.molecule s.spatial = some (j.molecule,j.spatial))
    (ids : List Nat) : RingHydrogenReport.fromRaw? s.molecule s.spatial ids =
      if ids.all (· < s.molecule.atomCount) then expected? r ids else none :=
  RingPreparedReportFormula.prepared_agreement r _ (fun xs => raw ▸ CrossParentAllAtoms.raw_agreement i raw ok xs)
    (raw ▸ closed) (raw ▸ light) sourceGeom prepared ids

end TetraStereo.Examples.CrossParentNumbering
assert_kernel_only TetraStereo.Examples.CrossParentNumbering.raw_agreement
assert_kernel_only TetraStereo.Examples.CrossParentNumbering.prepared_agreement
