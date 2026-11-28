import TetraStereo.Engine.RingFoldedLigandInventory
import TetraStereo.Engine.RingConstitutionalResidual
import TetraStereo.Engine.RingStereoInventoryReport
import TetraStereo.Engine.RingFrameTransport

/-! Folded ordinary ligand keys in tetrahedral and pyramidal residual trials.
The evaluator commits its own auxiliary rows before evaluating the root. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFoldedLigandReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingActiveDistanceSchedule (Cell Rule)
open RingFullPathEligibility (Key)
open RingFoldedLigandInventory (key? molecular_key_exact)

private def keys? {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) :=
  RingActivePairReport.four? fun s => key? i r rev (RingGroupedCentre.cursor fr s)

private theorem keys_exact {i f} (fr : @Frame i f) {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) : keys? fr r rev = RingStereoInventoryReport.keys? fr r rev := by
  rw [RingStereoInventoryReport.keys_exact]
  unfold keys? RingFullPathPublication.keys?
  congr 1
  funext s
  exact molecular_key_exact ready rev _ (RingGroupedCentre.valid fr s) (fr.direction s).property.1

private def centre? {i f} (fr : @Frame i f) (r : Reader i) : Cell := do
  let ks ← keys? fr r false
  let ms ← keys? fr r true
  let out ← RingFullPathTrialReadings.readingsWith fr r false ks
  return RingFullPathPublication.letters ks ms (out.map Prod.snd)

private def ligands? (i : Input) (q : Site i) (r : Reader i) (rev : Bool) :=
  (RingRetainedAuxiliary.frame i.certified q).mapM fun arm => do
    let atom ← arm.occurrence.val.node.current?
    let priority ← key? i r rev arm
    return (⟨arm,atom.val,priority⟩ : RingPyramidalPublication.Ligand i)

private theorem ligands_exact {i : Input} {q : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready q r) (rev : Bool) :
    ligands? i q r rev = RingStereoInventoryReport.ligands? i q r rev := by
  rw [RingStereoInventoryReport.ligands_exact]
  unfold ligands? RingPyramidalPublication.ligands?
  apply RingFrameTransport.mapM_congr_mem
  intro arm member
  have frame := i.certified.executableLocalizedRerootChildren_declarative (⟨q,none⟩ : Arm i)
  rw [molecular_key_exact ready rev arm (i.certified.localizedRerootChild_valid _ _ _ frame member)
    (i.certified.localizedRerootChildren_root_eq _ _ _ frame member)]

private def hands? (i : Input) (q : Site i) (r : Reader i) (a : i.certified.Atom) (rev : Bool) :
    Option (List (Option RS)) := do
  let xs ← ligands? i q r rev
  let marks : List (Option Nat) := match xs with
    | [x,y,z] => if x.priority == y.priority && y.priority == z.priority then
        [some x.atom,some y.atom,some z.atom] else [none]
    | _ => []
  marks.mapM (RingPyramidalPublication.trial? r a rev xs)

private def pLabels (i : Input) (q : Site i) (r : Reader i) (a : i.certified.Atom) := do
  guard ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  let hs ← hands? i q r a false
  let ms ← hands? i q r a true
  RingFullPathPublication.crossed hs ms

/-- The preceding direct constitutional and molecular checks have already failed
at each actual call to this residual rule. -/
def residual (i : Input) : Rule i := fun q r =>
  match RingPyramidalPublication.focusP i q with
  | some a => some (pLabels i q r a)
  | none => match RingNestedActivePair.frame? i q with
    | none => some none
    | some fr => centre? fr r

private theorem agree (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingResidualPriority.ResidualAgreement (RingConstitutionalResidual.direct i) (residual i) := by
  intro q miss
  let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) q
  have ready : RingGroupedStereo.Ready q r := RingChemicalGraphProof.ready ok q
  change residual i q r = RingPyramidalPublication.publish i q r
  rw [← RingStereoInventoryReport.publish_exact]
  have early := (RingConstitutionalResidual.misses miss).1
  simp only [residual,RingStereoInventoryReport.publish,RingLigandTreeStore.early_exact,early,
    RingStereoInventoryReport.tetra?,centre?,RingStereoInventoryReport.centre?,keys_exact _ ready,
    pLabels,RingStereoInventoryReport.pLabels,hands?,RingStereoInventoryReport.hands?,ligands_exact ready]
  rfl

abbrev rows (i : Input) := RingConstitutionalResidual.rows i (residual i)
abbrev report (i : Input) := RingConstitutionalResidual.report i (residual i)
def fromRaw? := RingConstitutionalResidual.fromRaw? residual

/-- Includes the order, multiplicity and cell of every committed row at every cut. -/
theorem rows_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) :
    rows i a k = RingSphereStore.rows i a k :=
  (RingConstitutionalResidual.stores_and_reports ok _ (agree i ok)).1 a k bound

theorem report_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : report i atoms = RingChemicalReport.report? i atoms :=
  (RingConstitutionalResidual.stores_and_reports ok _ (agree i ok)).2 atoms

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? :=
  RingConstitutionalResidual.raw_exact residual agree

end TetraStereo.Engine.RingFoldedLigandReport
assert_kernel_only TetraStereo.Engine.RingFoldedLigandReport.rows_exact
assert_kernel_only TetraStereo.Engine.RingFoldedLigandReport.report_exact
assert_kernel_only TetraStereo.Engine.RingFoldedLigandReport.raw_exact
