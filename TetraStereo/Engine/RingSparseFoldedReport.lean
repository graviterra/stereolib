import TetraStereo.Engine.RingRootIndexedEarly
import TetraStereo.Engine.RingFoldedLigandReport

/-! Sparse public sphere reports using bottom-up ordinary ligand ranks. Each
requested root shares one child reader across its residual trials and reflections. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSparseFoldedReport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingActiveDistanceSchedule (Cell Rule height frozen)
open RingSparseTwinReport (keep facts layers)
open RingSphereQueue (stored reader viewOf)
open RingSecondShellDecision (armsFast)
open private armsFast_eq frameWith? frameWith_eq from TetraStereo.Engine.RingSecondShellDecision
open private slots slots_eq from TetraStereo.Engine.RingRootIndexedEarly
open private collectWith from TetraStereo.Engine.RingFoldedLigandRanks
open private centre? keys? pLabels hands? ligands? keys_exact ligands_exact from
  TetraStereo.Engine.RingFoldedLigandReport
open private on_frozen from TetraStereo.Engine.RingSparseTwinReport

private abbrev Edges (i : Input) :=
  i.certified.LocalizedRerootChildReader (i.certified.certified.input.molecule.atomCount+1)

private def edges (i : Input) (a : i.certified.Atom) : Edges i :=
  SelectedRoot.reader i.certified _ a

private def readKey {i : Input} (rd : Edges i) (v : Reader i) (rev : Bool) (arm : Arm i) :=
  let n := i.certified.localizedRerootCursorBudget arm + 1
  (collectWith i v rev (fun a => (rd.readChildren a).getD []) n arm).bind
    (RingFoldedLigandInventory.key n)

private theorem readKey_eq {i : Input} (rd : Edges i) (v : Reader i) (rev : Bool) :
    readKey rd v rev = RingFoldedLigandInventory.key? i v rev := by
  funext arm
  simp only [readKey,RingFoldedLigandInventory.key?,RingFoldedLigandRanks.collect,
    LocalizedRerootChildReader.readChildren_eq,executableLocalizedRerootChildren?,Option.getD_some]

private def tetra {i : Input} {q : Site i} (rd : Edges i) (arms : List (Arm i))
    (h : arms = RingRetainedAuxiliary.frame i.certified q) (fr : Frame i q) (v : Reader i) : Cell := do
  let keys := fun rev => RingActivePairReport.four? fun s => readKey rd v rev (slots arms h fr s)
  let ks ← keys false
  let ms ← keys true
  let out ← RingFullPathTrialReadings.readingsWith fr v false ks
  return RingFullPathPublication.letters ks ms (out.map Prod.snd)

private theorem tetra_eq {i : Input} {q : Site i} (rd : Edges i) (arms : List (Arm i))
    (h : arms = RingRetainedAuxiliary.frame i.certified q) (fr : Frame i q) (v : Reader i) :
    tetra rd arms h fr v = centre? fr v := by
  simp only [tetra,centre?,keys?,readKey_eq,slots_eq]

private def phosphorus {i : Input} {q : Site i} (rd : Edges i) (v : Reader i)
    (a : i.certified.Atom) : Option RingNestedActivePair.Labels := do
  let arms := armsFast i q
  guard (arms.length = 3)
  let hands (rev : Bool) := do
    let xs ← arms.mapM fun arm => do
      let atom ← arm.occurrence.val.node.current?
      let k ← readKey rd v rev arm
      return (⟨arm,atom.val,k⟩ : RingPyramidalPublication.Ligand i)
    let marks : List (Option Nat) := match xs with
      | [x,y,z] => if x.priority == y.priority && y.priority == z.priority then
          [some x.atom,some y.atom,some z.atom] else [none]
      | _ => []
    marks.mapM (RingPyramidalPublication.trial? v a rev xs)
  RingFullPathPublication.crossed (← hands false) (← hands true)

private theorem phosphorus_eq {i : Input} {q : Site i} (rd : Edges i) (v : Reader i)
    (a : i.certified.Atom) : phosphorus (q := q) rd v a = pLabels i q v a := by
  simp only [phosphorus,pLabels,hands?,ligands?,armsFast_eq,readKey_eq]
  rfl

private def publish {i : Input} (rd : Edges i) : Rule i := fun q v =>
  match RingPyramidalPublication.focusP i q with
  | some a => some (phosphorus (q := q) rd v a)
  | none => match RingRootIndexedEarly.early? i q with
    | some s => some s.letters
    | none =>
      let arms := armsFast i q
      match frameWith? i q arms (armsFast_eq i q) with
      | none => some none
      | some fr => tetra rd arms (armsFast_eq i q) fr v

private theorem publish_ready {i : Input} (rd : Edges i) (q : Site i) {v : Reader i}
    (ready : RingGroupedStereo.Ready q v) :
    publish rd q v = RingPyramidalPublication.publish i q v := by
  rw [← RingStereoInventoryReport.publish_exact]
  simp only [publish,RingStereoInventoryReport.publish,RingRootIndexedEarly.early_exact,
    RingLigandTreeStore.early_exact,RingZeroMassReport.zero_early_exact,frameWith_eq,tetra_eq,
    RingStereoInventoryReport.tetra?,centre?,RingStereoInventoryReport.centre?,keys_exact _ ready,
    phosphorus_eq,pLabels,RingStereoInventoryReport.pLabels,hands?,RingStereoInventoryReport.hands?,
    ligands_exact ready]
  rfl

private def residual {i : Input} (rd : Edges i) :=
  RingResidualPriority.splice (facts i) (publish rd)

private abbrev full {i : Input} (rd : Edges i) := RingSparseRefusalStore.guarded (keep i) (residual rd)

private theorem full_frozen {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (rd : Edges i) (q : Site i) : full rd q (frozen (RingChemicalGraphProof.state i) q) =
      RingPyramidalPublication.publish i q (frozen (RingChemicalGraphProof.state i) q) := by
  rw [← on_frozen ok q]
  simp only [full,RingSparseTwinReport.full,RingSparseRefusalStore.guarded,residual,
    RingSparseTwinReport.residual,RingResidualPriority.splice,publish_ready rd q (RingChemicalGraphProof.ready ok q)]

private theorem full_rows {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (rd : Edges i) (a : i.certified.Atom) (k : Nat) (bound : k ≤ height i+1) :
    stored (full rd) a (RingGlobalComparison.queue i a) (height i) k = RingSphereStore.rows i a k := by
  apply (RingGlobalComparison.rows_or_difference (RingConstitutionalResidual.publications i)
    (full rd) a k bound).resolve_right
  rintro ⟨n,_,q,d⟩
  apply d.2.2.1
  change full rd q (RingGlobalComparison.prior i a n) = _
  rw [RingGlobalComparison.prior_exact d.1]
  exact full_frozen ok rd q

private def sparseWith {i : Input} (rd : Edges i) (a : i.certified.Atom) (cut : Nat) :=
  let n := i.certified.certified.input.molecule.atomCount
  let qs := layers i a
  RingSparseRefusalStore.rows (keep i) (residual rd) a (fun d => qs.getD d []) (n-1) (n-cut)

def sparse (i : Input) (a : i.certified.Atom) (cut : Nat) := sparseWith (edges i a) a cut

private theorem sparseWith_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (rd : Edges i) (a : i.certified.Atom) (cut : Nat) :
    sparseWith rd a cut = RingSparseRefusalStore.compact (keep i) (RingSphereStore.rows i a (height i+1-cut)) ∧
      viewOf (sparseWith rd a cut) = viewOf (RingSphereStore.rows i a (height i+1-cut)) := by
  have materialized := (RingRootLayerStore.prefix_rows_eq i (RingPyramidalPublication.eligible i)
    (full rd) a cut).trans (full_rows ok rd a _ (by omega))
  rw [← materialized]
  exact RingSparseRefusalStore.exact_rows ..

/-- All retained addresses and every lookup match the public frozen table at each cut. -/
theorem sparse_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (cut : Nat) :
    sparse i a cut = RingSparseRefusalStore.compact (keep i) (RingSphereStore.rows i a (height i+1-cut)) ∧
      viewOf (sparse i a cut) = viewOf (RingSphereStore.rows i a (height i+1-cut)) :=
  sparseWith_exact ok _ a cut

def root (i : Input) (a : i.certified.Atom) : Cell :=
  let q := RingGroupedReport.origin i a
  if keep i q then
    match facts i q with
    | some result => result
    | none =>
      let rd := edges i a
      publish rd q (reader a (viewOf (sparseWith rd a 0)))
  else some none

theorem root_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) : root i a = RingChemicalGraphProof.root i a := by
  let rd := edges i a
  change full rd (RingGroupedReport.origin i a) (reader a (viewOf (sparseWith rd a 0))) = _
  rw [(sparseWith_exact ok rd a 0).2]
  change full rd _ (RingGlobalComparison.prior i a (height i+1)) = _
  have call : RingGlobalComparison.Called i a (height i+1) (RingGroupedReport.origin i a) := Or.inr ⟨rfl,rfl⟩
  rw [RingGlobalComparison.prior_exact call,full_frozen ok,← RingChemicalGraphProof.state_eq]
  exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a).symm

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (root i a).map fun labels => (a.val,labels)

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  simp only [report,root_exact ok]
  rfl

end TetraStereo.Engine.RingSparseFoldedReport
assert_kernel_only TetraStereo.Engine.RingSparseFoldedReport.sparse_exact
assert_kernel_only TetraStereo.Engine.RingSparseFoldedReport.root_exact
assert_kernel_only TetraStereo.Engine.RingSparseFoldedReport.raw_exact
