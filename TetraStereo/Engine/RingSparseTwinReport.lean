import TetraStereo.Engine.RingRootTwinDecision
import TetraStereo.Engine.RingPyramidalPathDecision
import TetraStereo.Engine.RingRootLayerStore
import TetraStereo.Engine.RingSparseRefusalStore
import TetraStereo.Engine.RingConstitutionalResidual




set_option autoImplicit false
namespace TetraStereo.Engine.RingSparseTwinReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View Rule height frozen)
open RingPyramidalPublication (publish eligible)
open RingSphereQueue (stored viewOf reader)
open RingConstitutionalResidual (publications)

def keep (i : Input) (q : Site i) : Bool :=
  decide (RingRootTwinDecision.direct i q ≠ some (some none))

/-- Consult the directly decided molecular frames before running the recursive rules. -/
def facts (i : Input) (q : Site i) : Option Cell :=
  (RingResidualPriority.graphCell? i q).orElse fun _ =>
    ((RingPyramidalPathDecision.direct? i q).map some).orElse fun _ =>
      (RingSecondShellDecision.direct? i q).map fun labels => some (some labels)

private theorem facts_sound {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) {cell : Cell} (hit : facts i q = some cell) :
    cell = RingChemicalGraphProof.state i q := by
  unfold facts at hit
  cases g : RingResidualPriority.graphCell? i q with
  | some v =>
    have eq : v = cell := by simpa [g] using hit
    exact eq ▸ RingResidualPriority.graphCell_sound i ok q v g
  | none =>
    cases p : RingPyramidalPathDecision.direct? i q with
    | some v =>
      have eq : some v = cell := by simpa [g,p] using hit
      exact eq ▸ (RingPyramidalPathDecision.sound ok p).symm
    | none =>
      cases d : RingSecondShellDecision.direct? i q with
      | none => simp [g,p,d] at hit
      | some labs =>
        have eq : some (some labs) = cell := by simpa [g,p,d] using hit
        exact eq ▸ (RingSecondShellDecision.direct_sound ok q d).symm

def residual (i : Input) : Rule i := RingResidualPriority.splice (facts i) (publish i)

abbrev full (i : Input) := RingSparseRefusalStore.guarded (keep i) (residual i)

private theorem on_frozen {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) : full i q (frozen (RingChemicalGraphProof.state i) q) =
      publish i q (frozen (RingChemicalGraphProof.state i) q) := by
  rw [← RingChemicalGraphProof.state_eq]
  unfold full RingSparseRefusalStore.guarded keep
  by_cases twins : RingRootTwinDecision.direct i q = some (some none)
  · simpa [twins] using (RingRootTwinDecision.sound i q ok _ twins).symm
  · rw [if_pos (decide_eq_true twins)]
    unfold residual RingResidualPriority.splice
    cases g : facts i q with
    | none => exact (RingChemicalGraphProof.state_eq i q).symm
    | some cell => exact facts_sound ok q g

private theorem full_rows {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) :
    stored (full i) a (RingGlobalComparison.queue i a) (height i) k = RingSphereStore.rows i a k := by
  apply (RingGlobalComparison.rows_or_difference (publications i) (full i) a k bound).resolve_right
  rintro ⟨n,_,q,d⟩
  apply d.2.2.1
  change full i q (RingGlobalComparison.prior i a n) = _
  rw [RingGlobalComparison.prior_exact d.1]
  exact on_frozen ok q

abbrev layers (i : Input) (a : i.certified.Atom) :=
  RingRootLayerStore.collect (eligible i) i.certified.certified.input.molecule.atomCount (RingGraphCache.sphere i a 0)

def sparse (i : Input) (a : i.certified.Atom) (cut : Nat) :=
  let n := i.certified.certified.input.molecule.atomCount
  let qs := layers i a
  RingSparseRefusalStore.rows (keep i) (residual i) a (fun d => qs.getD d []) (n-1) (n-cut)

private theorem materialized {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (cut : Nat) :
    stored (full i) a (fun d => (layers i a).getD d [])
      (i.certified.certified.input.molecule.atomCount-1) (i.certified.certified.input.molecule.atomCount-cut) =
      RingSphereStore.rows i a (height i+1-cut) :=
  (RingRootLayerStore.prefix_rows_eq i (eligible i) (full i) a cut).trans (full_rows ok a _ (by omega))

/-- The public row list with exactly the certified refusal addresses removed.
Every lookup, including the outer failure value, agrees at every cut. -/
theorem sparse_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (cut : Nat) :
    sparse i a cut = RingSparseRefusalStore.compact (keep i) (RingSphereStore.rows i a (height i+1-cut)) ∧
      viewOf (sparse i a cut) = viewOf (RingSphereStore.rows i a (height i+1-cut)) := by
  rw [← materialized ok a cut]
  exact RingSparseRefusalStore.exact_rows ..

/-- If every retained row of a batch prefix is decided without reading the
store, changing those decisions and rerunning all batches gives exactly the
pointwise change of the original list. The change may depend on the path. -/
private theorem rerun_direct_rows {i : Input} (change : Site i → Cell → Cell)
    (a : i.certified.Atom) (queue : Nat → List (Site i)) (top k : Nat)
    (direct : ∀ row ∈ stored (residual i) a queue top k, facts i row.1 = some row.2) :
    stored (fun q r => change q (residual i q r)) a queue top k =
      (stored (residual i) a queue top k).map (fun row => (row.1,change row.1 row.2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let old := stored (residual i) a queue top k
    let new := stored (fun q r => change q (residual i q r)) a queue top k
    have prior := ih (fun row member => direct row (List.mem_append_right _ member))
    simp only [stored,List.map_append,List.map_map] at ⊢
    apply congrArg₂ List.append _ prior
    apply List.map_congr_left
    intro q queued
    let cell := residual i q (reader a (viewOf old))
    have hit : facts i q = some cell :=
      direct (q,cell) (List.mem_append_left _ (List.mem_map.mpr ⟨q,queued,rfl⟩))
    have same : residual i q (reader a (viewOf new)) = cell :=
      RingResidualPriority.splice_direct (facts i) (publish i) q cell hit _
    exact congrArg (fun v => (q,change q v)) same





theorem sparse_rerun_of_facts {i : Input} (change : Site i → Cell → Cell)
    (a : i.certified.Atom) (cut : Nat)
    (direct : ∀ row ∈ sparse i a cut, facts i row.1 = some row.2) :
    RingSparseRefusalStore.rows (keep i) (fun q r => change q (residual i q r)) a
        (fun d => (layers i a).getD d []) (i.molecule.atomCount - 1) (i.molecule.atomCount - cut) =
      (sparse i a cut).map (fun row => (row.1,change row.1 row.2)) := by
  have count := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  rw [← count]
  exact rerun_direct_rows change a _ _ _ direct

private def addresses {α : Type} (queue : Nat → List α) (top : Nat) : Nat → List α
  | 0 => []
  | k+1 => queue (top-k) ++ addresses queue top k

private theorem stored_addresses {i : Input} (rule : Rule i) (a : i.certified.Atom)
    (queue : Nat → List (Site i)) (top k : Nat) :
    (stored rule a queue top k).map Prod.fst = addresses queue top k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [stored,addresses,ih,List.map_map,Function.comp_def]


def audit (i : Input) (a : i.certified.Atom) (cut : Nat) :=
  let qs := layers i a
  let n := i.certified.certified.input.molecule.atomCount
  let queue := fun d => qs.getD d []
  let small := RingSparseRefusalStore.rows (keep i) (residual i) a queue (n-1) (n-cut)
  (addresses queue (n-1) (n-cut)).map fun q => (q,viewOf small q)

theorem audit_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (cut : Nat) : audit i a cut = RingSphereStore.rows i a (height i+1-cut) := by
  rw [← materialized ok a cut]
  unfold audit
  dsimp only
  rw [← stored_addresses (full i) a]
  apply RingSparseRefusalStore.restore
  rw [materialized ok a cut]
  exact RingSphereStore.chemical_stored_keys_nodup i a _ (by omega)

def root (i : Input) (a : i.certified.Atom) : Cell :=
  let q := RingGroupedReport.origin i a
  if keep i q then
    match facts i q with
    | some result => result
    | none => publish i q (reader a (viewOf (sparse i a 0)))
  else some none

theorem root_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) : root i a = RingChemicalGraphProof.root i a := by
  have expanded : root i a = full i (RingGroupedReport.origin i a)
      (reader a (viewOf (sparse i a 0))) := by
    unfold root full RingSparseRefusalStore.guarded residual RingResidualPriority.splice
    rfl
  rw [expanded]
  rw [(sparse_exact ok a 0).2]
  change full i _ (RingGlobalComparison.prior i a (height i+1)) = _
  have called : RingGlobalComparison.Called i a (height i+1) (RingGroupedReport.origin i a) := Or.inr ⟨rfl,rfl⟩
  rw [RingGlobalComparison.prior_exact called,on_frozen ok,← RingChemicalGraphProof.state_eq]
  exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a).symm

def fastRoot (i : Input) (a : i.certified.Atom) : Cell :=
  match RingPyramidalTwoShell.rootDecision? i a with
  | some v => some v
  | none => root i a

theorem fastRoot_exact {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) : fastRoot i a = RingChemicalGraphProof.root i a := by
  unfold fastRoot
  cases h : RingPyramidalTwoShell.rootDecision? i a with
  | some v => exact (RingPyramidalTwoShell.rootDecision_sound ok a h).symm
  | none => exact root_exact ok a

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (fastRoot i a).map fun x => (a.val,x)

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  simp only [report,fastRoot_exact ok]
  rfl

end TetraStereo.Engine.RingSparseTwinReport
assert_kernel_only TetraStereo.Engine.RingSparseTwinReport.sparse_exact
assert_kernel_only TetraStereo.Engine.RingSparseTwinReport.audit_exact
assert_kernel_only TetraStereo.Engine.RingSparseTwinReport.raw_exact
assert_kernel_only TetraStereo.Engine.RingSparseTwinReport.sparse_rerun_of_facts
