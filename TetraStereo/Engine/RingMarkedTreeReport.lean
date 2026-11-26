import TetraStereo.Engine.RingMarkedTreeOrder
import TetraStereo.Engine.RingOrdinaryLigandInventory
import TetraStereo.Engine.RingNumericPairReport

/-! Reports reconstructed from ordinary signed inventories and unordered marked trees.
The equivalence is on ready reachable stores; frame, atom and coordinate failures
are retained by the surrounding native physical interface. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedTreeReport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame)
open RingActiveDistanceSchedule (View Rule)
open RingActivePairReport (Slot)
open RingRetainedChemicalTrace (Word)
open RingStereoSiblingPass (Branch)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open RingPyramidalPublication (Ligand)
open RingConstitutionalResidual (publications)
open RingUniversalLigandOrder (Observation interpret observe)
open private ligand_read from TetraStereo.Engine.RingPyramidalNumericRows

/-- The complete bounded native tree is decoded directly; no marked evaluator
is consulted to supply a successful result. -/
def word? (i : Input) (r : Reader i) (atom : Nat) (q : Arm i) : Option Word :=
  let n := i.certified.localizedRerootCursorBudget q + 1
  (RingMarkedTreeOrder.reconstruct n (RingMarkedTreeFold.view i r atom n q)).map Branch.word

theorem word_exact {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (atom : Nat) (q : Arm i)
    (valid : RingRule5Shape.Valid q) (on : RingRule5Shape.On f q) :
    word? i r atom q = (RingGroupedMark.arm? i r atom q).map (fun e => e.2.word) := by
  dsimp only [word?]
  rw [RingMarkedTreeOrder.reconstruct_arm ready _ q atom valid on (Nat.lt_succ_self _)]
  simp only [Option.map_map,Function.comp_def]

def optionalWord? (i : Input) (r : Reader i) (mark : Option Nat) (q : Arm i) : Option Word :=
  match mark with
  | none => some []
  | some atom => word? i r atom q

theorem optionalWord_exact {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (mark : Option Nat) (q : Arm i)
    (valid : RingRule5Shape.Valid q) (on : RingRule5Shape.On f q) :
    optionalWord? i r mark q = RingFrameTransport.markWord? i r mark q := by
  cases mark with
  | none => rfl
  | some atom => exact word_exact ready atom q valid on

/-- Every ordinary slot is assembled from its root type and signed inventory. -/
def keys? {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) :=
  RingActivePairReport.four? fun k => RingOrdinaryLigandInventory.key? i r rev (RingGroupedCentre.cursor fr k)

theorem keys_exact {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) :
    keys? fr r rev = RingFullPathPublication.keys? fr r rev := by
  simp only [keys?,RingFullPathPublication.keys?,RingOrdinaryLigandInventory.key_exact]

def markWords? {i f} (fr : @Frame i f) (r : Reader i) : Option Slot → Option (Slot → Word)
  | none => some (fun _ => [])
  | some s => RingActivePairReport.four? fun k => word? i r (RingGroupedTrials.atom fr s) (RingGroupedCentre.cursor fr k)

theorem markWords_exact {i f} (fr : @Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (s : Option Slot) :
    markWords? fr r s = RingFullPathTrialReadings.markWords? fr r s := by
  cases s with
  | none => rfl
  | some s =>
    obtain ⟨ws,got,only⟩ := RingFullPathTrialReadings.mark_exact fr ready false (some s)
    have src := (only ws).mpr rfl
    have each (k : Slot) : word? i r (RingGroupedTrials.atom fr s) (RingGroupedCentre.cursor fr k) = some (ws k) := by
      obtain ⟨b,hb,eqn⟩ := src k
      dsimp only [word?]
      rw [RingMarkedTreeOrder.reconstruct_reading ready _ (RingGroupedCentre.valid fr k)
        (fr.direction k).property.1 (Nat.lt_succ_self _) hb]
      simp only [Option.map_some,← eqn]
    rw [got]
    simp only [markWords?,RingActivePairReport.four?,each,bind,pure,Option.bind_some ]
    congr 1
    funext k
    fin_cases k <;> rfl

def tetraData {i f} (fr : @Frame i f) (r : Reader i) (x y : Slot → Key) : RingPairwisePublication.Data where
  ordinary rev := RingPairwisePublication.ordinary (if rev then y else x)
  marked rev s := (markWords? fr r s).map fun ws =>
    RingPairwisePublication.directions (fun k => trialKey ((if rev then y else x) k) (ws k))

def tetraData? {i f} (fr : @Frame i f) (r : Reader i) : Option RingPairwisePublication.Data := do
  let x ← keys? fr r false
  let y ← keys? fr r true
  return tetraData fr r x y

theorem tetra_exact {i f} (fr : @Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) : tetraData? fr r = RingPairwisePublication.nativeData? fr r := by
  have marks : markWords? fr r = RingFullPathTrialReadings.markWords? fr r :=
    funext (markWords_exact fr ready)
  simp only [tetraData?,keys_exact,RingPairwisePublication.nativeData?,tetraData,
    RingPairwisePublication.nativeData,marks]

def ligands? (i : Input) (q : Site i) (r : View i) (rev : Bool) :=
  (RingRetainedAuxiliary.frame i.certified q).mapM fun arm => do
    let atom ← arm.occurrence.val.node.current?
    let key ← RingOrdinaryLigandInventory.key? i r rev arm
    return (⟨arm,atom.val,key⟩ : Ligand i)

theorem ligands_exact (i : Input) (q : Site i) (r : View i) (rev : Bool) :
    ligands? i q r rev = RingPyramidalPublication.ligands? i q r rev := by
  simp only [ligands?,RingPyramidalPublication.ligands?,RingOrdinaryLigandInventory.key_exact]

def rowOf (i : Input) (r : View i) (mark : Option Nat) (x : Ligand i) :=
  (optionalWord? i r mark x.arm).map fun w => (x.atom,trialKey x.priority w)

private theorem mapM_congr_on {α β : Type} (xs : List α) (f g : α → Option β)
    (same : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,same x List.mem_cons_self,
      ih (fun y hy => same y (List.mem_cons_of_mem _ hy))]

def pyramidalData (i : Input) (q : Site i) (r : View i) : RingPyramidalPairwise.Data where
  shape := decide ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  ordinary rev := (ligands? i q r rev).map
    (RingPyramidalPairwise.extractRow (fun x => x.atom) (fun x => trialKey x.priority []))
  marked rev mark := do
    let xs ← ligands? i q r rev
    let rows ← xs.mapM (rowOf i r mark)
    return RingPyramidalPairwise.extractRow Prod.fst Prod.snd rows

theorem pyramidal_exact (i : Input) (q : Site i) (r : View i)
    (ready : RingGroupedStereo.Ready q r) : pyramidalData i q r = RingPyramidalPairwise.nativeData i q r := by
  unfold pyramidalData RingPyramidalPairwise.nativeData
  simp only [ligands_exact]
  congr 1
  funext rev mark
  cases got : RingPyramidalPublication.ligands? i q r rev with
  | none => rfl
  | some xs =>
    simp only [bind,pure,Option.bind_some]
    have same : xs.mapM (rowOf i r mark) = xs.mapM (RingFrameTransport.rowOf i r mark) := by
      apply mapM_congr_on
      intro x hx
      obtain ⟨valid,on,_⟩ := ligand_read got hx
      simp only [rowOf,RingFrameTransport.rowOf,optionalWord_exact ready mark x.arm valid on]
      cases RingFrameTransport.markWord? i r mark x.arm <;> rfl
    rw [same]

def observations (i : Input) (q : Site i) (r : View i) : Observation i q :=
  match RingPyramidalPublication.focusP i q with
  | some a => .pyramidal a (pyramidalData i q r)
  | none => .tetra (match RingNestedActivePair.frame? i q with
    | none => some none
    | some fr => (tetraData? fr r).map fun d => some (fr,d))

theorem observations_exact {i : Input} {q : Site i} {r : View i}
    (ready : RingGroupedStereo.Ready q r) : observations i q r = observe i q r := by
  unfold observations observe
  cases p : RingPyramidalPublication.focusP i q with
  | some a => rw [pyramidal_exact i q r ready]
  | none =>
    unfold RingPairwisePublication.extract?
    cases fr : RingNestedActivePair.frame? i q with
    | none => rfl
    | some frame => simp only [tetra_exact frame ready]

def procedure (i : Input) : Rule i := fun q r => interpret (observations i q r)
abbrev rows (i : Input) := RingGlobalComparison.rows (publications i) (procedure i)
abbrev report (i : Input) := RingGlobalComparison.report (publications i) (procedure i)

theorem stores_and_reports {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    (∀ a k, k ≤ RingActiveDistanceSchedule.height i + 1 → rows i a k = RingSphereStore.rows i a k) ∧
      ∀ atoms, report i atoms = RingChemicalReport.report? i atoms := by
  have no (a k q) : ¬ RingGlobalComparison.Difference (publications i) (procedure i) a k q := by
    intro d
    apply d.2.2.2
    change interpret (observations i q (RingGlobalComparison.prior i a k)) = _
    rw [RingGlobalComparison.prior_exact d.1,observations_exact (RingChemicalGraphProof.ready ok q)]
    exact (RingUniversalLigandOrder.interface i ok).reachable q
  constructor
  · intro a k bound
    exact (RingGlobalComparison.rows_or_difference (publications i) (procedure i) a k bound).resolve_right
      (by rintro ⟨n,_,q,d⟩; exact no a n q d)
  · intro atoms
    by_contra bad
    obtain ⟨a,_,k,_,q,d⟩ := RingGlobalComparison.report_disagreement (publications i) (procedure i) atoms bad
    exact no a k q d

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  exact (stores_and_reports ok).2 atoms

end TetraStereo.Engine.RingMarkedTreeReport
assert_kernel_only TetraStereo.Engine.RingMarkedTreeReport.word_exact
assert_kernel_only TetraStereo.Engine.RingMarkedTreeReport.tetra_exact
assert_kernel_only TetraStereo.Engine.RingMarkedTreeReport.pyramidal_exact
assert_kernel_only TetraStereo.Engine.RingMarkedTreeReport.stores_and_reports
assert_kernel_only TetraStereo.Engine.RingMarkedTreeReport.raw_exact
