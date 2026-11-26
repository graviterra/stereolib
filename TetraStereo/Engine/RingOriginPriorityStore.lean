import TetraStereo.Engine.RingSingleCycleComparison
import TetraStereo.Engine.RingLigandTreeStore

/-! Recompute constitutional priorities at each tetrahedral early exit, and
run the resulting publisher on its own preceding sphere stores. Pyramidal
publication and the full stereochemical calculation on ties use the public rules. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginPriorityStore
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Rule height)
open RingSingleCycleComparison (CommonOrigin rebuilt)
open RingRetainedChemicalPreorder (Direction orderWord keyFor)
open private orientation_congr from TetraStereo.Engine.RingZeroMassReport
attribute [local instance] lexOrd

private def word {i : Input} {f : Site i} (a : Direction i f) :=
  ((rebuilt i f ⟨a.val,some f⟩).map orderWord).getD []

private theorem word_compare {i : Input} {f : Site i} (common : CommonOrigin i f.val.root)
    (a b : Direction i f) :
    compare (word a) (word b) = compare (orderWord (keyFor a)) (orderWord (keyFor b)) := by
  have eqn := (RingSingleCycleComparison.of_common_origin f common a b).trans
    (RingRetainedChemicalPreorder.table_order a b)
  cases ha : rebuilt i f ⟨a.val,some f⟩ <;> cases hb : rebuilt i f ⟨b.val,some f⟩ <;>
    simp [ha,hb,word,RingRetainedChemicalPreorder.compare_word] at eqn ⊢
  exact eqn

def early? (i : Input) (q : Site i) : Option RingGeometryCriterion.Signature := do
  let fr ← RingNestedActivePair.frame? i q
  let parity := RingOrientation.orientation fun j => word (fr.direction j)
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

theorem early_exact {i : Input} (q : Site i) (common : CommonOrigin i q.val.root) :
    early? i q = RingZeroMassReport.zeroEarly? i q := by
  rw [RingZeroMassReport.zero_early_exact]
  unfold early? RingSphereQueue.early?
  apply congrArg (fun next => (RingNestedActivePair.frame? i q).bind next)
  funext fr
  exact congrArg (fun parity : Int => if parity = 0 then none else
    some (⟨RingOrientation.baseline fr * parity,0⟩ : RingGeometryCriterion.Signature))
    (orientation_congr _ _ (fun j k => word_compare common (fr.direction j) (fr.direction k)))

def publish (i : Input) : Rule i := fun q read =>
  match RingPyramidalPublication.focusP i q with
  | some a => some (RingPyramidalPublication.pLabels i q read a)
  | none => match early? i q with
    | some s => some s.letters
    | none => RingFullPathPublication.publish? i q read

theorem publish_exact {i : Input} (q : Site i) (common : CommonOrigin i q.val.root)
    (read : RingActiveDistanceSchedule.View i) :
    publish i q read = RingPyramidalPublication.publish i q read := by
  cases hp : RingPyramidalPublication.focusP i q <;>
    cases he : RingZeroMassReport.zeroEarly? i q <;>
    simp [publish,RingPyramidalPublication.publish,RingFullPathConstitution.fastPublish,
      early_exact q common,hp,he]

def rows (i : Input) (r : i.certified.Atom) (batches : Nat) :=
  RingSphereQueue.stored (publish i) r (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) r)
    (height i) batches

/-- Equality of ordered address/value rows at every sphere boundary on this
root slice, even when the two runs read their own preceding stores. -/
theorem rows_exact {i : Input} (r : i.certified.Atom) (common : CommonOrigin i r)
    (batches : Nat) : rows i r batches = RingSphereStore.rows i r batches := by
  unfold rows RingSphereStore.rows
  induction batches with
  | zero => rfl
  | succ n ih =>
    simp only [RingSphereQueue.stored,ih]
    congr 1
    apply List.map_congr_left
    intro q mem
    have root := (((RingEligibleGraph.inventory i _ r) _ q).mp mem).1.1
    rw [publish_exact q (root.symm ▸ common)]

/-- Read the requested root against the completed independently generated store. -/
def root (i : Input) (r : i.certified.Atom) :=
  publish i (RingGroupedReport.origin i r)
    (RingSphereQueue.reader r (RingSphereQueue.viewOf (rows i r (height i + 1))))

theorem root_exact {i : Input} (r : i.certified.Atom) (common : CommonOrigin i r) :
    root i r = RingChemicalGraphProof.root i r := by
  unfold root
  rw [rows_exact r common,publish_exact _ common]
  unfold RingSphereStore.rows
  rw [RingSphereQueue.stored_eq]
  rfl

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun r => (root i r).map fun labels => (r.val,labels)

/-- Every requested root may have its own common origin. Repeated requests,
casing, refused descriptors and failed reads are preserved. -/
theorem report_exact {i : Input} (atoms : List i.certified.Atom)
    (common : ∀ r ∈ atoms, CommonOrigin i r) :
    report i atoms = RingChemicalReport.report? i atoms := by
  unfold report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r mem
  rw [root_exact r (common r mem)]
  rfl

end TetraStereo.Engine.RingOriginPriorityStore
assert_kernel_only TetraStereo.Engine.RingOriginPriorityStore.rows_exact
assert_kernel_only TetraStereo.Engine.RingOriginPriorityStore.report_exact
