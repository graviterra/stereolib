import TetraStereo.Engine.RingUnmarkedExchange
import TetraStereo.Engine.RingExchangeStore

/-! Discover persistent ties directly on the four retained ligand trees.
The public entry point needs no proposed atom permutation. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAutomaticRefusal
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingPyramidalPublication (focusP publish)

/-- The constitutional classes determine which matches can justify a refusal.
The sole-pair case needs one unmarked match. Three or four repeated slots may
lead to Rule 6 nominations. -/
def frameCheck {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Bool :=
  match RingUnmarkedExchange.repeated fr with
  | [u,v] => u != v && (RingObservedTreeMatch.unmarked? fr r u v).isSome
  | _ :: _ :: _ :: _ => RingObservedTreeMatch.check fr r
  | _ => false

theorem frame_refusal {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : focusP i f = none) (ready : RingGroupedStereo.Ready f r)
    (hit : frameCheck fr r = true) : publish i f r = some none := by
  unfold frameCheck at hit
  split at hit
  · rename_i u v pattern
    exact RingUnmarkedExchange.checked_publish fr geom tetra ready
      (by simpa only [RingUnmarkedExchange.check,pattern] using hit)
  · exact RingLigandExchange.publish_refusal fr geom tetra ready
      (RingObservedTreeMatch.check_sound fr r hit)
  · contradiction

def select {i : Input} : RingExchangeStore.Selector i := fun f read =>
  (focusP i f).isNone && (RingNestedActivePair.frame? i f).any (fun fr => frameCheck fr read)

theorem refuses {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingExchangeStore.Refuses (select (i := i)) := by
  intro f read hit
  obtain ⟨tetra,good⟩ := Bool.and_eq_true_iff.mp hit
  cases found : RingNestedActivePair.frame? i f with
  | none => simp [found] at good
  | some fr =>
    exact frame_refusal fr geom (Option.isNone_iff_eq_none.mp tetra)
      (RingChemicalGraphProof.ready geom f) (by simpa [found] using good)

/-- The automatically pruned evaluator computes the same rows in its own run. -/
theorem stores {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (k : Nat) (bound : k ≤ RingActiveDistanceSchedule.height i + 1) :
    RingStoreDecision.candidateRows (RingExchangeStore.rule select) r k = RingSphereStore.rows i r k :=
  RingExchangeStore.stores_of_refuses (refuses geom) r k bound

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun r => (RingExchangeStore.root select r).map fun labels => (r.val,labels)

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms geom
  unfold report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r _
  rw [RingExchangeStore.root_of_refuses (refuses geom) r]
  rfl

end TetraStereo.Engine.RingAutomaticRefusal
assert_kernel_only TetraStereo.Engine.RingAutomaticRefusal.frame_refusal
assert_kernel_only TetraStereo.Engine.RingAutomaticRefusal.stores
assert_kernel_only TetraStereo.Engine.RingAutomaticRefusal.raw_exact
