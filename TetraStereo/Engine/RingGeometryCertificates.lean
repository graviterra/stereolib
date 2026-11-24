import TetraStereo.Engine.RingGeometryCriterion
import TetraStereo.Engine.RingBranchMatching
import TetraStereo.Engine.RingMarkedIncidence

set_option autoImplicit false

namespace TetraStereo.Engine.RingGeometryCertificates
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Reader Frame Labels)
open RingActivePairReport (Slot)
open RingGroupedCentre (Arms)
open RingGeometryCriterion (Signature)
open RingActiveDistanceSchedule (frozen)
attribute [local instance] lexOrd

/-- All branch comparisons at the requested site share one geometric root
table. The caller supplies no auxiliary labels, trial outcomes or CIP letters. -/
structure Context (i : Input) (q : Site i) where
  coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true
  read : Reader i
  geometric : read = frozen (RingGeometryCriterion.rootState i q.val.root) q
  fr : Frame i q
  frame : RingNestedActivePair.frame? i q = some fr
  arms : Arms fr read
  profiles : RingGroupedCentre.arms? fr read = some arms

def prepare? (i : Input) (q : Site i) : Option (Context i q) := do
  if coords : LocalizedChemicalRing.coordinatesAdmitted i = true then
    let table := RingGeometryCriterion.rootTable i q.val.root
    let read := frozen (RingActiveDistanceSchedule.snapshot table) q
    let ⟨fr,hf⟩ ← (RingNestedActivePair.frame? i q).attach
    let ⟨a,ha⟩ ← (RingGroupedCentre.arms? fr read).attach
    return ⟨coords,read,rfl,fr,hf,a,ha⟩
  else none

private theorem Context.ready {i q} (c : Context i q) : RingGroupedStereo.Ready q c.read := by
  rw [c.geometric,RingGeometryCriterion.rootReader_exact c.coordinates]
  exact RingGroupedPublication.ready (RingGroupedGeometry.physical c.coordinates) q

private theorem Context.publication {i q} (c : Context i q) :
    RingGroupedPublication.state i q = some (Signature.mk
      (RingOrientation.baseline c.fr * RingOrientation.index c.arms) (RingGeometryCriterion.reversals c.arms)).letters := by
  obtain ⟨s,hs,pub,_⟩ := RingGeometryCriterion.at_centre c.coordinates q c.fr.recognized
  rw [RingGeometryCriterion.state_eq c.coordinates,← RingGeometryCriterion.rootReader_exact c.coordinates q,← c.geometric] at hs
  simp [RingGeometryCriterion.signature?,c.frame,c.profiles] at hs
  cases hs
  exact pub

/-- Every successful return carries a proof of the actual scheduled absence. -/
def Context.refusal? {i q} (c : Context i q) (propose : Slot → RingBranchMatching.Proposal) :
    Option (PLift (RingGroupedPublication.state i q = some none)) := do
  let ⟨r⟩ ← RingBranchMatching.certify? c.arms propose
  return ⟨by
    obtain ⟨m,_⟩ := Option.isSome_iff_exists.mp c.arms.matrix_total
    obtain ⟨d,_⟩ := Option.isSome_iff_exists.mp (RingGroupedTrials.decision_total c.arms m c.ready
      (RingGroupedGeometry.calibrated c.coordinates c.fr))
    have zero := (RingOrientation.refusal_iff d c.ready c.coordinates).mp (r.forces d c.ready c.coordinates)
    rw [c.publication,Option.some.injEq,Signature.refusal_iff]
    simp [zero]⟩

/-- Check first-sphere bond coupling and read the answer from the reference
frame. The returned pair of letters carries a proof for the complete schedule. -/
def Context.descriptor? {i q} (ctx : Context i q) (a b c d : Slot) :
    Option ((letters : Labels) × PLift (RingGroupedPublication.state i q = some (some letters))) := do
  let ⟨p,coupled⟩ ← RingMarkedIncidence.classify? ctx.arms a b c d
  let signature : Signature := ⟨RingOrientation.baseline ctx.fr * (p.sign * 4),RingGeometryCriterion.reversals ctx.arms⟩
  let ⟨v,hv⟩ ← signature.letters.attach
  return ⟨v,⟨by
    rw [ctx.publication,RingMarkedIncidence.coupled_index p ctx.ready coupled]
    exact congrArg some hv⟩⟩

end TetraStereo.Engine.RingGeometryCertificates
assert_kernel_only TetraStereo.Engine.RingGeometryCertificates.Context.refusal?
assert_kernel_only TetraStereo.Engine.RingGeometryCertificates.Context.descriptor?
