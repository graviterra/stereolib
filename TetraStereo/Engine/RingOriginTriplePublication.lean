import TetraStereo.Engine.RingOriginTripleFrame
import TetraStereo.Engine.RingOriginTripleTrials
import TetraStereo.Engine.RingTerminalTwinRefusal

/-! A single nomination cannot split three exchangeable terminal neighbors
into a strict ordering on any ready occurrence store. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTriplePublication
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)

theorem refusal {i : Input} {f : Site i} (fr : Frame i f)
    (hf : RingNestedActivePair.frame? i f = some fr) (hp : RingPyramidalPublication.focusP i f = none)
    (t : RingOriginTripleFrame.Triple fr) (read : Reader i) (ready : RingGroupedStereo.Ready f read) :
    RingOriginMetricReport.publish i f read = some none := by
  obtain ⟨center,offU,offV⟩ := t.base_facts
  have recognized := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f fr.center).mp fr.recognized
  have current : f.val.node.current? = some t.basePair.c.val := center.symm ▸ recognized.2
  have early := RingOriginTwinFrame.early_none t.basePair f recognized.1 current offU offV
  exact RingOriginTripleTrials.publish_refusal fr hp early hf ready (t.ties read ready)

def check (i : Input) (f : Site i) : Bool :=
  (RingPyramidalPublication.focusP i f).isNone &&
    (RingNestedActivePair.frame? i f).any RingOriginTripleFrame.check

theorem exact_cell {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (hit : check i f = true) (read : Reader i) (ready : RingGroupedStereo.Ready f read) :
    RingOriginMetricReport.publish i f read = some none ∧ RingChemicalGraphProof.state i f = some none := by
  obtain ⟨hp,h⟩ := Bool.and_eq_true_iff.mp hit
  have tetra := Option.isNone_iff_eq_none.mp hp
  cases hf : RingNestedActivePair.frame? i f with
  | none => simp [hf] at h
  | some fr =>
    obtain ⟨t⟩ := RingOriginTripleFrame.check_sound fr (by simpa [hf] using h)
    obtain ⟨center,offU,offV⟩ := t.base_facts
    have facts := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff f fr.center).mp fr.recognized
    exact ⟨refusal fr hf tetra t read ready,
      t.basePair.occurrence_refusal geom f offU offV facts.1 (center.symm ▸ facts.2)⟩

end TetraStereo.Engine.RingOriginTriplePublication
assert_kernel_only TetraStereo.Engine.RingOriginTriplePublication.refusal
assert_kernel_only TetraStereo.Engine.RingOriginTriplePublication.exact_cell
