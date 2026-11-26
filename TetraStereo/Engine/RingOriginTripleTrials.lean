import TetraStereo.Engine.RingOriginMetricReport
import TetraStereo.Engine.RingOriginMetricTotal

/-! A tie in every actual marking trial gives a completed tetrahedral refusal.
All comparison and marking coverage is derived from the ready molecular reader. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTripleTrials
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot four?)
open RingOriginTetrahedralTrials (keysWith wordsWith centreWith dataWith data)
open RingOriginMetricReport (marks)
open RingOriginFullKeys (active)
open RingPairwisePublication (Data ballot directions trials)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key)

private theorem collect {A B : Type} (xs : List A) (fn : A → Option B) (v : A → B)
    (full : ∀ a ∈ xs, fn a = some (v a)) : xs.mapM fn = some (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.mapM_cons,List.map_cons]
    rw [full a List.mem_cons_self,ih (fun b hb => full b (List.mem_cons_of_mem a hb))]
    rfl

theorem keys_total {i : Input} {f : Site i} {r : Reader i} (fr : Frame i f)
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) :
    ∃ ks, keysWith fr (active i f r) rev = some ks := by
  apply Option.isSome_iff_exists.mp
  apply RingActivePairReport.four_full
  intro s
  exact Option.isSome_iff_exists.mpr (RingOriginMetricTotal.active_total ready rev
    (RingGroupedCentre.cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1)

theorem words_total {i : Input} {f : Site i} {r : Reader i} (fr : Frame i f)
    (ready : RingGroupedStereo.Ready f r) (m : Option Slot) :
    ∃ ws, wordsWith fr (marks i f r) m = some ws := by
  cases m with
  | none => exact ⟨fun _ => [],rfl⟩
  | some s =>
    simp only [wordsWith,marks]
    apply Option.isSome_iff_exists.mp
    apply RingActivePairReport.four_full
    intro k
    exact Option.isSome_iff_exists.mpr (RingOriginMetricTotal.mark_total ready
      (RingGroupedTrials.atom fr s) (RingGroupedCentre.cursor fr k)
      (RingGroupedCentre.valid fr k) (fr.direction k).property.1)

/-- Each nomination may use a different residual pair, as happens with three
identical terminal ligands. No aggregate, handedness or coverage premise occurs. -/
def Ties {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Prop :=
  ∀ m : Option Slot, ∃ u v : Slot, u ≠ v ∧
    active i f r false (RingGroupedCentre.cursor fr u) =
      active i f r false (RingGroupedCentre.cursor fr v) ∧
    (wordsWith fr (marks i f r) m).map (fun ws => ws u) =
      (wordsWith fr (marks i f r) m).map (fun ws => ws v)

/-- Ties refuse every ballot, for any number of actual nominations. -/
theorem centre_refusal {i : Input} {f : Site i} {r : Reader i} (fr : Frame i f)
    (ready : RingGroupedStereo.Ready f r) (ties : Ties fr r) :
    centreWith fr (active i f r) (marks i f r) = some none := by
  obtain ⟨x,hx⟩ := keys_total fr ready false
  obtain ⟨y,hy⟩ := keys_total fr ready true
  let d := data x y (wordsWith fr (marks i f r))
  have absent (m : Option Slot) :
      (do
        let comparison ← d.marked false m
        pure (m,ballot comparison (fun row => readback?
          (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (fr.atoms row)))) = some (m,none) := by
    obtain ⟨ws,hw⟩ := words_total fr ready m
    obtain ⟨u,v,ne,hk,hm⟩ := ties m
    have xu := RingActivePairReport.four_at hx u
    have xv := RingActivePairReport.four_at hx v
    change active i f r false (RingGroupedCentre.cursor fr u) = some (x u) at xu
    change active i f r false (RingGroupedCentre.cursor fr v) = some (x v) at xv
    have keys : x u = x v := Option.some.inj (xu.symm.trans (hk.trans xv))
    rw [hw] at hm
    have words : ws u = ws v := Option.some.inj hm
    have equal : RingFullPathTrialReadings.trialKey (x u) (ws u) =
        RingFullPathTrialReadings.trialKey (x v) (ws v) := by rw [keys,words]
    have tie : RingPairwisePublication.tied
        (directions (fun k => RingFullPathTrialReadings.trialKey (x k) (ws k))) u v = true := by
      rw [RingPairwisePublication.tied_directions,equal]
      simp
    have no := RingPairwisePublication.ballot_tied _
      (fun row => readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (fr.atoms row)) u v ne tie
    change ((wordsWith fr (marks i f r) m).map _).bind _ = _
    rw [hw]
    simp only [Option.map_some,Option.bind_some,Bool.false_eq_true,ite_false]
    rw [no]
    rfl
  have ballots : d.ballots (fun _ row => readback?
      (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (fr.atoms row)) =
      some ((trials (d.ordinary false)).map fun m => (m,none)) := by
    exact collect _ _ _ (fun m _ => absent m)
  unfold centreWith dataWith
  rw [hx,hy]
  change d.publish _ = _
  unfold Data.publish
  rw [ballots]
  simp [Data.letters,List.map_map,Function.comp_def,
    LocalizedChemicalRingPromotionAggregation.readingBalance,
    LocalizedChemicalRingPromotionAggregation.readingScore,
    RingChemicalPriority.ReferenceFrame.survivingHand]

/-- The complete active-origin publisher refuses after the actual tetrahedral
and early-exit branches have selected this frame. -/
theorem publish_refusal {i : Input} {f : Site i} {r : Reader i} (fr : Frame i f)
    (hp : RingPyramidalPublication.focusP i f = none)
    (early : RingOriginPriorityStore.early? i f = none)
    (frame : RingNestedActivePair.frame? i f = some fr)
    (ready : RingGroupedStereo.Ready f r) (ties : Ties fr r) :
    RingOriginMetricReport.publish i f r = some none := by
  simp only [RingOriginMetricReport.publish,hp,early,
    RingOriginTetrahedralTrials.publishWith,frame]
  exact centre_refusal fr ready ties

assert_kernel_only keys_total
assert_kernel_only words_total
assert_kernel_only centre_refusal
assert_kernel_only publish_refusal
end TetraStereo.Engine.RingOriginTripleTrials
