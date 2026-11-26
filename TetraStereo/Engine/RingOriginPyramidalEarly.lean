import TetraStereo.Engine.RingSingleCycleComparison
import TetraStereo.Engine.RingPyramidalEarly
import TetraStereo.Engine.RingOriginPyramidalTrials

/-! Rebuild the three constitutional ligand trees at the active pyramidal focus.
The optional decision retains both constitutional ties and flat physical reads. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginPyramidalEarly
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingPyramidalSource (Directions slots atomId)
open RingSingleCycleComparison (CommonOrigin rebuilt)
open RingRetainedChemicalPreorder (Direction keyFor orderWord)
open RingPyramidalPairwise (extractRow)
open private extract_strict extract_order from TetraStereo.Engine.RingPyramidalPairwise
open private wordlist_lt from TetraStereo.Engine.RingDuplicateScale
attribute [local instance] lexOrd

private def direction {i : Input} {q : Site i} (d : Directions i q) (s : Fin 3) : Direction i q :=
  ⟨(d.arm s).occurrence, (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mp (by
    have h := d.valid s
    have prev := i.certified.executableLocalizedRerootChildren_previous
      (⟨q,none⟩ : RingActivePairs.Arm i) (d.arm s) (d.mem s)
    simpa only [CertifiedLocalizedCIPInput.LocalizedRerootCursorValid,prev] using h) |>.2⟩

private theorem arm_eq {i : Input} {q : Site i} (d : Directions i q) (s : Fin 3) :
    d.arm s = ⟨(direction d s).val,some q⟩ := by
  have prev := i.certified.executableLocalizedRerootChildren_previous
    (⟨q,none⟩ : RingActivePairs.Arm i) (d.arm s) (d.mem s)
  cases h : d.arm s
  simp_all [direction]

private def word {i : Input} {q : Site i} (d : Directions i q) (s : Fin 3) :=
  ((rebuilt i q (d.arm s)).map orderWord).getD []

private theorem word_compare {i : Input} {q : Site i} (d : Directions i q)
    (common : CommonOrigin i q.val.root) (s t : Fin 3) :
    compare (word d s) (word d t) =
      compare (orderWord (keyFor (direction d s))) (orderWord (keyFor (direction d t))) := by
  have eqn := (RingSingleCycleComparison.of_common_origin q common (direction d s) (direction d t)).trans
    (RingRetainedChemicalPreorder.table_order _ _)
  rw [← arm_eq d s,← arm_eq d t] at eqn
  cases hs : rebuilt i q (d.arm s) <;> cases ht : rebuilt i q (d.arm t) <;>
    simp [hs,ht,word,RingRetainedChemicalPreorder.compare_word] at eqn ⊢
  exact eqn

/-- A strict rebuilt constitutional row is read with the phantom last.
A tie misses the early test; a flat frame completes it with no labels. -/
def early? (i : Input) (q : Site i) : Option (Option RingNestedActivePair.Labels) := do
  let a ← RingPyramidalPublication.focusP i q
  let d ← RingPyramidalEarly.directions? i q
  let row := extractRow (atomId d) (word d) slots
  if row.strict then
    return (row.read (LocalizedGenericMarkedRecalculation.readback?
      (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)) a.val).map
        fun h => (.chiral h,.chiral h.swap)
  else none

/-- Exact equality includes an early miss on ties and `some none` on flat reads. -/
theorem early_exact {i : Input} (q : Site i) (common : CommonOrigin i q.val.root) :
    early? i q = RingPyramidalEarly.early? i q := by
  unfold early? RingPyramidalEarly.early?
  apply congrArg (fun next => (RingPyramidalPublication.focusP i q).bind next)
  funext a
  apply congrArg (fun next => (RingPyramidalEarly.directions? i q).bind next)
  funext d
  let cs := fun s => keyFor (direction d s)
  have native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s) := by
    intro s
    rw [arm_eq d s]
    exact RingRetainedChemicalPreorder.read_key _
  rw [RingPyramidalEarly.keys_of d cs native]
  have rows : extractRow (atomId d) (word d) slots =
      extractRow (atomId d) (fun s => orderWord (cs s)) slots := by
    apply RingOriginPyramidalTrials.extract_congr
    intro s _ t _
    have same := congrArg (fun o => o = Ordering.lt) (word_compare d common s t)
    exact (wordlist_lt _ _).symm.trans ((iff_of_eq same).trans (wordlist_lt _ _))
  rw [rows]
  simp only [bind,Option.bind_some]
  have strict := extract_strict (atomId d) (fun s => orderWord (cs s)) slots
  change (extractRow (atomId d) (fun s => orderWord (cs s)) slots).strict ↔
    [orderWord (cs 0),orderWord (cs 1),orderWord (cs 2)].Nodup at strict
  by_cases nd : [orderWord (cs 0),orderWord (cs 1),orderWord (cs 2)].Nodup
  · simp only [if_pos nd,if_pos (strict.mpr nd),RingPyramidalPairwise.Row.read,
      extract_order,pure]
  · simp only [if_neg nd,if_neg (mt strict.mp nd)]

theorem early_local {i : Input} {q : Site i} (common : CommonOrigin i q.val.root)
    {r : RingNestedActivePair.Reader i} (ready : RingGroupedStereo.Ready q r)
    {v : Option RingNestedActivePair.Labels} (hit : early? i q = some v) :
    RingPyramidalPublication.publish i q r = some v :=
  RingPyramidalEarly.early_local ready ((early_exact q common) ▸ hit)

theorem early_state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} (common : CommonOrigin i q.val.root)
    {v : Option RingNestedActivePair.Labels} (hit : early? i q = some v) :
    RingChemicalGraphProof.state i q = some v :=
  RingPyramidalEarly.early_state geom ((early_exact q common) ▸ hit)

end TetraStereo.Engine.RingOriginPyramidalEarly
assert_kernel_only TetraStereo.Engine.RingOriginPyramidalEarly.early_exact
assert_kernel_only TetraStereo.Engine.RingOriginPyramidalEarly.early_local
assert_kernel_only TetraStereo.Engine.RingOriginPyramidalEarly.early_state
