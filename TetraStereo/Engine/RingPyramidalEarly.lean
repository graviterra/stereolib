import TetraStereo.Engine.RingPyramidalConstitution

/-! Full-depth constitutional early decisions at selected neutral P/As centers.
A flat physical frame is an early completed refusal, not an early-test failure. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalEarly
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Reader Labels)
open RingPyramidalSource (Directions slots atomId)
open RingRetainedChemicalTrace (Key)
open RingRetainedChemicalPreorder (orderWord)
attribute [local instance] lexOrd
open private nodup_injective from TetraStereo.Engine.RingPyramidalSource

/-- Actual retained arms, including the incoming direction at auxiliary occurrences. -/
def directions? (i : Input) (q : Site i) : Option (Directions i q) :=
  match frameEq : RingRetainedAuxiliary.frame i.certified q with
  | [x,y,z] =>
    match hx : x.occurrence.val.node.current?, hy : y.occurrence.val.node.current?, hz : z.occurrence.val.node.current? with
    | some ax,some ay,some az => some {
        arm := ![x,y,z]
        atom := ![ax,ay,az]
        incident := frameEq
        real := by intro k; fin_cases k <;> first | exact hx | exact hy | exact hz }
    | _,_,_ => none
  | _ => none

theorem directions_of (i : Input) (q : Site i) (d : Directions i q) : directions? i q = some d := by
  have present : (directions? i q).isSome = true := by
    unfold directions?
    split
    · rename_i x y z frameEq
      have same := d.incident.symm.trans frameEq
      obtain ⟨hx,hy,hz⟩ := List.cons.inj same
      subst x
      split
      · rfl
      · rename_i impossible
        exact (impossible (d.atom 0) (d.atom 1) (d.atom 2) (d.real 0) (d.real 1) (d.real 2)).elim
    · rename_i impossible
      exact (impossible _ _ _ d.incident).elim
  obtain ⟨e,hit⟩ := Option.isSome_iff_exists.mp present
  exact hit.trans (congrArg some (Directions.unique e d))

def keys? {i : Input} {q : Site i} (d : Directions i q) : Option (Fin 3 → Key) := do
  let x ← RingRetainedChemicalTrace.key? i (d.arm 0)
  let y ← RingRetainedChemicalTrace.key? i (d.arm 1)
  let z ← RingRetainedChemicalTrace.key? i (d.arm 2)
  return ![x,y,z]

theorem keys_source {i : Input} {q : Site i} {d : Directions i q} {cs : Fin 3 → Key}
    (hit : keys? d = some cs) : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s) := by
  unfold keys? at hit
  cases hx : RingRetainedChemicalTrace.key? i (d.arm 0) <;>
  cases hy : RingRetainedChemicalTrace.key? i (d.arm 1) <;>
  cases hz : RingRetainedChemicalTrace.key? i (d.arm 2) <;> simp [hx,hy,hz] at hit
  subst cs
  intro s
  fin_cases s <;> assumption

theorem keys_of {i : Input} {q : Site i} (d : Directions i q) (cs : Fin 3 → Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s)) : keys? d = some cs := by
  simp only [keys?,native 0,native 1,native 2,Option.bind_some,bind,pure]
  congr 1
  funext s
  fin_cases s <;> rfl

/-- A hit contains a fully decided optional label pair; only a strict
constitutional order is read. No stereo suffix or promotion word is consulted. -/
def early? (i : Input) (q : Site i) : Option (Option Labels) := do
  let a ← RingPyramidalPublication.focusP i q
  let d ← directions? i q
  let cs ← keys? d
  let word := fun s => orderWord (cs s)
  if [word 0,word 1,word 2].Nodup then
    let row := RingStereoSiblingPass.order word slots
    return (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      (row.map (atomId d) ++ [a.val])).map fun h => (.chiral h,.chiral h.swap)
  else none

/-- Every hit equals the ordinary native local publication on any ready reader. -/
theorem early_local {i : Input}
    {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r) {v : Option Labels}
    (hit : early? i q = some v) : RingPyramidalPublication.publish i q r = some v := by
  simp only [early?,bind,Option.bind_eq_some_iff] at hit
  obtain ⟨a,selected,d,hd,cs,hcs,tail⟩ := hit
  have native := keys_source hcs
  split at tail
  · rename_i distinct
    have strict := (nodup_injective (fun s => orderWord (cs s))).mp distinct
    have legal := RingStereoSiblingPass.legal_order (fun s => orderWord (cs s)) slots
    have size : (RingStereoSiblingPass.order (fun s => orderWord (cs s)) slots).length = 3 := legal.perm.length_eq
    obtain ⟨j,k,l,row⟩ := List.length_eq_three.mp size
    have sorted : RingStereoSiblingPass.Legal (fun s => orderWord (cs s)) slots [j,k,l] := row ▸ legal
    have actual := RingPyramidalConstitution.pLabels_strict d ready a cs native strict j k l sorted
    simp only [RingPyramidalPublication.publish,selected]
    rw [actual]
    rw [row] at tail
    simpa only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,pure,Option.some.injEq] using tail
  · contradiction

theorem early_state {i : Input}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {v : Option Labels} (hit : early? i q = some v) :
    RingChemicalGraphProof.state i q = some v := by
  rw [RingChemicalGraphProof.state_eq]
  exact early_local (RingChemicalGraphProof.ready geom q) hit

/-- Exact successful-test value, including a flat frame's `some none`. -/
theorem early_of {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (cs : Fin 3 → Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s))
    (strict : Function.Injective (fun s => orderWord (cs s))) :
    early? i q = some ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      ((RingStereoSiblingPass.order (fun s => orderWord (cs s)) slots).map (atomId d) ++ [a.val])).map
      fun h => (.chiral h,.chiral h.swap)) := by
  have distinct := (nodup_injective (fun s => orderWord (cs s))).mpr strict
  simp only [early?,selected,directions_of i q d,keys_of d cs native,bind,Option.bind_some]
  simp [distinct]

/-- Presence and injectivity of the three full constitutional words suffice
for a hit, independently of geometry and every frozen stereo reader. -/
theorem complete {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (cs : Fin 3 → Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s))
    (strict : Function.Injective (fun s => orderWord (cs s))) : (early? i q).isSome = true := by
  have distinct := (nodup_injective (fun s => orderWord (cs s))).mpr strict
  simp only [early?,selected,directions_of i q d,keys_of d cs native,bind,Option.bind_some]
  simp [distinct]

/-- Once all three constitutional keys are available, an early miss leaves
an actual constitutional tie; it cannot hide a strict full-depth order. -/
theorem miss_tie {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (cs : Fin 3 → Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s))
    (miss : early? i q = none) :
    ∃ j k : Fin 3, j ≠ k ∧ orderWord (cs j) = orderWord (cs k) := by
  classical
  by_contra no
  push_neg at no
  have strict : Function.Injective (fun s => orderWord (cs s)) := by
    intro j k equal
    by_contra different
    exact no j k different equal
  have hit := complete selected d cs native strict
  rw [miss] at hit
  contradiction

/-- Every selected P/As early miss has a genuine complete constitutional tie
between distinct valid incident arms. No missing-key or supplied-frame premise
remains, and the retained frame includes the incoming rerooted arm. -/
theorem selected_miss_tie {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a)
    (miss : early? i q = none) :
    ∃ u v : RingActivePairs.Arm i, ∃ ku kv : Key,
      u ≠ v ∧ i.certified.LocalizedRerootCursorValid u ∧ i.certified.LocalizedRerootCursorValid v ∧
      u ∈ RingRetainedAuxiliary.frame i.certified q ∧ v ∈ RingRetainedAuxiliary.frame i.certified q ∧
      u.occurrence.val.root = q.val.root ∧ v.occurrence.val.root = q.val.root ∧
      RingRetainedChemicalTrace.key? i u = some ku ∧ RingRetainedChemicalTrace.key? i v = some kv ∧
      orderWord ku = orderWord kv := by
  obtain ⟨d⟩ := RingPyramidalSource.selected_framed selected
  have covered (k : Fin 3) := RingRetainedChemicalCoverage.key_total i
    (RingRetainedChemicalCoverage.admitted_atoms i) (d.arm k) (d.valid k)
  choose cs native using covered
  obtain ⟨j,k,different,tied⟩ := miss_tie selected d cs native miss
  have nd : ((List.finRange 3).map d.arm).Nodup := by
    change [d.arm 0,d.arm 1,d.arm 2].Nodup
    rw [← d.incident]
    exact i.certified.executableLocalizedRerootChildren_nodup (⟨q,none⟩ : RingActivePairs.Arm i)
  have distinct : d.arm j ≠ d.arm k := by
    intro equal
    exact different (List.inj_on_of_nodup_map nd (List.mem_finRange j) (List.mem_finRange k) equal)
  exact ⟨d.arm j,d.arm k,cs j,cs k,distinct,d.valid j,d.valid k,d.mem j,d.mem k,
    d.rooted j,d.rooted k,native j,native k,tied⟩

end TetraStereo.Engine.RingPyramidalEarly
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.directions_of
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.keys_source
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.early_local
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.early_state
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.complete
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.early_of
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.miss_tie
assert_kernel_only TetraStereo.Engine.RingPyramidalEarly.selected_miss_tie
