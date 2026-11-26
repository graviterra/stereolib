import TetraStereo.Engine.RingPyramidalEarly

/-! All-depth Rule 4a decisions using only the independent molecular unit pass. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalUnitEarly
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Reader Labels)
open RingPyramidalSource
open RingStereoSiblingPass (Branch)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
attribute [local instance] lexOrd
open private nodup_injective from TetraStereo.Engine.RingPyramidalSource

/-- Actual through-4a priority, before Rule 4b, 4c, 5 or promotion. -/
def keys? {i : Input} {q : Site i} (d : Directions i q) (r : Reader i) : Option (Fin 3 → Branch) := do
  let x ← RingRetainedStereoRefinement.priority i r false [] (d.arm 0)
  let y ← RingRetainedStereoRefinement.priority i r false [] (d.arm 1)
  let z ← RingRetainedStereoRefinement.priority i r false [] (d.arm 2)
  return ![x,y,z]

theorem keys_source {i : Input} {q : Site i} {d : Directions i q} {r : Reader i} {cs : Fin 3 → Branch}
    (hit : keys? d r = some cs) : ∀ s, RingRetainedStereoRefinement.priority i r false [] (d.arm s) = some (cs s) := by
  unfold keys? at hit
  cases hx : RingRetainedStereoRefinement.priority i r false [] (d.arm 0) <;>
  cases hy : RingRetainedStereoRefinement.priority i r false [] (d.arm 1) <;>
  cases hz : RingRetainedStereoRefinement.priority i r false [] (d.arm 2) <;> simp [hx,hy,hz] at hit
  subst cs
  intro s
  fin_cases s <;> assumption

theorem keys_of {i : Input} {q : Site i} (d : Directions i q) (r : Reader i) (cs : Fin 3 → Branch)
    (native : ∀ s, RingRetainedStereoRefinement.priority i r false [] (d.arm s) = some (cs s)) : keys? d r = some cs := by
  simp only [keys?,native 0,native 1,native 2,Option.bind_some,bind,pure]
  congr 1
  funext s
  fin_cases s <;> rfl


/-- The independent unit pass supplies the exact through-4a part of every
full reading, on either reflected geometry. -/
theorem through_exact {i : Input} {q : Site i} (d : Directions i q)
    {r : Reader i} {bs : Fin 3 → Branch} (computed : keys? d r = some bs)
    {rev : Bool} {s : Fin 3} {key : Key} (actual : Reads i r rev (d.arm s) key) :
    key.throughFourA = (bs s).deep := by
  obtain ⟨u,l,ar,as',fr,du,_,_,_,_,rfl⟩ := actual
  have native := RingRetainedUnitPass.source i r rev _ _ (keys_source computed s)
  exact congrArg Branch.deep (RingRetainedUnitPass.Reading.unique du native)

private theorem ballot {i : Input} {q : Site i} (d : Directions i q)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom)
    (bs : Fin 3 → Branch) (computed : keys? d r = some bs)
    (strict : Function.Injective (fun s => (bs s).deep)) (j k l : Fin 3)
    (legal : RingStereoSiblingPass.Legal (fun s => (bs s).deep) slots [j,k,l]) (rev : Bool) :
    ∃ ks : Fin 3 → Key, Ballots d r a rev ks
      [readback? (geometry i rev) [atomId d j,atomId d k,atomId d l,a.val]] := by
  have each (s : Fin 3) := RingFullPathEligibility.key_exact ready rev (d.arm s) (d.valid s) (d.rooted s)
  choose ks got exactKey using each
  have reads (s : Fin 3) : Reads i r rev (d.arm s) (ks s) := (exactKey s _).mpr rfl
  have shape (s : Fin 3) := through_exact d computed (reads s)
  let w (s : Fin 3) := trialKey (ks s) []
  have inj : Function.Injective w := by
    intro s t eqn
    apply strict
    have heads := (List.cons.inj eqn).1
    exact (shape s).symm.trans (heads.trans (shape t))
  have order (s t : Fin 3) (ne : s ≠ t) : w s < w t ↔ (bs s).deep < (bs t).deep := by
    change (ks s).throughFourA :: _ < (ks t).throughFourA :: _ ↔ _
    rw [shape s,shape t,List.cons_lt_cons_iff]
    simp [strict.ne ne]
  have sorted : RingStereoSiblingPass.Legal w slots [j,k,l] := by
    refine ⟨legal.perm,List.pairwise_map.mpr ?_⟩
    have descending := List.pairwise_map.mp legal.descending
    have nd : [j,k,l].Nodup := legal.perm.nodup_iff.mpr (by decide)
    exact (descending.and nd).imp (fun {s t} h => le_of_lt ((order t s h.2.symm).mpr
      (lt_of_le_of_ne h.1 (strict.ne h.2.symm))))
  have different : ks 0 ≠ ks 1 := by
    intro eqn
    apply (by decide : (0 : Fin 3) ≠ 1)
    apply inj
    simp only [w,eqn]
  refine ⟨ks,reads,?_⟩
  rw [show trials ks = [none] by simp [trials,different]]
  apply List.Forall₂.cons _ (List.Forall₂.nil)
  refine ⟨fun _ => [],fun _ => rfl,?_⟩
  exact Outcome.read j k l inj sorted ((sense_exact _ _ _ _ _ _).mpr rfl)

/-- A strict complete unit order reads the actual physical P/As frame. -/
theorem pLabels_strict {i : Input} {q : Site i} (d : Directions i q)
    {r : Reader i} (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom)
    (bs : Fin 3 → Branch) (computed : keys? d r = some bs)
    (strict : Function.Injective (fun s => (bs s).deep)) (j k l : Fin 3)
    (legal : RingStereoSiblingPass.Legal (fun s => (bs s).deep) slots [j,k,l]) :
    RingPyramidalPublication.pLabels i q r a =
      (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        [atomId d j,atomId d k,atomId d l,a.val]).map fun h => (.chiral h,.chiral h.swap) := by
  obtain ⟨x,hx⟩ := ballot d ready a bs computed strict j k l legal false
  obtain ⟨y,hy⟩ := ballot d ready a bs computed strict j k l legal true
  have source := (source_iff ready a _).mp (Source.centre d hx hy)
  rw [source]
  clear hx hy source x y
  simp only [geometry,Bool.false_eq_true,if_false,if_true,readback_mirror]
  generalize readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
    [atomId d j,atomId d k,atomId d l,a.val] = hand
  cases hand with
  | none => rfl
  | some hand => cases hand <;> rfl
/-- A hit contains a fully decided optional label pair; only a strict
through-4a order is read. No stereo suffix or promotion word is consulted. -/
def early? (i : Input) (q : Site i) (r : Reader i) : Option (Option Labels) := do
  let a ← RingPyramidalPublication.focusP i q
  let d ← RingPyramidalEarly.directions? i q
  let cs ← keys? d r
  let word := fun s => (cs s).deep
  if [word 0,word 1,word 2].Nodup then
    let row := RingStereoSiblingPass.order word slots
    return (readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      (row.map (atomId d) ++ [a.val])).map fun h => (.chiral h,.chiral h.swap)
  else none

/-- Every hit equals the ordinary native local publication on any ready reader. -/
theorem early_local {i : Input}
    {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r) {v : Option Labels}
    (hit : early? i q r = some v) : RingPyramidalPublication.publish i q r = some v := by
  simp only [early?,bind,Option.bind_eq_some_iff] at hit
  obtain ⟨a,selected,d,hd,cs,hcs,tail⟩ := hit
  split at tail
  · rename_i distinct
    have strict := (nodup_injective (fun s => (cs s).deep)).mp distinct
    have legal := RingStereoSiblingPass.legal_order (fun s => (cs s).deep) slots
    have size : (RingStereoSiblingPass.order (fun s => (cs s).deep) slots).length = 3 := legal.perm.length_eq
    obtain ⟨j,k,l,row⟩ := List.length_eq_three.mp size
    have sorted : RingStereoSiblingPass.Legal (fun s => (cs s).deep) slots [j,k,l] := row ▸ legal
    have actual := pLabels_strict d ready a cs hcs strict j k l sorted
    simp only [RingPyramidalPublication.publish,selected]
    rw [actual]
    rw [row] at tail
    simpa only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,pure,Option.some.injEq] using tail
  · contradiction

/-- Exact successful-test value, including a flat frame's `some none`. -/
theorem early_of {i : Input} {q : Site i} {r : Reader i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (cs : Fin 3 → Branch)
    (native : ∀ s, RingRetainedStereoRefinement.priority i r false [] (d.arm s) = some (cs s))
    (strict : Function.Injective (fun s => (cs s).deep)) :
    early? i q r = some ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      ((RingStereoSiblingPass.order (fun s => (cs s).deep) slots).map (atomId d) ++ [a.val])).map
      fun h => (.chiral h,.chiral h.swap)) := by
  have distinct := (nodup_injective (fun s => (cs s).deep)).mpr strict
  simp only [early?,selected,RingPyramidalEarly.directions_of i q d,keys_of d r cs native,bind,Option.bind_some]
  simp [distinct]

/-- Presence and injectivity of the three complete through-4a words suffice
for a hit, independently of geometry. -/
theorem complete {i : Input} {q : Site i} {r : Reader i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (cs : Fin 3 → Branch)
    (native : ∀ s, RingRetainedStereoRefinement.priority i r false [] (d.arm s) = some (cs s))
    (strict : Function.Injective (fun s => (cs s).deep)) : (early? i q r).isSome = true := by
  have distinct := (nodup_injective (fun s => (cs s).deep)).mpr strict
  simp only [early?,selected,RingPyramidalEarly.directions_of i q d,keys_of d r cs native,bind,Option.bind_some]
  simp [distinct]

/-- Once all three through-4a keys are available, an early miss leaves
an actual through-4a tie; it cannot hide a strict full-depth order. -/
theorem miss_tie {i : Input} {q : Site i} {r : Reader i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (d : Directions i q)
    (cs : Fin 3 → Branch)
    (native : ∀ s, RingRetainedStereoRefinement.priority i r false [] (d.arm s) = some (cs s))
    (miss : early? i q r = none) :
    ∃ j k : Fin 3, j ≠ k ∧ (cs j).deep = (cs k).deep := by
  classical
  by_contra no
  push_neg at no
  have strict : Function.Injective (fun s => (cs s).deep) := by
    intro j k equal
    by_contra different
    exact no j k different equal
  have hit := complete selected d cs native strict
  rw [miss] at hit
  contradiction


/-- On a selected real P/As and ready reader, a missing early decision is an
actual through-4a tie between distinct valid incident arms. -/
theorem selected_miss_tie {i : Input} {q : Site i} {r : Reader i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a)
    (ready : RingGroupedStereo.Ready q r) (miss : early? i q r = none) :
    ∃ u v : RingActivePairs.Arm i, ∃ ku kv : Key,
      u ≠ v ∧ i.certified.LocalizedRerootCursorValid u ∧ i.certified.LocalizedRerootCursorValid v ∧
      u ∈ RingRetainedAuxiliary.frame i.certified q ∧ v ∈ RingRetainedAuxiliary.frame i.certified q ∧
      u.occurrence.val.root = q.val.root ∧ v.occurrence.val.root = q.val.root ∧
      Reads i r false u ku ∧ Reads i r false v kv ∧ ku.throughFourA = kv.throughFourA := by
  obtain ⟨d⟩ := selected_framed selected
  have covered (k : Fin 3) := RingOccurrenceStereo.rank_total ready false []
    (d.arm k) (d.valid k) (d.rooted k)
  choose bs native using covered
  have computed : keys? d r = some bs := keys_of d r bs native
  obtain ⟨j,k,different,tied⟩ := miss_tie selected d bs native miss
  have nd : ((List.finRange 3).map d.arm).Nodup := by
    change [d.arm 0,d.arm 1,d.arm 2].Nodup
    rw [← d.incident]
    exact i.certified.executableLocalizedRerootChildren_nodup (⟨q,none⟩ : RingActivePairs.Arm i)
  have distinct : d.arm j ≠ d.arm k := by
    intro equal
    exact different (List.inj_on_of_nodup_map nd (List.mem_finRange j) (List.mem_finRange k) equal)
  obtain ⟨ku,_,hu⟩ := RingFullPathEligibility.key_exact ready false (d.arm j) (d.valid j) (d.rooted j)
  obtain ⟨kv,_,hv⟩ := RingFullPathEligibility.key_exact ready false (d.arm k) (d.valid k) (d.rooted k)
  have su := (hu ku).mpr rfl
  have sv := (hv kv).mpr rfl
  exact ⟨d.arm j,d.arm k,ku,kv,distinct,d.valid j,d.valid k,d.mem j,d.mem k,
    d.rooted j,d.rooted k,su,sv,(through_exact d computed su).trans
      (tied.trans (through_exact d computed sv).symm)⟩

end TetraStereo.Engine.RingPyramidalUnitEarly
assert_kernel_only TetraStereo.Engine.RingPyramidalUnitEarly.through_exact
assert_kernel_only TetraStereo.Engine.RingPyramidalUnitEarly.pLabels_strict
assert_kernel_only TetraStereo.Engine.RingPyramidalUnitEarly.early_local
assert_kernel_only TetraStereo.Engine.RingPyramidalUnitEarly.early_of
assert_kernel_only TetraStereo.Engine.RingPyramidalUnitEarly.selected_miss_tie
