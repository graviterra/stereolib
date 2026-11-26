import TetraStereo.Engine.RingMolecularPairScore
import TetraStereo.Engine.RingPyramidalPairwise
import Mathlib.Tactic.CongrExclamation

/-! Numeric fixed-reference keys in the actual phosphorus trial rows. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalNumericRows
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActiveDistanceSchedule (View)
open RingPyramidalPublication RingFrameTransport RingPyramidalPairwise
open RingRetainedChemicalTrace (Word)
open RingFullPathTrialReadings (trialKey)
open RingMolecularPairScore (numericKey)
attribute [local instance] lexOrd

private def markedRows {i : Input} (r : View i) (mark : Option Nat) (xs : List (Ligand i)) :=
  xs.mapM fun x => (markWord? i r mark x.arm).map (fun w => (x,w))

/-- The original physical IDs, failed reads and promotion words are retained;
only the comparison key uses unsigned binary encodings. -/
def data (i : Input) (q : Site i) (r : View i) : Data where
  shape := decide ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  ordinary rev := (ligands? i q r rev).map
    (extractRow (fun x => x.atom) (fun x => numericKey x.priority []))
  marked rev mark := do
    let xs ← ligands? i q r rev
    let rows ← markedRows r mark xs
    return extractRow (fun x => x.1.atom) (fun x => numericKey x.1.priority x.2) rows

private theorem extract_eq {α : Type} (ids : α → Nat) (old new : α → List (List Word))
    (xs : List α) (same : ∀ a ∈ xs, ∀ b ∈ xs, old a < old b ↔ new a < new b) :
    extractRow ids old xs = extractRow ids new xs := by
  unfold extractRow
  congr 1
  funext a b
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact same _ (List.get_mem _ _) _ (List.get_mem _ _)

private theorem mapM_property {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ∀ y ∈ ys, ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => cases h; simp
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨v,hv,rest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vs,hvs,last⟩ := Option.bind_eq_some_iff.mp rest
    cases last
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x,List.mem_cons_self,hv⟩
    · obtain ⟨a,ha,eqn⟩ := ih hvs y hy
      exact ⟨a,List.mem_cons_of_mem _ ha,eqn⟩

private theorem ligand_read {i : Input} {q : Site i} {r : View i} {rev : Bool}
    {xs : List (Ligand i)} (got : ligands? i q r rev = some xs) {x : Ligand i} (mem : x ∈ xs) :
    i.certified.LocalizedRerootCursorValid x.arm ∧ x.arm.occurrence.val.root = q.val.root ∧
    RingFullPathEligibility.key? i r rev x.arm = some x.priority := by
  obtain ⟨a,ha,read⟩ := mapM_property got x mem
  change ligandOf i r rev a = some x at read
  unfold ligandOf at read
  obtain ⟨atom,hatom,rest⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨key,hkey,last⟩ := Option.bind_eq_some_iff.mp rest
  cases last
  have frame := i.certified.executableLocalizedRerootChildren_declarative (⟨q,none⟩ : Arm i)
  exact ⟨i.certified.localizedRerootChild_valid _ _ _ frame ha,
    i.certified.localizedRerootChildren_root_eq _ _ _ frame ha,hkey⟩

private theorem marked_native {i : Input} (r : View i) (mark : Option Nat) (xs : List (Ligand i)) :
    xs.mapM (rowOf i r mark) = (markedRows r mark xs).map
      (List.map fun x => (x.1.atom,trialKey x.1.priority x.2)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hw : markWord? i r mark x.arm <;>
      simp [markedRows,rowOf,List.mapM_cons,hw,ih,Option.map_bind]
    all_goals
      cases ht : markedRows r mark xs <;> simp only [markedRows] at ht <;> simp [ht]

private theorem marked_mem {i : Input} {r : View i} {mark : Option Nat} {xs : List (Ligand i)}
    {rows : List (Ligand i × Word)} (h : markedRows r mark xs = some rows)
    {x : Ligand i × Word} (hx : x ∈ rows) : x.1 ∈ xs := by
  obtain ⟨a,ha,eqn⟩ := mapM_property h x hx
  obtain ⟨w,_,last⟩ := Option.map_eq_some_iff.mp eqn
  cases last
  exact ha

/-- On the ready molecular reader the numeric rows are exactly the native
pairwise ballots for every ordinary and marked trial, on both geometries. -/
theorem data_exact (i : Input) (q : Site i) (r : View i) (ready : RingGroupedStereo.Ready q r) :
    data i q r = nativeData i q r := by
  have rowsEqual (rev : Bool) {xs : List (Ligand i)} (got : ligands? i q r rev = some xs)
      (a b : Ligand i) (ha : a ∈ xs) (hb : b ∈ xs) (m n : Word) :
      trialKey a.priority m < trialKey b.priority n ↔ numericKey a.priority m < numericKey b.priority n := by
    obtain ⟨va,ra,ka⟩ := ligand_read got ha
    obtain ⟨vb,rb,kb⟩ := ligand_read got hb
    exact RingMolecularPairScore.key_lt ready rev a.arm b.arm va vb ra rb ka kb m n
  unfold data nativeData
  congr 1
  · funext rev
    cases got : ligands? i q r rev with
    | none => rfl
    | some xs =>
      simp only [Option.map_some]
      exact congrArg some (extract_eq _ _ _ xs (fun a ha b hb => rowsEqual rev got a b ha hb [] [])).symm
  · funext rev mark
    cases got : ligands? i q r rev with
    | none => rfl
    | some xs =>
      simp only [bind,pure,Option.bind_some]
      rw [marked_native]
      cases hm : markedRows r mark xs with
      | none => rfl
      | some rows =>
        simp only [Option.map_some,Option.bind_some]
        have mapped : extractRow Prod.fst Prod.snd
            (rows.map fun x => (x.1.atom,trialKey x.1.priority x.2)) =
            extractRow (fun x => x.1.atom) (fun x => trialKey x.1.priority x.2) rows := by
          simp [extractRow,List.get_eq_getElem]
          constructor <;> congr! <;> simp
        rw [mapped]
        exact congrArg some (extract_eq _ _ _ rows (fun a ha b hb =>
          rowsEqual rev got a.1 b.1 (marked_mem hm ha) (marked_mem hm hb) a.2 b.2)).symm

end TetraStereo.Engine.RingPyramidalNumericRows
assert_kernel_only TetraStereo.Engine.RingPyramidalNumericRows.data_exact
