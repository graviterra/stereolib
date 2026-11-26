import TetraStereo.Engine.RingFrameTransport
import Batteries.Tactic.OpenPrivate

/-! Comparison-only three-coordinate phosphorus ballots. Both physical geometries
and every ordinary/marked trial retain ties and unavailable observations. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalPairwise
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (View)
open RingPyramidalPublication RingFrameTransport
open RingRetainedChemicalTrace (Word)
attribute [local instance] lexOrd
open private trial_eq from TetraStereo.Engine.RingFullPathTrialParity

/-- Physical IDs and pairwise strict comparisons; no priority values are stored. -/
structure Row where
  size : Nat
  ids : Fin size → Nat
  less : Fin size → Fin size → Bool

def Row.strict (r : Row) : Prop := ∀ a b, a ≠ b → r.less a b = true ∨ r.less b a = true
instance (r : Row) : Decidable r.strict := by unfold Row.strict; infer_instance

def Row.read (r : Row) (sense : List Nat → Option RS) (focus : Nat) : Option RS :=
  if r.strict then sense
    (((List.finRange r.size).mergeSort (fun a b => !(r.less a b))).map r.ids ++ [focus]) else none

def extractRow {α κ : Type} [LinearOrder κ] (ids : α → Nat) (key : α → κ) (xs : List α) : Row :=
  ⟨xs.length,fun k => ids (xs.get k),fun a b => decide (key (xs.get a) < key (xs.get b))⟩

private theorem extract_strict {α κ : Type} [LinearOrder κ] (ids : α → Nat) (key : α → κ) (xs : List α) :
    (extractRow ids key xs).strict ↔ (xs.map key).Nodup := by
  have mapped : (List.finRange xs.length).map (fun k => key (xs.get k)) = xs.map key := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map key) (List.map_get_finRange xs)
  have inj : Function.Injective (fun k : Fin xs.length => key (xs.get k)) ↔ (xs.map key).Nodup := by
    rw [←mapped]
    constructor
    · intro h; exact (List.nodup_finRange _).map h
    · intro h a b eqn
      exact (List.nodup_map_iff_inj_on (List.nodup_finRange _)).mp h a
        (List.mem_finRange _) b (List.mem_finRange _) eqn
  rw [←inj]
  constructor
  · intro h a b eqn
    by_contra ne
    rcases h a b ne with lt | gt
    · exact (ne_of_lt (of_decide_eq_true lt)) eqn
    · exact (ne_of_lt (of_decide_eq_true gt)) eqn.symm
  · intro h a b ne
    rcases lt_or_gt_of_ne (h.ne ne) with lt | gt
    · exact Or.inl (decide_eq_true lt)
    · exact Or.inr (decide_eq_true gt)

private theorem extract_order {α κ : Type} [LinearOrder κ] (ids : α → Nat) (key : α → κ) (xs : List α) :
    (((List.finRange (extractRow ids key xs).size).mergeSort
      (fun a b => !((extractRow ids key xs).less a b))).map (extractRow ids key xs).ids) =
      (RingStereoSiblingPass.order key xs).map ids := by
  have sorted := List.map_mergeSort (l := List.finRange xs.length) (f := xs.get)
    (r := fun a b => !(decide (key (xs.get a) < key (xs.get b))))
    (s := fun a b => decide (key b ≤ key a)) (by
      intro a _ b _
      by_cases lt : key xs[a.val] < key xs[b.val]
      · have off : ¬ key xs[b.val] ≤ key xs[a.val] := not_le.mpr lt
        simp [lt,off]
      · have on : key xs[b.val] ≤ key xs[a.val] := le_of_not_gt lt
        simp [lt,on])
  rw [List.map_get_finRange] at sorted
  have mapped := congrArg (List.map ids) sorted
  simpa only [extractRow,RingStereoSiblingPass.order,List.map_map,Function.comp_def] using mapped

theorem finishS_extract (sense : List Nat → Option RS) (a : Nat)
    (rows : List (Nat × List (List Word))) :
    finishS sense a rows = some ((extractRow Prod.fst Prod.snd rows).read sense a) := by
  by_cases nd : (rows.map Prod.snd).Nodup
  · have strict := (extract_strict Prod.fst Prod.snd rows).mpr nd
    simp only [finishS,nd,decide_true,Bool.not_true,Bool.false_eq_true,if_false,Row.read,if_pos strict,extract_order]
  · have notStrict := mt (extract_strict Prod.fst Prod.snd rows).mp nd
    simp [finishS,Row.read,nd,notStrict]

def Row.equal (r : Row) (a b : Fin r.size) : Prop := r.less a b = false ∧ r.less b a = false
instance (r : Row) (a b : Fin r.size) : Decidable (r.equal a b) := by unfold Row.equal; infer_instance

private theorem extract_equal {α κ : Type} [LinearOrder κ] (ids : α → Nat) (key : α → κ)
    (xs : List α) (a b : Fin xs.length) :
    (extractRow ids key xs).equal a b ↔ key (xs.get a) = key (xs.get b) := by
  change (decide (_ < _) = false ∧ decide (_ < _) = false) ↔ _
  simp only [decide_eq_false_iff_not]
  exact ⟨fun h => le_antisymm (le_of_not_gt h.2) (le_of_not_gt h.1),fun h => by
    change key xs[a.val] = key xs[b.val] at h
    simp [h]⟩

/-- All three ordinary ligands tie exactly when adjacent pairs tie. -/
def Row.marks (r : Row) : List (Option Nat) :=
  if h : r.size = 3 then
    let slot : Fin 3 → Fin r.size := Fin.cast h.symm
    if r.equal (slot 0) (slot 1) ∧ r.equal (slot 1) (slot 2) then
      (List.finRange r.size).map (fun k => some (r.ids k)) else [none]
  else []

private theorem marks_extract {i : Input} (xs : List (Ligand i)) :
    (extractRow (fun x => x.atom) (fun x => RingFullPathTrialReadings.trialKey x.priority []) xs).marks = marksOf xs := by
  match xs with
  | [] | [_] | [_,_] | _::_::_::_::_ => simp [Row.marks,extractRow,marksOf]
  | [a,b,c] =>
    have equal (s t : Fin 3) :
        (extractRow (fun x : Ligand i => x.atom) (fun x => RingFullPathTrialReadings.trialKey x.priority []) [a,b,c]).equal s t ↔
        ([a,b,c].get s).priority = ([a,b,c].get t).priority :=
      (extract_equal (fun x : Ligand i => x.atom) (fun x => RingFullPathTrialReadings.trialKey x.priority []) [a,b,c] s t).trans ⟨fun h => ((trial_eq _ _ [] []).mp h).1,fun h => by rw [h]⟩
    change (if (extractRow (fun x : Ligand i => x.atom) (fun x => RingFullPathTrialReadings.trialKey x.priority []) [a,b,c]).equal (0:Fin 3) (1:Fin 3) ∧
        (extractRow (fun x : Ligand i => x.atom) (fun x => RingFullPathTrialReadings.trialKey x.priority []) [a,b,c]).equal (1:Fin 3) (2:Fin 3)
      then [some a.atom,some b.atom,some c.atom] else [none]) = _
    simp [equal,marksOf,Bool.and_eq_true,beq_iff_eq]

/-- Each optional marked row retains an actual failed key/mark read. -/
structure Data where
  shape : Bool
  ordinary : Bool → Option Row
  marked : Bool → Option Nat → Option Row

def Data.hands (d : Data) (sense : List Nat → Option RS) (focus : Nat) (rev : Bool) :
    Option (List (Option RS)) := do
  let ordinary ← d.ordinary rev
  ordinary.marks.mapM fun mark => (d.marked rev mark).map (fun row => row.read sense focus)

def Data.publish (d : Data) (g : Geometry) (focus : Nat) : Option RingNestedActivePair.Labels := do
  guard d.shape
  let hs ← d.hands (senseOf g false) focus false
  let ms ← d.hands (senseOf g true) focus true
  RingFullPathPublication.crossed hs ms

def nativeData (i : Input) (q : Site i) (r : View i) : Data where
  shape := decide ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  ordinary rev := (ligands? i q r rev).map (extractRow (fun x => x.atom) (fun x => RingFullPathTrialReadings.trialKey x.priority []))
  marked rev mark := do
    let xs ← ligands? i q r rev
    let rows ← xs.mapM (rowOf i r mark)
    return extractRow Prod.fst Prod.snd rows


theorem handsS_native (sense : List Nat → Option RS) (i : Input) (q : Site i)
    (r : View i) (a : i.certified.Atom) (rev : Bool) :
    handsS sense i q r a rev = (nativeData i q r).hands sense a.val rev := by
  unfold handsS Data.hands nativeData
  cases hx : ligands? i q r rev with
  | none => simp [hx]
  | some xs =>
    simp only [hx,Option.bind_some,Option.map_some]
    simp only [bind,pure,Option.bind_some,Option.map_bind]
    rw [marks_extract]
    apply congrArg (fun f => (marksOf xs).mapM f)
    funext mark
    unfold trialS
    cases rows : xs.mapM (rowOf i r mark) <;> simp [finishS_extract]

theorem pLabelsG_native (i : Input) (g : Geometry) (q : Site i) (r : View i)
    (a : i.certified.Atom) :
    pLabelsG i g q r a = (nativeData i q r).publish g a.val := by
  unfold pLabelsG Data.publish
  rw [handsS_native,handsS_native]
  by_cases shape : (RingRetainedAuxiliary.frame i.certified q).length = 3 <;>
    simp [nativeData,shape]

/-- Exact native factorization, including ties, failed keys, and flat readbacks. -/
theorem publishG_native {i : Input} (g : Geometry) {q : Site i}
    {a : i.certified.Atom} (hp : focusP i q = some a) (r : View i) :
    publishG i g q r = some ((nativeData i q r).publish g a.val) := by
  rw [publishG_phosphorus g hp r,pLabelsG_native]


/-- Any independently supplied comparison table equal to the native projection
replays the native phosphorus publication; no hand or descriptor agreement is assumed. -/
theorem publishG_of_data {i : Input} (g : Geometry) {q : Site i}
    {a : i.certified.Atom} (hp : focusP i q = some a) (r : View i)
    (d : Data) (same : nativeData i q r = d) :
    publishG i g q r = some (d.publish g a.val) := by
  rw [publishG_native g hp r,same]

/-- Pairwise data suffice even when the two frozen readers differ arbitrarily. -/
theorem publishG_congr_data {i : Input} (g : Geometry) {q : Site i}
    {a : i.certified.Atom} (hp : focusP i q = some a) (r r' : View i)
    (same : nativeData i q r = nativeData i q r') :
    publishG i g q r = publishG i g q r' := by
  rw [publishG_native g hp r,publishG_native g hp r',same]

end TetraStereo.Engine.RingPyramidalPairwise
assert_kernel_only TetraStereo.Engine.RingPyramidalPairwise.finishS_extract
assert_kernel_only TetraStereo.Engine.RingPyramidalPairwise.publishG_native
assert_kernel_only TetraStereo.Engine.RingPyramidalPairwise.publishG_of_data
assert_kernel_only TetraStereo.Engine.RingPyramidalPairwise.publishG_congr_data
