import TetraStereo.Engine.RingGroupedMark

/-! # The all-zero Rule 6 word preserves the complete through-4c row shape. -/

set_option autoImplicit false
namespace TetraStereo.Engine.RingNeutralPromotion
open OneCenter RingStereoSiblingPass
open RingGroupedMark (Entry)
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Key Word)

def eraseRow (xs : List Nat) := xs.map fun _ => 0
def eraseWord (w : Word) := w.map eraseRow
private def eraseLevels (ls : Layers) := ls.map eraseWord

private def lift (b : Branch) : Branch := ⟨b.shallow,b.deep,0,eraseLevels b.levels⟩

private theorem lift_word (b : Branch) : (lift b).word = eraseWord b.word := by
  simp [lift,Branch.word,eraseWord,eraseRow,eraseLevels,List.map_flatten]
  rfl

private theorem strict_extend {α : Type} [LinearOrder α] {xs ys : List α}
    (less : xs < ys) (size : xs.length = ys.length) (a b : α) :
    xs ++ [a] < ys ++ [b] := by
  change List.Lex (· < ·) xs ys at less
  induction less with
  | nil => simp at size
  | rel h => exact List.Lex.rel h
  | cons _ ih => exact List.Lex.cons (ih (Nat.succ.inj size))

private theorem le_extend {α : Type} [LinearOrder α] {xs ys : List α} {a b : α}
    (size : xs.length = ys.length) (tie : xs = ys → a = b) :
    (xs ++ [a] ≤ ys ++ [b]) ↔ xs ≤ ys := by
  rcases lt_trichotomy xs ys with lt | eqn | gt
  · simp [(strict_extend lt size a b).le,lt.le]
  · simp [eqn,tie eqn]
  · simp [(strict_extend gt size.symm b a).not_ge,gt.not_ge]

private theorem lift_sort (cs : List Branch) (key : Branch → List Nat)
    (width : ∀ b ∈ cs, (key b).length = 5)
    (proj : ∀ b, key (lift b) = key b ++ [0]) :
    (order key cs).map lift = order key (cs.map lift) := by
  apply List.map_mergeSort
  intro a ha b hb
  change decide (_ ≤ _) = decide (_ ≤ _)
  rw [proj,proj]
  simp [le_extend ((width b hb).trans (width a ha).symm) (fun _ => rfl)]

private theorem deep_sort (cs : List Branch) (width : ∀ b ∈ cs, b.deep.length = 5) :
    (order Branch.deep cs).map lift = order Branch.deep (cs.map lift) := by
  apply List.map_mergeSort
  intro a ha b hb
  have tie (h : b.deep = a.deep) : (lift b).word = (lift a).word := by
    have h' := congrArg List.getLast? h
    simp only [Branch.deep,List.getLast?_append,List.getLast?_singleton,Option.some_or] at h'
    simpa [lift_word] using congrArg (Option.map eraseWord) h'
  change decide (_ ≤ _) = decide ((b.deep ++ [(lift b).word]) ≤ (a.deep ++ [(lift a).word]))
  simp [le_extend ((width b hb).trans (width a ha).symm) tie]

private theorem erase_interleave (xs ys : Layers) :
    eraseLevels (RingChildKeyRecovery.interleave xs ys) =
      RingChildKeyRecovery.interleave (eraseLevels xs) (eraseLevels ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys with
    | nil => rfl
    | cons y ys => simp [eraseLevels,eraseWord,RingChildKeyRecovery.interleave] at ih ⊢; exact ih ys

private theorem erase_forest (xs : List Branch) :
    eraseLevels ((xs.map Branch.levels).foldr RingChildKeyRecovery.interleave []) =
      ((xs.map lift).map Branch.levels).foldr RingChildKeyRecovery.interleave [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.foldr_cons,erase_interleave,ih]
    rfl

private theorem erase_rows (xs ys : List Branch) :
    eraseLevels (rows xs ys) = rows (xs.map lift) (ys.map lift) := by
  change eraseWord [xs.map Branch.value,ys.map Branch.value] :: _ = _ :: _
  exact congrArg₂ List.cons (by simp [eraseWord,eraseRow,lift]) (erase_forest ys)

-- The five components are Rules 1a, 1b, 2, 4a and 4c in the unseeded pass.
-- This fixed width prevents the appended word from overtaking an earlier stage.
private def Good (e : Entry) : Prop :=
  e.2 = lift e.1.lower ∧ e.1.lower.shallow.length = 5 ∧ e.1.lower.deep.length = 5

theorem neutralBit {i : Input} (q : Arm i) : RingGroupedMark.bit i.molecule.atomCount q = 0 := by
  unfold RingGroupedMark.bit
  cases h : q.occurrence.val.node.current? with
  | none => rfl
  | some a =>
    have bound : a.val < i.molecule.atomCount := by
      rw [← i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]; exact a.isLt
    simp [Nat.ne_of_lt bound]

private theorem join_good {i : Input} (q : Arm i) (k : Key) (v : Option RingNestedActivePair.Labels)
    (cs : List Entry) (below : ∀ e ∈ cs, Good e) : Good (RingGroupedMark.join i.molecule.atomCount q k v cs) := by
  refine ⟨?_,rfl,rfl⟩
  let low := (cs.map Prod.fst).map RingRetainedStereoDecision.ArmProfile.lower
  have mem (b) (hb : b ∈ low) : ∃ e ∈ cs, b = e.1.lower := by
    simpa [low,List.map_map,Function.comp_def,eq_comm] using hb
  have widths (b) (hb : b ∈ low) : b.shallow.length = 5 ∧ b.deep.length = 5 := by
    obtain ⟨e,h,rfl⟩ := mem b hb
    exact (below e h).2
  have marks : cs.map Prod.snd = low.map lift := by
    simp only [low,List.map_map,Function.comp_def]
    exact List.map_congr_left (fun e he => (below e he).1)
  have sh := lift_sort low Branch.shallow (fun b hb => (widths b hb).1) (fun _ => rfl)
  have de := deep_sort low (fun b hb => (widths b hb).2)
  let lower := (RingGroupedStereo.assemble k v (cs.map Prod.fst)).lower
  change (⟨lower.shallow,lower.deep,RingGroupedMark.bit i.molecule.atomCount q,
    rows (order Branch.shallow (cs.map Prod.snd)) (order Branch.deep (cs.map Prod.snd))⟩ : Branch) = _
  rw [neutralBit,marks,← sh,← de,← erase_rows]
  rfl

private theorem build_good {i : Input} (read : Reader i) (key : Arm i → Option Key)
    (edges : Arm i → List (Arm i)) (n : Nat) (q : Arm i) {e : Entry}
    (h : RingGroupedMark.build i read i.molecule.atomCount key edges n q = some e) : Good e := by
  induction n generalizing q e with
  | zero => contradiction
  | succ n ih =>
    unfold RingGroupedMark.build at h
    obtain ⟨v,_,more⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u,_,more⟩ := Option.bind_eq_some_iff.mp more
    obtain ⟨k,_,more⟩ := Option.bind_eq_some_iff.mp more
    obtain ⟨cs,all,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    apply join_good
    intro x hx
    obtain ⟨c,_,get⟩ := RingRetainedUnitPass.forOutput all hx
    exact ih c get

/-- The complete neutral word is the through-4c word with every entry zeroed.
The original parent rows and their boundaries are preserved. -/
theorem neutral_word {i : Input} {read : Reader i} {q : Arm i} {e : Entry}
    (found : RingGroupedMark.arm? i read i.molecule.atomCount q = some e) :
    e.2.word = eraseWord e.1.lower.word := by
  rw [(build_good read _ _ _ q found).1,lift_word]

end TetraStereo.Engine.RingNeutralPromotion

assert_kernel_only TetraStereo.Engine.RingNeutralPromotion.neutral_word
