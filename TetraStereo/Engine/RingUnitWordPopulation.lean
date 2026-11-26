import TetraStereo.Engine.RingReferenceGroupTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingUnitWordPopulation
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedUnitPass (Reading)
open RingRetainedReferenceGroup (Hit Listing)
open RingRetainedChemicalTrace (Word)

/-- The root's unit class followed by the deep slots of its actual Rule 4a
word. No occurrence identifiers or auxiliary reference hands enter this projection. -/
def stream (w : Word) : List Nat :=
  ((w.head?).getD []).head?.toList ++ deepValues w.tail

@[simp] theorem stream_word (b : Branch) : stream b.word = b.stream := by
  simp [stream,Branch.word,Branch.stream]

/-- Count uppercase publications, retaining repeated occurrences. -/
def population (w : Word) : Nat := (stream w).countP (· == 2)

theorem word_stream_eq {a b : Branch} (tie : a.word = b.word) : a.stream = b.stream := by
  simpa using congrArg stream tie

theorem word_population_eq {a b : Branch} (tie : a.word = b.word) :
    (a.stream.countP (· == 2)) = (b.stream.countP (· == 2)) :=
  congrArg (fun xs : List Nat => xs.countP (· == 2)) (word_stream_eq tie)

private def mark (n : Nat) : Nat := if n = 2 then 1 else 0
private def rowMass (w : Word) : Nat := ((w.map (fun r => (r.map mark).sum))).sum
private def layerMass (ls : Layers) : Nat := (ls.map rowMass).sum

private theorem rowMass_append (a b : Word) : rowMass (a ++ b) = rowMass a + rowMass b := by
  simp [rowMass]

private theorem layerMass_interleave (a b : Layers) :
    layerMass (RingChildKeyRecovery.interleave a b) = layerMass a + layerMass b := by
  induction a generalizing b with
  | nil => simp [RingChildKeyRecovery.interleave,layerMass]
  | cons a as ih =>
    cases b with
    | nil => simp [RingChildKeyRecovery.interleave,layerMass]
    | cons b bs =>
      have h := ih bs
      simp only [RingChildKeyRecovery.interleave,layerMass,List.map_cons,List.sum_cons,rowMass_append] at h ⊢
      omega

private theorem forest_mass (bs : List Branch) :
    layerMass ((bs.map Branch.levels).foldr RingChildKeyRecovery.interleave []) =
      (bs.map (fun b => layerMass b.levels)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [layerMass_interleave,ih]

private theorem rows_mass {cs sh de : List Branch} (a : sh.Perm cs) (b : de.Perm cs) :
    layerMass (rows sh de) =
      (cs.map (fun c => 2 * mark c.value + layerMass c.levels)).sum := by
  have x := (a.map (fun c => mark c.value)).sum_eq
  have y := (b.map (fun c => mark c.value)).sum_eq
  have z := (b.map (fun c => layerMass c.levels)).sum_eq
  simp only [rows,layerMass,List.map_cons,List.sum_cons,rowMass,List.map_map,
    List.map_nil,List.sum_nil,Nat.add_zero,Function.comp_def]
  have forest := forest_mass de
  change (sh.map (fun c => mark c.value)).sum + (de.map (fun c => mark c.value)).sum +
    layerMass ((de.map Branch.levels).foldr RingChildKeyRecovery.interleave []) = _
  rw [forest,x,y,z]

  change (cs.map (fun c => mark c.value)).sum + (cs.map (fun c => mark c.value)).sum +
    (cs.map (fun c => layerMass c.levels)).sum =
    (cs.map (fun c => 2 * mark c.value + layerMass c.levels)).sum
  clear * - cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons,List.sum_cons]; omega

/-- A pure count from the serialized word: non-root publications occur in
both shallow and deep rows, while the root row occurs only once. -/
def serializedPopulation (w : Word) : Nat :=
  (rowMass w + rowMass (w.take 1)) / 2

private theorem join_length (v : Option RingNestedActivePair.Labels) (parts : List (Branch × List Hit)) :
    (RingRetainedReferenceGroup.joinHits v parts).length =
      mark (RingNestedActivePair.unit (v.map Prod.fst)) + (parts.map (fun p => p.2.length)).sum := by
  unfold RingRetainedReferenceGroup.joinHits
  simp only [List.length_append,List.length_flatMap]
  have root : (((RingNestedActivePair.upper (v.map Prod.fst)).map (Hit.mk [])).toList).length =
      mark (RingNestedActivePair.unit (v.map Prod.fst)) := by
    rcases v with _ | ⟨(_|_),(_|_)⟩ <;> rfl
  change (((RingNestedActivePair.upper (v.map Prod.fst)).map (Hit.mk [])).toList).length +
    (parts.map (fun p => (p.2.map (fun h => {h with path := p.1.deep :: h.path})).length)).sum = _
  rw [root]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  exact List.length_map _

private theorem mapM_sum {α β γ : Type} {xs : List α} {ys : List β} {zs : List γ}
    {f : α → Option β} {g : α → Option γ} (a : xs.mapM f = some ys) (b : xs.mapM g = some zs)
    (u : β → Nat) (v : γ → Nat)
    (same : ∀ c ∈ xs, ∀ {y z}, f c = some y → g c = some z → u y = v z) :
    (ys.map u).sum = (zs.map v).sum := by
  induction xs generalizing ys zs with
  | nil => cases a; cases b; rfl
  | cons c cs ih =>
    rw [List.mapM_cons] at a b
    obtain ⟨y,hy,more⟩ := Option.bind_eq_some_iff.mp a
    obtain ⟨ys,hys,out⟩ := Option.bind_eq_some_iff.mp more
    obtain ⟨z,hz,more⟩ := Option.bind_eq_some_iff.mp b
    obtain ⟨zs,hzs,out'⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    obtain rfl := Option.some.inj out'
    simp only [List.map_cons,List.sum_cons]
    rw [same c List.mem_cons_self hy hz,
      ih hys hzs (fun d hd => same d (List.mem_cons_of_mem _ hd))]

private theorem doubled {i r q xs} (listing : Listing i r q xs) {b}
    (reading : Reading i r false q b) :
    2 * xs.length = 2 * mark b.value + layerMass b.levels := by
  induction listing generalizing b with
  | @node q v parts seen physical lookup complete rank below ih =>
    cases reading with
    | @node _ k labs cs sh de key found physical' get all sub first second =>
      obtain rfl := Option.some.inj (found.symm.trans seen)
      have sums := mapM_sum complete all (fun p => 2 * p.2.length)
        (fun c => 2 * mark c.value + layerMass c.levels) (by
          intro c hc p d hp hd
          exact ih c hc hp (sub c hc hd))
      rw [join_length]
      change 2 * (_ + _) = 2 * mark (RingNestedActivePair.unit (labs.map Prod.fst)) + layerMass (rows sh de)
      rw [rows_mass first.perm second.perm,← sums]
      have distribute : (parts.map (fun p => 2 * p.2.length)).sum =
          2 * (parts.map (fun p => p.2.length)).sum := by
        clear * - parts
        induction parts with
        | nil => rfl
        | cons p ps ih => simp only [List.map_cons,List.sum_cons]; omega
      omega

theorem Listing.serializedPopulation {i r q xs} (listing : Listing i r q xs) {b}
    (reading : Reading i r false q b) : xs.length = serializedPopulation b.word := by
  have h := doubled listing reading
  unfold RingUnitWordPopulation.serializedPopulation
  simp only [Branch.word,List.take_succ_cons,List.take_zero]
  have mass : rowMass ([b.value] :: b.levels.flatten) = mark b.value + layerMass b.levels := by
    simp only [rowMass,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,Nat.add_zero]
    have eqn : ((b.levels.flatten.map (fun r => (r.map mark).sum))).sum = layerMass b.levels := by
      simp only [layerMass,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def]
      rfl
    exact congrArg (mark b.value + ·) eqn
  rw [mass]
  have root : rowMass [[b.value]] = mark b.value := by simp [rowMass]
  rw [root]
  have total : mark b.value + layerMass b.levels + mark b.value = 2 * xs.length := by omega
  rw [total]
  omega

theorem Listing.word_length_eq {i : Input} {r : Reader i} {q : Arm i} {xs : List Hit}
    (left : Listing i r q xs) {j : Input} {v : Reader j} {p : Arm j} {ys : List Hit}
    (right : Listing j v p ys) {a b : Branch} (ra : Reading i r false q a)
    (rb : Reading j v false p b) (tie : a.word = b.word) : xs.length = ys.length := by
  rw [Listing.serializedPopulation left ra,Listing.serializedPopulation right rb,tie]

/-- Every independent listing has the same total population under equal
through-4a priorities; no length equality is supplied as a premise. -/
theorem Listing.length_eq {i : Input} {r : Reader i} {q : Arm i} {xs : List Hit}
    (left : Listing i r q xs) {j : Input} {v : Reader j} {p : Arm j} {ys : List Hit}
    (right : Listing j v p ys) {a b : Branch} (ra : Reading i r false q a)
    (rb : Reading j v false p b) (tie : a.deep = b.deep) : xs.length = ys.length := by
  simpa using (RingReferenceGroupTransport.Listing.paths_perm left right ra rb tie).length_eq

end TetraStereo.Engine.RingUnitWordPopulation

assert_kernel_only TetraStereo.Engine.RingUnitWordPopulation.stream_word
assert_kernel_only TetraStereo.Engine.RingUnitWordPopulation.word_population_eq
assert_kernel_only TetraStereo.Engine.RingUnitWordPopulation.Listing.length_eq

assert_kernel_only TetraStereo.Engine.RingUnitWordPopulation.Listing.serializedPopulation

assert_kernel_only TetraStereo.Engine.RingUnitWordPopulation.Listing.word_length_eq
