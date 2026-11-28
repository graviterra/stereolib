import TetraStereo.Examples.DecalinRootWords
import TetraStereo.Examples.DecalinEarlierTie

/-! Rank separation at a fusion root. Each spectator comparison is already
settled by Rule 1a on the native full key, for arbitrary later mark words. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinRootRanking
open Engine OneCenter
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedCentre (cursor)
open RingGroupedReport (origin)
open DecalinFrames (molecule)
open RingRetainedChemicalTrace (Word Column)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
open private member start from TetraStereo.Examples.DecalinRootWords
open private cursorKey read_valid from TetraStereo.Engine.RingAtomicProfileShape
open private project from TetraStereo.Engine.RingAtomicMetricIndependence
attribute [local instance] lexOrd

def group (r a : Nat) : Nat := if a = 1-r then 2 else if 10 ≤ a then 0 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem table : ∀ r : Fin 2,
    let ids := DecalinLigandOrder.arms r
    let words := ids.map fun a => (DecalinAuxiliary.key 15 [r.val] [a,r.val]).atomic.word
    (∀ a ∈ ids, DecalinAuxiliary.closed 15 [r.val] [a,r.val] = true) ∧
    ∀ a ∈ ids, ∀ b ∈ ids, compare (words[ids.idxOf a]?.getD []) (words[ids.idxOf b]?.getD []) =
      compare (group r.val a) (group r.val b) := by decide +kernel

theorem atomic {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (j : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root)) (a b : Fin 4) :
    compare (RingRetainedChemicalPreorder.keyFor (fr.direction a)).atomic.word
      (RingRetainedChemicalPreorder.keyFor (fr.direction b)).atomic.word =
      compare (group root.val (atom fr a)) (group root.val (atom fr b)) := by
  let r : Fin 2 := ⟨root.val,j⟩
  obtain ⟨closed,order⟩ := table r
  have atId (s : Fin 4) :
      (RingRetainedChemicalPreorder.keyFor (fr.direction s)).atomic.word =
        (DecalinAuxiliary.key 15 [root.val] [atom fr s,root.val]).atomic.word := by
    have prev := start root fr s
    have valid := RingGroupedCentre.valid fr s
    have h := DecalinAuxiliary.key_correspondence graph 15 (cursor fr s) (origin i root) rfl valid
      (by change DecalinAuxiliary.closed 15 [root.val] (DecalinLigandOrder.history (cursor fr s)) = true
          rw [prev]; exact closed _ (member graph root j fr s))
    have eq := Option.some.inj ((read_valid valid).symm.trans (RingRetainedChemicalPreorder.read_key (fr.direction s)))
    have w := congrArg (fun t : Nat × Column => t.2.word) h
    change (cursorKey i (cursor fr s)).atomic.word =
      (DecalinAuxiliary.key 15 [root.val] (DecalinLigandOrder.history (cursor fr s))).atomic.word at w
    rwa [eq,prev] at w
  rw [atId a,atId b]
  have concrete := order _ (member graph root j fr a) _ (member graph root j fr b)
  simpa [List.getElem?_map,List.getElem?_idxOf,member graph root j fr,r] using concrete

theorem spectator {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (j : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root)) {a b : Fin 4}
    {read : RingNestedActivePair.Reader i} {rev : Bool} {x y : Key}
    (rx : Reads i read rev (cursor fr a) x) (ry : Reads i read rev (cursor fr b) y)
    (different : group root.val (atom fr a) ≠ group root.val (atom fr b)) (m n : Word) :
    compare (trialKey x m) (trialKey y n) =
      compare (group root.val (atom fr a)) (group root.val (atom fr b)) := by
  obtain ⟨u,hu⟩ := RingFullPathConstitution.through_extends fr rx
  obtain ⟨v,hv⟩ := RingFullPathConstitution.through_extends fr ry
  have ord := atomic graph root j fr a b
  simp only [trialKey,hu,hv,RingFullPathConstitution.word,RingRetainedChemicalPreorder.orderWord,
    List.cons_append,List.compare_cons_cons,ord]
  cases h : compare (group root.val (atom fr a)) (group root.val (atom fr b)) with
  | lt => rfl
  | gt => rfl
  | eq => exact (different (compare_eq_iff_eq.mp h)).elim

open DecalinRootWords (routeAtom publicRead)
open DecalinLigandOrder (ranked arms)
open LocalizedGenericMarkedRecalculation (readback?)
open private slot_injective from TetraStereo.Engine.RingAtomicFramePriority

private def handAt (h : RS) (s : Fin 2) := if s.val = 0 then h else h.swap

private theorem positions : ∀ (r : Fin 2) (h : RS), ∀ a ∈ arms r, ∀ b ∈ arms r,
    (group r.val a ≠ group r.val b →
      compare (group r.val a) (group r.val b) = compare ((ranked r h).idxOf b) ((ranked r h).idxOf a)) ∧
    (a ≠ b → group r.val a = group r.val b → ∃ s t : Fin 2,
      a = routeAtom r s ∧ b = routeAtom r t ∧ s ≠ t) := by decide +kernel

private theorem exchanged : ∀ (r s t : Fin 2), s ≠ t →
    DecalinPathSwap.exchange (routeAtom r s) = routeAtom r t := by decide +kernel

private theorem signed_order : ∀ (r s t : Fin 2) (h : RS), s ≠ t →
    let x := RingFullPathTrialReadings.bitWord [handAt h s == .R]
    let y := RingFullPathTrialReadings.bitWord [handAt h t == .R]
    compare [x] [y] ≠ .eq ∧ compare [x] [y] =
      compare ((ranked r h).idxOf (routeAtom r t)) ((ranked r h).idxOf (routeAtom r s)) := by decide +kernel

private theorem fields {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (j : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root))
    (a : Fin 4) (s : Fin 2) (id : atom fr a = routeAtom ⟨root.val,j⟩ s)
    (h : RS) (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (DecalinFrames.junctionRow (1-root.val)) = some h)
    (rev : Bool) (k : Key) (got : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr a) = some k) :
    k.bestFourB = [true] ∧ k.fixedR = [handAt (if rev then h.swap else h) s == .R] := by
  let value := handAt (if rev then h.swap else h) s
  have R := DecalinRootWords.public_long_word graph geom root j fr a s id rev h sense [] .R
  have S := DecalinRootWords.public_long_word graph geom root j fr a s id rev h sense [] .S
  have F := DecalinRootWords.public_long_word graph geom root j fr a s id rev h sense [.lowercase] .R
  change RingFullPathPairs.pairs? _ _ _ _ _ = some [value == .R] at R
  change RingFullPathPairs.pairs? _ _ _ _ _ = some [value == .S] at S
  change RingFullPathRule5.word? _ _ _ _ _ = some [value == .R] at F
  unfold RingFullPathEligibility.key? at got
  rw [R,S,F] at got
  cases u : RingRetainedStereoRefinement.priority i (publicRead i root) rev [] (cursor fr a) <;>
    cases l : RingRetainedStereoRefinement.priority i (publicRead i root) rev [.lowercase] (cursor fr a) <;>
    simp [u,l] at got
  subst k
  exact ⟨by cases value <;> rfl,rfl⟩

/-- Strict native priority at both fusion roots on either geometry. This compares
the completed public keys from every actual slot, including self-comparisons. -/
theorem frame_order {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (j : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root))
    (h : RS) (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (DecalinFrames.junctionRow (1-root.val)) = some h)
    (rev : Bool) (ks : Fin 4 → Key)
    (got : RingFullPathPublication.keys? fr (publicRead i root) rev = some ks) (a b : Fin 4) :
    compare (trialKey (ks a) []) (trialKey (ks b) []) =
      compare ((ranked ⟨root.val,j⟩ (if rev then h.swap else h)).idxOf (atom fr b))
        ((ranked ⟨root.val,j⟩ (if rev then h.swap else h)).idxOf (atom fr a)) := by
  let r : Fin 2 := ⟨root.val,j⟩
  let g := if rev then h.swap else h
  have key (s : Fin 4) : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr s) = some (ks s) :=
    RingActivePairReport.four_at got s
  have reads (s : Fin 4) : Reads i (publicRead i root) rev (cursor fr s) (ks s) := by
    obtain ⟨k,hk,exactK⟩ := RingFullPathEligibility.key_exact (RingChemicalGraphProof.ready geom _)
      rev (cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact (exactK _).mpr (Option.some.inj ((key s).symm.trans hk))
  have pos := positions r g _ (member graph root j fr a) _ (member graph root j fr b)
  by_cases same : atom fr a = atom fr b
  · have eq : a = b := slot_injective fr (Subtype.ext (Fin.ext (by
        simpa only [RingAtomicFramePriority.slotNeighbor_val] using same)))
    subst b
    simp
  by_cases diff : group root.val (atom fr a) ≠ group root.val (atom fr b)
  · exact (spectator graph root j fr (reads a) (reads b) diff [] []).trans (pos.1 diff)
  obtain ⟨s,t,A,B,ne⟩ := pos.2 same (of_not_not diff)
  have cross : DecalinPathSwap.exchange (atom fr a) = atom fr b := by rw [A,B,exchanged r s t ne]
  obtain ⟨x,y,hx,hy,early,lower⟩ := DecalinEarlierTie.earlier graph geom root j fr a b cross rev
  have ex : x = ks a := Option.some.inj (hx.symm.trans (key a))
  have ey : y = ks b := Option.some.inj (hy.symm.trans (key b))
  subst x
  subst y
  obtain ⟨a4,a5⟩ := fields graph geom root j fr a s A h sense rev _ (key a)
  obtain ⟨b4,b5⟩ := fields graph geom root j fr b t B h sense rev _ (key b)
  obtain ⟨strict,dir⟩ := signed_order r s t g ne
  simp only [trialKey,early,lower,a4,b4,a5,b5,List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then]
  change _ = compare ((ranked r g).idxOf (atom fr b)) ((ranked r g).idxOf (atom fr a))
  rw [A,B,←dir]
  cases c : compare [RingFullPathTrialReadings.bitWord [handAt g s == .R]]
      [RingFullPathTrialReadings.bitWord [handAt g t == .R]] <;> simp_all [g]

end TetraStereo.Examples.DecalinRootRanking
assert_kernel_only TetraStereo.Examples.DecalinRootRanking.spectator
assert_kernel_only TetraStereo.Examples.DecalinRootRanking.frame_order
