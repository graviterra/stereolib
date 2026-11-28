import TetraStereo.Examples.AntipodalCyclohexaneWords
import TetraStereo.Examples.HexachlorocyclohexanePublicStore
import TetraStereo.Examples.HexachlorocyclohexaneSignedOrder

/-! A finite written-graph check for the order of molecular observations.
At a given distance there may be silent visits and arbitrarily many copies
of the same observation. The observation may change at every distance. -/
set_option autoImplicit false
namespace TetraStereo.Examples.HexachlorocyclohexanePublicWords
open OneCenter Engine
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingFullPathPairs (Oracle FullVisit FullTrace)
open AntipodalCyclohexaneHands.HistoryPriority (GraphFacts)
open AntipodalCyclohexaneWords (children histories Rooted expansion_histories)
open DecalinAuxiliary (History history)
open private block_paths from TetraStereo.Examples.DecalinLigandOrder
open private flatMap_perm from TetraStereo.Engine.RingFullPathPairs

/-- A successful result lists every observation, including repetitions.
Running out of depth with a nonempty frontier fails. -/
def layerWord? {α β : Type} [DecidableEq β] (kids : α → List α) (emit : α → Option β) :
    Nat → List α → Option (List β)
  | 0, row => if row.isEmpty then some [] else none
  | n+1, row => do
    let head := row.filterMap emit
    guard (head.Pairwise (· = ·))
    let tail ← layerWord? kids emit n (row.flatMap kids)
    return head ++ tail

private theorem perm_uniform {β : Type} {xs ys : List β} (perm : xs.Perm ys)
    (same : ys.Pairwise (· = ·)) : xs = ys := by
  cases ys with
  | nil => exact perm.eq_nil
  | cons b bs =>
    have all : ∀ y ∈ b::bs, y = b := by
      intro y hy
      exact (List.mem_cons.mp hy).elim id (fun mem => ((List.pairwise_cons.mp same).1 y mem).symm)
    have right := List.eq_replicate_iff.mpr ⟨rfl,all⟩
    exact (List.eq_replicate_iff.mpr ⟨perm.length_eq,fun y hy => all y (perm.mem_iff.mp hy)⟩).trans right.symm

private theorem empty_word {α β : Type} [DecidableEq β] (kids : α → List α) (emit : α → Option β) :
    ∀ n, layerWord? kids emit n [] = some [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [layerWord?,ih]

/-- A checked sequence is shared by all complete ranked traces, regardless
of which order the ranking assigns to visits within any one sphere. -/
theorem trace_word {α β γ κ : Type} [DecidableEq γ] [LinearOrder κ] {E : α → List α → Prop}
    {key : α → κ} {proj : α → β} {kids : β → List β} {D : α → Prop}
    (step : ∀ x, D x → ∀ ys, E x ys → (ys.map proj).Perm (kids (proj x)) ∧ ∀ y ∈ ys, D y)
    (emit : β → Option γ) {xs out : List α} (trace : FullTrace key E xs out) (inside : ∀ x ∈ xs, D x) :
    ∀ n row word, (xs.map proj).Perm row → layerWord? kids emit n row = some word →
      out.filterMap (fun x => emit (proj x)) = word ∧ ∀ x ∈ out, D x := by
  induction trace with
  | stop =>
    intro n row word perm ok
    obtain rfl := perm.symm.eq_nil
    rw [empty_word] at ok
    exact ⟨Option.some.inj ok,by simp⟩
  | @sphere b row blocks next later expanded sorted _ ih =>
    intro n actual word roots ok
    have nonempty : actual.isEmpty = false := by
      cases actual with
      | nil => have := roots.eq_nil; contradiction
      | cons => rfl
    cases n with
    | zero => simp [layerWord?,nonempty] at ok
    | succ n =>
      obtain ⟨paths,sub⟩ := block_paths expanded inside step
      have nextPaths := ((sorted.perm.map proj).trans paths).trans (flatMap_perm kids roots)
      by_cases same : (actual.filterMap emit).Pairwise (· = ·)
      · cases tail : layerWord? kids emit n (actual.flatMap kids) with
        | none => simp [layerWord?,same,tail] at ok
        | some rest =>
          have final : actual.filterMap emit ++ rest = word := by simpa [layerWord?,same,tail] using ok
          have eq := perm_uniform (roots.filterMap emit) same
          obtain ⟨suffix,valid⟩ := ih (fun x hx => sub x (sorted.perm.mem_iff.mp hx)) n _ _ nextPaths tail
          simp only [List.filterMap_map,Function.comp_def] at eq
          refine ⟨?_,fun x hx => (List.mem_append.mp hx).elim (inside x) (valid x)⟩
          rw [List.filterMap_append,eq,suffix,final]
      · simp [layerWord?,same] at ok

/-- A source emitter may interpret each graph observation at the current
geometry and reference seed. Only its graph incidence and emissions are required. -/
theorem molecular_word {γ : Type} [DecidableEq γ] {m : RawMolecule} {i : Input}
    (raw : i.molecule = m) (written : GraphFacts m) (o : Oracle i) (bit : Arm i → Option Bool)
    (emit : History → Option γ) (read : γ → Bool) (root : i.certified.Atom)
    (q : Arm i) (p : Site i) (prev : q.previous? = some p)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = root)
    (seen : ∀ c : Arm i, c.occurrence.val.root = root → bit c = (emit (history c.occurrence)).map read)
    (n : Nat) (word : List γ) (ok : layerWord? (children m) (fun e => emit e.2) n [histories q] = some word)
    {w : List Bool} (src : o.Source bit q w) : w = word.map read := by
  obtain ⟨out,walk,rfl⟩ := src
  have initial : Rooted root (Oracle.root bit q) := ⟨valid,on,p,prev⟩
  obtain ⟨eq,dom⟩ := trace_word (expansion_histories raw written o bit root) (fun e => emit e.2) walk
    (by simpa using initial) n [histories q] word (.refl _) ok
  rw [←eq,List.map_filterMap]
  exact List.filterMap_congr fun x hx => seen _ (dom _ hx).2.1

open BlueBookHexachlorocyclohexane (molecule site)
open HexachlorocyclohexanePublicStore (tag? handAt_tag)
open HexachlorocyclohexaneFamily (forwardSite fixedFrame hand directionHand)
open HexachlorocyclohexaneSignedOrder (signedWord)
open AntipodalCyclohexaneWords (EdgeHistory publicRead)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open LocalizedGenericMarkedRecalculation (readback?)
open private start from TetraStereo.Examples.DecalinRootWords
open private rawFacts from TetraStereo.Examples.HexachlorocyclohexanePublicStore

private def first (r : Fin 6) (cw : Bool) : EdgeHistory := ([r.val],[site r cw 1,r.val])

set_option maxRecDepth 100000 in
private theorem tags (r : Fin 6) (cw : Bool) :
    layerWord? (children molecule) (fun e => tag? r e.2) 8 [first r cw] =
      some ((List.finRange 5).map (fun k => (cw,k))) := by
  fin_cases r <;> cases cw <;> decide +kernel

/-- Each ring arm emits the five other carbons in traversal order for every
legal stage ranking, either seed, and either geometry reading. -/
theorem ring_word {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (s : Fin 4) (cw : Bool) (id : atom fr s = site r cw 1) (rev : Bool) (p : Fin 32)
    (signs : ∀ k, readback? (RingWrittenPHReadings.geometry i.spatial)
      (fixedFrame (forwardSite r k)) = some (hand p k))
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i (publicRead i root) rev os seed (cursor fr s) =
      some (signedWord p cw rev seed) := by
  let o := RingFullPathPairs.stage i (publicRead i root) rev os
  let bit := RingFullPathPairs.likeAt i (publicRead i root) rev seed
  let read (t : Bool × Fin 5) := (if rev then (directionHand p t.1 t.2).swap else directionHand p t.1 t.2) == seed
  have seen (c : Arm i) (on : c.occurrence.val.root = root) : bit c = (tag? r (history c.occurrence)).map read := by
    change (RingFullPathPairs.handAt i _ rev c).map _ = _
    rw [handAt_tag graph geom r atRoot c on p signs rev]
    cases tag? r (history c.occurrence) <;> rfl
  have firstEdge : histories (cursor fr s) = first r cw := by
    change ([root.val], DecalinLigandOrder.history (cursor fr s)) = _
    rw [start root fr s,id,atRoot]
    rfl
  have cert := tags r cw
  rw [←firstEdge] at cert
  obtain ⟨w,hit,src⟩ := o.source_exact (f := origin i root) bit
    (RingOccurrenceStereo.rank_total (RingChemicalGraphProof.ready geom _) rev os)
    (cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  have eqn := molecular_word graph rawFacts o bit (tag? r) read root _ (origin i root) rfl
    (RingGroupedCentre.valid fr s) (fr.direction s).property.1 seen 8 _ cert ((src w).mpr rfl)
  exact hit.trans (congrArg some (eqn.trans (by simp [List.map_map,signedWord,read,Function.comp_def])))

end TetraStereo.Examples.HexachlorocyclohexanePublicWords
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicWords.molecular_word
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicWords.ring_word
