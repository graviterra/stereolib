import TetraStereo.Engine.RingRule5Shape

/-! # Exchanging the reference in a full molecular walk

Keep each sphere's path multiset. Exchanging the reference complements every
occupied step and sorts the entire sphere again, including across parents. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingRule5SeedExchange
open OneCenter RingStereoSiblingPass RingFullPathPairs
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)

/-- Record the globally sorted paths of each nonempty sphere. -/
inductive Layers {α κ : Type} [LinearOrder κ] (key : α → κ) (E : α → List α → Prop) :
    List α → List α → List (List κ) → Prop where
  | stop : Layers key E [] [] []
  | sphere {b row blocks next rest layers} (grown : List.Forall₂ E (b::row) blocks)
      (sorted : Legal key blocks.flatten next) (tail : Layers key E next rest layers) :
      Layers key E (b::row) ((b::row) ++ rest) (((b::row).map key)::layers)

theorem record {α κ : Type} [LinearOrder κ] {key : α → κ} {E : α → List α → Prop} {row out}
    (h : FullTrace key E row out) : ∃ rows, Layers key E row out rows := by
  induction h with
  | stop => exact ⟨[],.stop⟩
  | sphere grow sorted _ ih =>
    obtain ⟨rows,hs⟩ := ih
    exact ⟨_,.sphere grow sorted hs⟩

theorem flatten_layers {α κ : Type} [LinearOrder κ] {key : α → κ} {E : α → List α → Prop}
    {row out rows} (h : Layers key E row out rows) : rows.flatten = out.map key := by
  induction h with
  | stop => rfl
  | sphere _ _ _ ih => simp only [List.flatten_cons,List.map_append,ih]

def flipStep (w : List Word) := stepKey (stripBit w) ((bitOf [w]).map (!·))
def flipPath (p : Path) := p.map flipStep

theorem flip_step (k : List Word) (m : Option Bool) :
    flipStep (stepKey k m) = stepKey k (m.map (!·)) := by
  unfold flipStep
  rw [stripBit_step,show bitOf [stepKey k m] = m from bitOf_snoc [] k m]

def switch {i : Input} (v : FullVisit i) : FullVisit i := ⟨v.cursor,flipPath v.path⟩

private theorem opposite {i : Input} (r : Reader i) (rev : Bool) (s : RS) (q : Arm i) :
    likeAt i r rev s.swap q = (likeAt i r rev s q).map (!·) := by
  unfold likeAt
  cases handAt i r rev q with
  | none => rfl
  | some v => cases v <;> cases s <;> rfl

private theorem switch_expansion {i : Input} (o : Oracle i) (r : Reader i) (rev : Bool) (s : RS)
    {v vs} (h : o.Expansion (likeAt i r rev s) v vs) :
    o.Expansion (likeAt i r rev s.swap) (switch v) (vs.map switch) := by
  change List.Forall₂ _ (i.certified.executableLocalizedRerootChildren v.cursor) vs at h
  change List.Forall₂ _ (i.certified.executableLocalizedRerootChildren v.cursor) (vs.map switch)
  generalize i.certified.executableLocalizedRerootChildren v.cursor = kids at h ⊢
  induction h with
  | nil => exact .nil
  | cons head _ ih =>
    obtain ⟨k,hk,rfl⟩ := head
    exact .cons ⟨k,hk,by simp [switch,flipPath,flip_step,opposite]⟩ ih

def exchangeRow (row : List Path) := order id (row.map flipPath)

private theorem replay {i : Input} (o : Oracle i) (r : Reader i) (rev : Bool) (s : RS)
    {row out rows} (h : Layers FullVisit.path (o.Expansion (likeAt i r rev s)) row out rows) :
    ∀ {row' out' rows'}, Layers FullVisit.path (o.Expansion (likeAt i r rev s.swap)) row' out' rows' →
      row'.Perm (row.map switch) → (row'.map FullVisit.path).Pairwise (· ≥ ·) →
      rows' = rows.map exchangeRow := by
  induction h with
  | stop =>
    intro _ _ _ t p _
    obtain rfl := p.eq_nil
    cases t
    rfl
  | @sphere b row blocks next rest layers grown sorted tail ih =>
    intro _ _ _ t p desc
    cases t with
    | stop => simp at p
    | @sphere b' row' blocks' next' rest' layers' grown' sorted' tail' =>
      let f := pick (o.Expansion (likeAt i r rev s.swap))
      have mapped : ∀ {xs bs}, List.Forall₂ (o.Expansion (likeAt i r rev s)) xs bs →
          (xs.map switch).flatMap f = bs.flatten.map switch := by
        intro xs bs all
        induction all with
        | nil => rfl
        | cons a _ hi =>
          have eqn := pick_eq (o.expansion_functional _) (switch_expansion o r rev s a)
          simp only [List.map_cons,List.flatMap_cons,List.flatten_cons,List.map_append,hi]
          rw [show f _ = _ from eqn]
      have np : next'.Perm (next.map switch) := by
        apply sorted'.perm.trans
        rw [flatten_pick (o.expansion_functional _) grown']
        exact (List.Perm.flatMap_right f p).trans
          ((List.Perm.of_eq (mapped grown)).trans (sorted.perm.map switch).symm)
      have head : (b'::row').map FullVisit.path = exchangeRow ((b::row).map FullVisit.path) := by
        have canon := legal_order id (((b::row).map FullVisit.path).map flipPath)
        apply List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab) desc
        · simpa [exchangeRow] using canon.descending
        · apply List.Perm.trans _ canon.perm.symm
          simpa only [List.map_map,switch,Function.comp_def] using p.map FullVisit.path
      exact congrArg₂ List.cons head (ih tail' np sorted'.descending)

/-- For any two legal molecular walks with opposite seeds, each sphere of
the second is exactly the re-sorted complement of the first. -/
theorem molecular_exchange {i : Input} (o : Oracle i) (r : Reader i) (rev : Bool) (s : RS)
    (q : Arm i) {out out' rows rows'}
    (t : Layers FullVisit.path (o.Expansion (likeAt i r rev s)) [Oracle.root (likeAt i r rev s) q] out rows)
    (t' : Layers FullVisit.path (o.Expansion (likeAt i r rev s.swap)) [Oracle.root (likeAt i r rev s.swap) q] out' rows') :
    rows' = rows.map exchangeRow := by
  apply replay o r rev s t t'
  · simp [Oracle.root,switch,flipPath,flip_step,opposite]
  · simp

end TetraStereo.Engine.RingRule5SeedExchange
assert_kernel_only TetraStereo.Engine.RingRule5SeedExchange.molecular_exchange
