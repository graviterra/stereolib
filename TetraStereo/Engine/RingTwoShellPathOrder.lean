import TetraStereo.Engine.RingSecondShellDecision

/-! A strict difference between two physical two-shell prefixes controls the
order of any two signed donor paths whose first different step uses those
directions. Stereo passes and reference hands can vary on the two paths. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingTwoShellPathOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingRetainedChemicalPreorder (Site Direction keyFor read_key orderWord)
open RingStereoSiblingPass (Branch)
open RingRetainedStereoRefinement (Observation Derives)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingNestedActivePair (Reader)
open RingFullPathPairs (stepKey)

private theorem rank_prefix {i : Input} {f : Site i} (a : Direction i f) {r : Reader i} {rev : Bool}
    (stages : List Observation) {x : Branch} (d : Derives i r rev stages ⟨a.val,some f⟩ x) :
    ∃ suffix, x.deep = orderWord (keyFor a) ++ suffix := by
  induction stages generalizing x with
  | nil =>
    obtain ⟨k,hk,prior⟩ := RingRetainedUnitPass.Reading.constitution d
    have same := Option.some.inj (hk.symm.trans (read_key a))
    exact ⟨[x.word],congrArg (fun p => p ++ [x.word]) (prior.trans (congrArg orderWord same))⟩
  | cons stage stages ih =>
    cases d with
    | node prev _ _ _ _ _ _ =>
      obtain ⟨suffix,h⟩ := ih prev
      exact ⟨_,(congrArg (fun p => p ++ [_]) h).trans (List.append_assoc ..)⟩

private theorem append_lt_of_fixed {α : Type} [LinearOrder α] {a b : List α}
    (equalSize : a.length = b.length) (less : a < b) (xs ys : List α) : a ++ xs < b ++ ys := by
  induction a generalizing b with
  | nil =>
    have : b = [] := List.length_eq_zero_iff.mp equalSize.symm
    subst b
    exact (lt_irrefl _ less).elim
  | cons x a ih =>
    cases b with
    | nil => simp at equalSize
    | cons y b =>
      rcases List.cons_lt_cons_iff.mp less with h | ⟨rfl,h⟩
      · exact List.cons_lt_cons_iff.mpr (.inl h)
      · exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih (by simpa using equalSize) h⟩)

/-- At every refinement stage a strict two-shell order fixes the complete
earlier-rule edge priority of the two directions. -/
private theorem ranked_append {i : Input} {f : Site i} (a b : Direction i f)
    (order : RingSecondShellDecision.prefixFor i f a < RingSecondShellDecision.prefixFor i f b)
    {r t : Reader i} {rev mir : Bool} {sa sb : List Observation} {x y : Branch}
    (left : RingRetainedStereoRefinement.priority i r rev sa ⟨a.val,some f⟩ = some x)
    (right : RingRetainedStereoRefinement.priority i t mir sb ⟨b.val,some f⟩ = some y) :
    ∀ (p q : List Word), x.deep ++ p < y.deep ++ q := by
  intro p q
  rw [RingSecondShellDecision.prefixFor_physical,RingSecondShellDecision.prefixFor_physical] at order
  have less := RingAllLigandTwoShell.word_lt_of_prefix a b order
  obtain ⟨u,hu⟩ := rank_prefix a sa (RingRetainedStereoRefinement.source _ _ left)
  obtain ⟨v,hv⟩ := rank_prefix b sb (RingRetainedStereoRefinement.source _ _ right)
  rw [hu,hv,List.append_assoc,List.append_assoc]
  exact append_lt_of_fixed (a := orderWord (keyFor a)) (b := orderWord (keyFor b)) rfl less _ _

theorem rank_lt {i : Input} {f : Site i} (a b : Direction i f)
    (order : RingSecondShellDecision.prefixFor i f a < RingSecondShellDecision.prefixFor i f b)
    {r t : Reader i} {rev mir : Bool} {sa sb : List Observation} {x y : Branch}
    (left : RingRetainedStereoRefinement.priority i r rev sa ⟨a.val,some f⟩ = some x)
    (right : RingRetainedStereoRefinement.priority i t mir sb ⟨b.val,some f⟩ = some y) :
    x.deep < y.deep := by simpa using ranked_append a b order left right [] []

/-- The complete signed paths keep a strict graph order even when their
remaining edges, reference bits, readers and lists of refinement passes differ. -/
theorem path_lt {i : Input} {f : Site i} (a b : Direction i f)
    (order : RingSecondShellDecision.prefixFor i f a < RingSecondShellDecision.prefixFor i f b)
    {r t : Reader i} {rev mir : Bool} {sa sb : List Observation} {x y : Branch}
    (left : RingRetainedStereoRefinement.priority i r rev sa ⟨a.val,some f⟩ = some x)
    (right : RingRetainedStereoRefinement.priority i t mir sb ⟨b.val,some f⟩ = some y)
    (head tailA tailB : Path) (bitA bitB : Option Bool) :
    head ++ stepKey x.deep bitA :: tailA < head ++ stepKey y.deep bitB :: tailB := by
  have step : stepKey x.deep bitA < stepKey y.deep bitB := ranked_append a b order left right _ _
  induction head with
  | nil => exact List.cons_lt_cons_iff.mpr (.inl step)
  | cons _ _ ih => exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih⟩)

end TetraStereo.Engine.RingTwoShellPathOrder
assert_kernel_only TetraStereo.Engine.RingTwoShellPathOrder.path_lt
