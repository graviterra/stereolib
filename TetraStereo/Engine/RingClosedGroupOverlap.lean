import TetraStereo.Engine.RingClosedGroupRecognition

set_option autoImplicit false
namespace TetraStereo.Engine.RingClosedGroupOverlap
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingClosedPairGroup (Group children)
open RingRetainedChemicalTrace (Key key? compareKeys)
open RingNestedActivePair (Reader)

private theorem either_pair {α : Type} [DecidableEq α] {xs : List α} {a b : α} {r : α → α → Prop}
    (sorted : xs.Pairwise r) (ha : a ∈ xs) (hb : b ∈ xs) (ne : a ≠ b) : r a b ∨ r b a := by
  have distinct : xs.idxOf a ≠ xs.idxOf b := fun h => ne ((List.idxOf_inj ha).mp h)
  have go {x y : α} (hx : x ∈ xs) (hy : y ∈ xs) (lt : xs.idxOf x < xs.idxOf y) : r x y := by
    have w := List.pairwise_iff_getElem.mp sorted _ _ (List.idxOf_lt_length_of_mem hx)
      (List.idxOf_lt_length_of_mem hy) lt
    simpa only [List.getElem_idxOf] using w
  exact (lt_or_gt_of_ne distinct).elim (fun h => .inl (go ha hb h)) (fun h => .inr (go hb ha h))

private theorem distinct {i q read} (g : Group i q read) : g.pos ≠ g.neg := by
  intro same
  have p := g.posRead
  rw [same,g.negRead] at p
  contradiction

private theorem members {i q read} (g : Group i q read) {xs : List (Arm i)} (perm : xs.Perm (children i q)) :
    g.pos ∈ xs ∧ g.neg ∈ xs := by
  have all := perm.trans g.allChildren
  exact ⟨all.mem_iff.mpr (by simp),all.mem_iff.mpr (by simp)⟩

theorem no_atomic {i q read} (g : Group i q read) : RingActivePairs.children? i q = none := by
  cases h : RingActivePairs.children? i q with
  | none => rfl
  | some xs =>
    have atomic := RingActivePairs.children_source h
    obtain ⟨p,n⟩ := members g atomic.complete
    have clash := either_pair atomic.descending p n (distinct g)
    simp [g.numbers.1,g.numbers.2.1] at clash

private def Accepted {i : Input} (a b : Arm i) := ∃ x y : Key, key? i a = some x ∧ key? i b = some y ∧
  (compareKeys x y = .gt ∨ (compareKeys x y = .eq ∧ RingRetainedSiblingOrder.SameLeaves i a b))

private theorem own_keys {i q read} (g : Group i q read) {x y : Key}
    (px : key? i g.pos = some x) (ny : key? i g.neg = some y) :
    compareKeys x y = .eq ∧ compareKeys y x = .eq := by
  have frame := i.certified.executableLocalizedRerootChildren_declarative q
  obtain ⟨pm,nm⟩ := members g (List.Perm.refl (children i q))
  have pc : (⟨g.pos.occurrence,some q.occurrence⟩ : Arm i) = g.pos :=
    LocalizedRerootCursor.ext _ rfl (frame.2 _ pm).symm
  have nc : (⟨g.neg.occurrence,some q.occurrence⟩ : Arm i) = g.neg :=
    LocalizedRerootCursor.ext _ rfl (frame.2 _ nm).symm
  have prior := g.earlierRead
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  have obs : RingRetainedChemicalTrace.keyTrace x y = g.earlier := by
    simpa [RingRetainedChemicalTrace.compareAt?,inc,RingRetainedChemicalTrace.trace?,pc,nc,px,ny] using prior
  have order : compareKeys x y = .eq := by simpa only [compareKeys,obs] using g.oneClass
  have words := order
  rw [RingRetainedChemicalPreorder.compare_word] at words
  have same := (Std.compare_eq_eq_iff_eq.mp words)
  exact ⟨order,by simp [RingRetainedChemicalPreorder.compare_word,same]⟩

private theorem not_accepted {i q read} (g : Group i q read) :
    ¬Accepted g.pos g.neg ∧ ¬Accepted g.neg g.pos := by
  have pc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp g.closed g.pos (by simp))
  have nc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp g.closed g.neg (by simp))
  have pl := beq_iff_eq.mp pc.1
  have nl := beq_iff_eq.mp nc.1
  constructor
  · rintro ⟨x,y,hx,hy,h | ⟨_,same⟩⟩
    · rw [(own_keys g hx hy).1] at h
      contradiction
    · have none : children i g.pos = [] := same.1
      simp [none] at pl
  · rintro ⟨x,y,hx,hy,h | ⟨_,same⟩⟩
    · rw [(own_keys g hy hx).2] at h
      contradiction
    · have none : children i g.neg = [] := same.1
      simp [none] at nl

/-- After its atomic fast path fails, the old molecular child collector requires
each prior tie to consist of terminal leaves. This extracts that condition from
the actual successful collector. -/
private theorem chemical_pairs {i : Input} {q : Arm i}
    {w : {xs : List (Arm i) // RingRetainedSiblingOrder.Order i q xs}}
    (fast : RingActivePairs.children? i q = none) (got : RingRetainedSiblingOrder.chemicalChildren? i q = some w) :
    w.val.Pairwise Accepted := by
  unfold RingRetainedSiblingOrder.chemicalChildren? at got
  split at got
  next es h _ => rw [fast] at h; contradiction
  next =>
    obtain ⟨_,_,nextStep⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨⟨rs,_⟩,_,out⟩ := Option.bind_eq_some_iff.mp nextStep
    dsimp only at out
    split at out
    next strict =>
      obtain rfl := Option.some.inj out
      exact List.pairwise_map.mpr (strict.imp (fun {a b} h => ⟨a.2.val,b.2.val,a.2.property,b.2.property,h⟩))
    next => contradiction

theorem no_chemical_order {i q read} (g : Group i q read) : RingRetainedSiblingOrder.chemicalChildren? i q = none := by
  cases got : RingRetainedSiblingOrder.chemicalChildren? i q with
  | none => rfl
  | some w =>
    have paired := chemical_pairs (no_atomic g) got
    obtain ⟨p,n⟩ := members g w.property.complete
    exact False.elim ((either_pair paired p n (distinct g)).elim (not_accepted g).1 (not_accepted g).2)

private theorem no_levels {i q read} (g : Group i q read) (n : Nat) :
    RingNestedActivePair.retainedLevels? i read n [q] = none := by
  cases n with
  | zero => rfl
  | succ n =>
    cases got : RingNestedActivePair.retainedLevels? i read (n+1) [q] with
    | none => rfl
    | some data =>
      unfold RingNestedActivePair.retainedLevels? at got
      obtain ⟨_,mapped,_⟩ := Option.bind_eq_some_iff.mp got
      rw [List.mapM_cons] at mapped
      obtain ⟨_,visit,_⟩ := Option.bind_eq_some_iff.mp mapped
      obtain ⟨_,order,_⟩ := Option.bind_eq_some_iff.mp visit
      obtain ⟨_,chosen,_⟩ := Option.bind_eq_some_iff.mp order
      rw [no_chemical_order g] at chosen
      contradiction

/-- The preceding nested proof cannot have returned *any* score at a proven
equal group. A strict constitutional edge contradicts the stored prior tie;
a stereo edge would have had to order the two live constitutionally tied siblings. -/
theorem nested_excluded {i f a b read} (c : RingClosedGroupTie.Certificate i f a b read) {s} :
    ¬RingNestedActivePair.Edge i f a b read s := by
  intro edge
  cases edge with
  | below old result | above old result =>
    have eqn := Option.some.inj (old.symm.trans c.earlier)
    rw [eqn,c.tie] at result
    contradiction
  | stereo p =>
    have h := p.leftRead
    rw [no_levels c.left] at h
    contradiction

theorem previous_missing {i f a b read} (c : RingClosedGroupTie.Certificate i f a b read) :
    RingClosedPairGroup.score? i f a b read = none := by
  cases got : RingClosedPairGroup.score? i f a b read with
  | none => rfl
  | some v =>
    rcases RingClosedPairGroup.issued got with old | ⟨strict,_⟩
    · exact False.elim (nested_excluded c old)
    · exact False.elim (RingClosedGroupRecognition.strict_excluded c ⟨strict⟩)

/-- All existing executable score outputs survive on every molecular input and
reader. The additional zero never overrides an earlier returned score. -/
theorem preserve_previous {i f a b read v} (prior : RingClosedPairGroup.score? i f a b read = some v) :
    RingClosedGroupTie.score? i f a b read = some v := by
  cases hit : RingClosedGroupTie.edge? i f a b read with
  | none => rwa [RingClosedGroupTie.previous_on_miss hit]
  | some c =>
    rw [previous_missing c] at prior
    contradiction

end TetraStereo.Engine.RingClosedGroupOverlap
assert_kernel_only TetraStereo.Engine.RingClosedGroupOverlap.no_atomic
assert_kernel_only TetraStereo.Engine.RingClosedGroupOverlap.no_chemical_order
assert_kernel_only TetraStereo.Engine.RingClosedGroupOverlap.nested_excluded
assert_kernel_only TetraStereo.Engine.RingClosedGroupOverlap.previous_missing
assert_kernel_only TetraStereo.Engine.RingClosedGroupOverlap.preserve_previous
