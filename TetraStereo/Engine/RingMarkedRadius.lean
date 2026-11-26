import TetraStereo.Engine.RingMarkedDistanceOrder

/-! Nearest marked distance is decisive unless both finite radii coincide. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedRadius
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRule5Shape (Valid On)
open RingGroupedMark (Reading bit)
open RingRetainedChemicalTrace (Word)
open RingFullPathTrialReadings (trialKey)
open RingMarkedDistanceOrder (hitsAt hitsAt_iff)
open private spheres sphere_get sphere_flat from TetraStereo.Engine.RingMarkedDistanceOrder
attribute [local instance] lexOrd

/-- The minimum retained-child distance to any occurrence of the selected atom.
`none` denotes infinity. No stereochemical reader or priority sort is used. -/
def radius (i : Input) (atom : Nat) (q : Arm i) : Option Nat :=
  (List.range (i.certified.localizedRerootCursorBudget q + 1)).find? (hitsAt i atom q)

theorem radius_some {i : Input} (atom : Nat) (q : Arm i) (d : Nat) :
    radius i atom q = some d ↔ hitsAt i atom q d = true ∧
      d ≤ i.certified.localizedRerootCursorBudget q ∧ ∀ j < d, hitsAt i atom q j = false := by
  simp only [radius,List.find?_eq_some_iff_getElem,List.length_range,List.getElem_range]
  constructor
  · rintro ⟨hit,j,bound,eqn,clear⟩
    subst j
    exact ⟨hit,by omega,fun j hj => by simpa using clear j hj⟩
  · rintro ⟨hit,bound,clear⟩
    exact ⟨hit,d,by omega,rfl,fun j hj => by simpa using clear j hj⟩

/-- The operational cursor budget makes the finite scan exhaustive. -/
theorem radius_none {i : Input} (atom : Nat) (q : Arm i) (valid : Valid q) :
    radius i atom q = none ↔ ∀ d, hitsAt i atom q d = false := by
  simp only [radius,List.find?_eq_none,List.mem_range,Bool.not_eq_true]
  constructor
  · intro clear d
    by_cases small : d < i.certified.localizedRerootCursorBudget q + 1
    · exact clear d small
    · cases h : hitsAt i atom q d with
      | false => rfl
      | true =>
        obtain ⟨t,path,_⟩ := (hitsAt_iff atom q d).mp h
        have bound := (path.root_and_budget valid).2.2
        omega
  · intro clear d _; exact clear d

/-- A smaller finite radius wins against a larger radius or an absent atom. -/
theorem smaller_wins {i f r rev a b atom x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r atom b y) {d : Nat}
    (ra : radius i atom a = some d)
    (later : radius i atom b = none ∨ ∃ e, radius i atom b = some e ∧ d < e) :
    compare (trialKey k x.word) (trialKey k y.word) = .gt := by
  apply RingMarkedDistanceOrder.nearer_wins ready va vb oa ob ka kb ma mb
    ((hitsAt_iff atom a d).mp ((radius_some atom a d).mp ra).1)
  intro j hj t path atAtom
  have hit := (hitsAt_iff atom b j).mpr ⟨t,path,atAtom⟩
  rcases later with absent | ⟨e,rb,less⟩
  · have zero := (radius_none atom b vb).mp absent j
    simp [zero] at hit
  · have zero := ((radius_some atom b e).mp rb).2.2 j (by omega)
    simp [zero] at hit

private theorem all_zero {i r atom q b} (read : Reading i r atom q b)
    (absent : ∀ d, hitsAt i atom q d = false) : ∀ z ∈ b.word.flatten, z = 0 := by
  intro z hz
  rw [← sphere_flat] at hz
  obtain ⟨row,hrow,hz⟩ := List.mem_flatten.mp hz
  obtain ⟨d,hd⟩ := List.mem_iff_getElem?.mp hrow
  have present : z ∈ RingMarkedDistanceOrder.atSphere b d := by
    rw [← sphere_get]
    simpa only [List.getD_eq_getElem?_getD,hd,Option.getD_some] using hz
  obtain ⟨t,path,rfl⟩ := (RingMarkedDistanceOrder.sphere_support read d z).mp present
  have noAtom : t.occurrence.val.node.current?.map Fin.val ≠ some atom := by
    intro equal
    have hit := (hitsAt_iff atom q d).mpr ⟨t,path,equal⟩
    simp [absent d] at hit
  simp [bit,noAtom]

private theorem zero_eq {xs ys : List Nat} (len : xs.length = ys.length)
    (a : ∀ z ∈ xs, z = 0) (b : ∀ z ∈ ys, z = 0) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | rfl | contradiction
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys =>
      exact congrArg₂ List.cons ((a x List.mem_cons_self).trans (b y List.mem_cons_self).symm)
        (ih (Nat.succ.inj len) (fun z hz => a z (.tail _ hz)) (fun z hz => b z (.tail _ hz)))

/-- Ordinary tied arms remain tied when neither retained tree contains the atom. -/
theorem absent_tie {i f r rev a b atom x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r atom b y)
    (ra : radius i atom a = none) (rb : radius i atom b = none) :
    compare (trialKey k x.word) (trialKey k y.word) = .eq := by
  rw [RingMarkedDistanceOrder.trial_compare ready va vb oa ob ka kb ma mb]
  have lengths := RingMarkedDistanceOrder.widths ready va vb oa ob ka kb ma mb
  have len : x.word.flatten.length = y.word.flatten.length := by
    simpa only [List.length_flatten] using congrArg List.sum lengths
  rw [zero_eq len (all_zero ma ((radius_none atom a va).mp ra))
    (all_zero mb ((radius_none atom b vb).mp rb))]
  exact Std.ReflCmp.compare_self

/-- Distance-only prediction, with finite radii preferred and absence treated as infinity. -/
def rankByRadius : Option Nat → Option Nat → Ordering
  | none,none => .eq
  | some _,none => .gt
  | none,some _ => .lt
  | some a,some b => compare b a

/-- Any departure from rank-by-distance-only is confined to two equally near,
actually present occurrences. Neither unequal radii nor two absent atoms can disagree. -/
theorem distance_disagreement {i f r rev a b atom x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r atom b y)
    (different : compare (trialKey k x.word) (trialKey k y.word) ≠
      rankByRadius (radius i atom a) (radius i atom b)) :
    ∃ d, radius i atom a = some d ∧ radius i atom b = some d := by
  have flip : ∀ {l t : Word}, compare (trialKey k t) (trialKey k l) = .gt →
      compare (trialKey k l) (trialKey k t) = .lt := by
    intro l t h
    rw [Std.OrientedCmp.eq_swap (cmp := compare),h]
    rfl
  cases ra : radius i atom a with
  | none =>
    cases rb : radius i atom b with
    | none =>
      simp only [ra,rb,rankByRadius] at different
      exact False.elim (different (absent_tie ready va vb oa ob ka kb ma mb ra rb))
    | some e =>
      simp only [ra,rb,rankByRadius] at different
      exact False.elim (different
        (flip (smaller_wins ready vb va ob oa kb ka mb ma rb (Or.inl ra))))
  | some d =>
    cases rb : radius i atom b with
    | none =>
      simp only [ra,rb,rankByRadius] at different
      exact False.elim (different
        (smaller_wins ready va vb oa ob ka kb ma mb ra (Or.inl rb)))
    | some e =>
      simp only [ra,rb,rankByRadius] at different
      rcases lt_trichotomy d e with less | equal | greater
      · have win := smaller_wins ready va vb oa ob ka kb ma mb ra (Or.inr ⟨e,rb,less⟩)
        exact False.elim (different (by simpa only [Nat.compare_eq_gt.mpr less] using win))
      · exact ⟨d,rfl,congrArg some equal.symm⟩
      · have win := flip (smaller_wins ready vb va ob oa kb ka mb ma rb (Or.inr ⟨d,ra,greater⟩))
        exact False.elim (different (by simpa only [Nat.compare_eq_lt.mpr greater] using win))
/-- Every unequal-radius comparison is exactly the distance-only prediction. -/
theorem compare_of_distinct_radii {i f r rev a b atom x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r atom b y)
    (different : radius i atom a ≠ radius i atom b) :
    compare (trialKey k x.word) (trialKey k y.word) =
      rankByRadius (radius i atom a) (radius i atom b) := by
  by_contra h
  obtain ⟨d,ha,hb⟩ := distance_disagreement ready va vb oa ob ka kb ma mb h
  exact different (ha.trans hb.symm)
end TetraStereo.Engine.RingMarkedRadius
assert_kernel_only TetraStereo.Engine.RingMarkedRadius.radius_some
assert_kernel_only TetraStereo.Engine.RingMarkedRadius.radius_none
assert_kernel_only TetraStereo.Engine.RingMarkedRadius.smaller_wins
assert_kernel_only TetraStereo.Engine.RingMarkedRadius.absent_tie
assert_kernel_only TetraStereo.Engine.RingMarkedRadius.distance_disagreement
assert_kernel_only TetraStereo.Engine.RingMarkedRadius.compare_of_distinct_radii
