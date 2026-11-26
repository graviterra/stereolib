import TetraStereo.Engine.RingMarkedLigandTree
import TetraStereo.Engine.RingMarkedLayout
import TetraStereo.Engine.RingRebuiltStereo
import TetraStereo.Engine.RingMarkedIncidence
import TetraStereo.Engine.RingSpherePopulation

/-! Rule 6 comparison at an ordinary tie. The earlier priority fixes row
boundaries throughout both arms, so only a molecular mark bit can decide. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedDistanceOrder
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRule5Shape (Valid On)
open RingRetainedChemicalTrace (Word)
open RingGroupedMark (Reading bit)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open private framed from TetraStereo.Engine.RingRetainedSeedFrames
open private cmp_append from TetraStereo.Engine.RingRebuiltStereo
open private compare_zero_row from TetraStereo.Engine.RingMarkedIncidence
attribute [local instance] lexOrd

/-- Erasing boundaries preserves all three comparison outcomes on a common row layout. Empty rows are allowed. -/
theorem flatten_compare {α : Type} [Ord α] (a b : List (List α))
    (widths : a.map List.length = b.map List.length) :
    compare a.flatten b.flatten = compare a b := by
  induction a generalizing b with
  | nil => cases b <;> first | rfl | contradiction
  | cons x xs ih =>
    cases b with
    | nil => contradiction
    | cons y ys =>
      obtain ⟨len,more⟩ := List.cons.inj widths
      simp only [List.flatten_cons,cmp_append x y _ _ len,ih ys more,List.compare_cons_cons]

private theorem common_prior {i r rev a b k}
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k) :
    ∃ p z, RingRetainedStereoRefinement.Derives i r false [.lowercase] a p ∧
      RingRetainedStereoRefinement.Derives i r false [.lowercase] b z ∧ p.word = z.word := by
  obtain ⟨_,p,_,_,_,_,pa,_,_,_,ha⟩ := ka
  obtain ⟨_,z,_,_,_,_,pb,_,_,_,hb⟩ := kb
  have same : p.word = z.word := (congrArg Key.fourC ha).symm.trans (congrArg Key.fourC hb)
  cases rev with
  | false => exact ⟨p,z,pa,pb,same⟩
  | true => exact ⟨p,z,RingRetainedStereoRefinement.mirror _ _ _ pa,
      RingRetainedStereoRefinement.mirror _ _ _ pb,same⟩

/-- Row boundaries coincide before comparing any bits, even for two different
promoted atoms and independently sorted arms. -/
theorem widths {i f r rev a b atom other x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r other b y) :
    x.word.map List.length = y.word.map List.length := by
  obtain ⟨p,z,psrc,zsrc,same⟩ := common_prior ka kb
  exact (RingMarkedLayout.word_lengths ready va oa ma psrc).trans
    ((congrArg (List.map List.length) same).trans (RingMarkedLayout.word_lengths ready vb ob mb zsrc).symm)

private theorem same_key (k : Key) (x y : Word) : compare (trialKey k x) (trialKey k y) = compare x y := by
  simp only [trialKey,List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then]
  cases compare x y <;> rfl

theorem trial_compare {i f r rev a b atom other x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r other b y) :
    compare (trialKey k x.word) (trialKey k y.word) = compare x.word.flatten y.word.flatten := by
  rw [same_key,flatten_compare _ _ (widths ready va vb oa ob ka kb ma mb)]

/-- Bits emitted at distance d, counting both the shallow and deep child row. -/
def atSphere (b : Branch) : Nat → List Nat
  | 0 => [b.value]
  | d+1 => (b.levels.getD d []).flatten

private theorem inter_at {α : Type} (xs ys : List (List α)) (d : Nat) :
    (RingChildKeyRecovery.interleave xs ys).getD d [] = xs.getD d [] ++ ys.getD d [] := by
  induction xs generalizing ys d with
  | nil => simp [RingChildKeyRecovery.interleave]
  | cons x xs ih =>
    cases ys with
    | nil => simp [RingChildKeyRecovery.interleave]
    | cons y ys => cases d with
      | zero => rfl
      | succ d => exact ih ys d

private theorem forest_at (xs : List Branch) (d z : Nat) :
    z ∈ (((xs.map Branch.levels).foldr RingChildKeyRecovery.interleave []).getD d []).flatten ↔
      ∃ b ∈ xs, z ∈ atSphere b (d+1) := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons,List.foldr_cons,inter_at,List.flatten_append,List.mem_append,ih]
    simp [atSphere,List.mem_cons,or_and_right,exists_or]

private theorem parent_at {p : Branch} {sh de cs : List Branch}
    (layout : p.levels = rows sh de) (a : sh.Perm cs) (b : de.Perm cs) (d z : Nat) :
    z ∈ atSphere p (d+1) ↔ ∃ c ∈ cs, z ∈ atSphere c d := by
  cases d with
  | zero =>
    simp only [atSphere,layout,rows,List.getD_cons_zero,List.flatten_cons,List.flatten_nil,
      List.append_nil,List.mem_append,List.mem_map,List.mem_singleton]
    constructor
    · rintro (⟨c,hc,h⟩ | ⟨c,hc,h⟩)
      · exact ⟨c,a.mem_iff.mp hc,h.symm⟩
      · exact ⟨c,b.mem_iff.mp hc,h.symm⟩
    · rintro ⟨c,hc,h⟩
      exact Or.inl ⟨c,a.mem_iff.mpr hc,h.symm⟩
  | succ d =>
    simp only [atSphere,layout,rows,List.getD_cons_succ,forest_at]
    exact exists_congr fun c => and_congr b.mem_iff Iff.rfl

/-- A bit occurs at this exact distance precisely when an actual molecular
cursor carrying it can be reached in that many retained child steps. -/
theorem sphere_support {i r atom q b} (h : Reading i r atom q b) (d z : Nat) :
    z ∈ atSphere b d ↔ ∃ t, RingSpherePopulation.AtDistance i d q t ∧ bit atom t = z := by
  induction h generalizing d with
  | node prior look complete below sh de ih =>
    cases d with
    | zero =>
      constructor
      · intro hz
        exact ⟨_,.here,(List.mem_singleton.mp hz).symm⟩
      · rintro ⟨_,path,hz⟩
        cases path
        exact List.mem_singleton.mpr hz.symm
    | succ d =>
      rw [parent_at rfl sh.perm de.perm d z]
      constructor
      · rintro ⟨c,hc,hz⟩
        obtain ⟨u,hu,found⟩ := RingRetainedUnitPass.forOutput complete hc
        obtain ⟨t,dist,bitEq⟩ := (ih u hu found d).mp hz
        exact ⟨t,.descend hu dist,bitEq⟩
      · rintro ⟨t,path,bitEq⟩
        cases path with
        | descend hc dist =>
          obtain ⟨v,hm,hv⟩ := RingRetainedReferenceGroup.forInput complete hc
          exact ⟨v,hm,(ih _ hc hv d).mpr ⟨t,dist,bitEq⟩⟩

private def spheres (b : Branch) : List (List Nat) := [b.value] :: b.levels.map List.flatten

private theorem sphere_get (b : Branch) (d : Nat) : (spheres b).getD d [] = atSphere b d := by
  cases d with
  | zero => rfl
  | succ d =>
    change (b.levels.map List.flatten).getD d [] = _
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,atSphere]
    cases b.levels[d]? <;> rfl

private theorem sphere_flat (b : Branch) : (spheres b).flatten = b.word.flatten := by
  simp [spheres,Branch.word,List.flatten_flatten]

private theorem sphere_sizes {i f r rev a b atom other x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r other b y) :
    (spheres x).map List.length = (spheres y).map List.length := by
  obtain ⟨p,z,pa,pb,same⟩ := common_prior ka kb
  have equal := RingRetainedChemicalTrace.Framed.unique (framed _ pa)
    (framed _ pb) (List.cons.inj same).2
  have layout := (RingMarkedLayout.layer_widths ready va oa ma pa).trans
    (equal ▸ (RingMarkedLayout.layer_widths ready vb ob mb pb).symm)
  simpa [spheres,List.map_map,Function.comp_def,List.length_flatten] using
    congrArg (fun ls : List (List Nat) => 1 :: ls.map List.sum) layout

private theorem nonnegative_row (xs ys : List Nat) (h : xs.length = ys.length)
    (silent : ∀ z ∈ ys, z = 0) : compare xs ys ≠ .lt := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | decide | contradiction
  | cons a xs ih =>
    cases ys with
    | nil => contradiction
    | cons b ys =>
      obtain rfl := silent b List.mem_cons_self
      cases a with
      | zero =>
        simpa only [List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then] using
          ih ys (Nat.succ.inj h) (fun z hz => silent z (.tail _ hz))
      | succ n =>
        simp [List.compare_cons_cons,Nat.compare_eq_gt.mpr (Nat.zero_lt_succ n)]

private theorem earlier_sphere (xs ys : List (List Nat)) (d : Nat)
    (layout : xs.map List.length = ys.map List.length)
    (hit : 1 ∈ xs.getD d [])
    (clear : ∀ j ≤ d, ∀ z ∈ ys.getD j [], z = 0) : compare xs ys = .gt := by
  induction xs generalizing ys d with
  | nil => simp at hit
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys =>
      obtain ⟨len,more⟩ := List.cons.inj layout
      have hy : ∀ z ∈ y, z = 0 := clear 0 (Nat.zero_le _)
      rw [List.compare_cons_cons]
      cases d with
      | zero => rw [compare_zero_row len hit hy]; rfl
      | succ d =>
        have later := ih ys d more hit (fun j hj => clear (j+1) (by omega))
        cases cmp : compare x y with
        | eq => exact later
        | gt => rfl
        | lt => exact False.elim (nonnegative_row x y len hy cmp)

/-- A purely molecular sufficient condition for a strict Rule 6 comparison.
The left arm reaches the promoted atom in d retained steps. The right arm
has no occurrence of it through that sphere. Both arms may contain the
atom farther away, including ring-closure copies. -/
theorem nearer_wins {i f r rev a b atom x y k}
    (ready : @RingGroupedStereo.Ready i f r) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b)
    (ka : RingFullPathEligibility.Reads i r rev a k) (kb : RingFullPathEligibility.Reads i r rev b k)
    (ma : Reading i r atom a x) (mb : Reading i r atom b y) {d : Nat}
    (hit : ∃ t, RingSpherePopulation.AtDistance i d a t ∧ t.occurrence.val.node.current?.map Fin.val = some atom)
    (clear : ∀ j ≤ d, ∀ t, RingSpherePopulation.AtDistance i j b t →
      t.occurrence.val.node.current?.map Fin.val ≠ some atom) :
    compare (trialKey k x.word) (trialKey k y.word) = .gt := by
  have layout := sphere_sizes ready va vb oa ob ka kb ma mb
  rw [trial_compare ready va vb oa ob ka kb ma mb,← sphere_flat,← sphere_flat,
    flatten_compare _ _ layout]
  apply earlier_sphere _ _ d layout
  · rw [sphere_get,sphere_support ma]
    obtain ⟨t,path,atAtom⟩ := hit
    exact ⟨t,path,by simp [bit,atAtom]⟩
  · intro j hj z hz
    rw [sphere_get,sphere_support mb] at hz
    obtain ⟨t,path,rfl⟩ := hz
    simp [bit,clear j hj t path]

/-- Inspect native children by distance, in molecular input order, without a
priority sort or any auxiliary-descriptor reader. -/
def hitsAt (i : Input) (atom : Nat) (q : Arm i) (d : Nat) : Bool :=
  (RingSpherePopulation.atDistance i d [q]).any fun c => c.occurrence.val.node.current?.map Fin.val == some atom

theorem hitsAt_iff {i : Input} (atom : Nat) (q : Arm i) (d : Nat) :
    hitsAt i atom q d = true ↔ ∃ c, RingSpherePopulation.AtDistance i d q c ∧
      c.occurrence.val.node.current?.map Fin.val = some atom := by
  simp [hitsAt,List.any_eq_true,RingSpherePopulation.mem_distance]

def winsAt (i : Input) (atom : Nat) (a b : Arm i) (d : Nat) : Bool :=
  hitsAt i atom a d && (List.range (d+1)).all fun j => !hitsAt i atom b j

/-- The whole public trial comparison on the actual store at a scheduled root
or auxiliary call. No marked order or marked reading is supplied as a premise. -/
theorem public_winsAt {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {stage : Nat} {f : Site i} (called : RingGlobalComparison.Called i root stage f)
    (rev : Bool) (atom : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingFullPathEligibility.key? i (RingGlobalComparison.prior i root stage) rev a =
      RingFullPathEligibility.key? i (RingGlobalComparison.prior i root stage) rev b)
    (d : Nat) (wins : winsAt i atom a b d = true) :
    (do let r := RingGlobalComparison.prior i root stage
        let k ← RingFullPathEligibility.key? i r rev a
        let l ← RingFullPathEligibility.key? i r rev b
        let x ← RingGroupedMark.arm? i r atom a
        let y ← RingGroupedMark.arm? i r atom b
        pure (compare (trialKey k x.2.word) (trialKey l y.2.word))) = some .gt := by
  rw [RingGlobalComparison.prior_exact called] at tie ⊢
  let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
  have ready : RingGroupedStereo.Ready f r := RingChemicalGraphProof.ready geom f
  obtain ⟨k,hk,ka⟩ := RingFullPathEligibility.key_exact ready rev a va oa
  obtain ⟨l,hl,kb⟩ := RingFullPathEligibility.key_exact ready rev b vb ob
  obtain rfl := Option.some.inj (hk.symm.trans (tie.trans hl))
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready atom a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready atom b vb ob
  obtain ⟨hit,clear⟩ := Bool.and_eq_true_iff.mp wins
  have earlier := nearer_wins ready va vb oa ob ((ka _).mpr rfl) ((kb _).mpr rfl)
    (RingGroupedMark.arm_source hx).2 (RingGroupedMark.arm_source hy).2 ((hitsAt_iff ..).mp hit) (by
      intro j hj t path atAtom
      have clearAt := List.all_eq_true.mp clear j (List.mem_range.mpr (by omega))
      have occupied := (hitsAt_iff atom b j).mpr ⟨t,path,atAtom⟩
      simp [occupied] at clearAt)
  dsimp only [r] at hk hl hx hy
  simp only [hk,hl,hx,hy,bind,pure,Option.bind_some,earlier]

end TetraStereo.Engine.RingMarkedDistanceOrder
assert_kernel_only TetraStereo.Engine.RingMarkedDistanceOrder.trial_compare
assert_kernel_only TetraStereo.Engine.RingMarkedDistanceOrder.sphere_support
assert_kernel_only TetraStereo.Engine.RingMarkedDistanceOrder.nearer_wins
assert_kernel_only TetraStereo.Engine.RingMarkedDistanceOrder.public_winsAt
