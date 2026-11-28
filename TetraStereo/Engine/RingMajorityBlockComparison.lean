import TetraStereo.Engine.RingAntichainDonors
import TetraStereo.Engine.RingFullPathReferencePolicy
import TetraStereo.Engine.RingPairWordPopulation
import TetraStereo.Engine.RingBinaryPairScore
import TetraStereo.Engine.RingLigandFirstDifference
import TetraStereo.Engine.RingChemicalGraphProof

/-! Compare the leading group of equally ranked chiral occurrences, after
Rules 1–4a. An unequal larger hand count decides actual trials at Rule 4b.
If both counts match, exactly this first group can be removed on both arms. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMajorityBlockComparison
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedReferenceGroup (Hit Listing hands group)
open RingReferencePrefix (Prefix)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey bitWord)
open RingRetainedChemicalTrace (Word)
open RingLigandFirstDifference (First Words directions stages)
attribute [local instance] lexOrd

/-- Count both hands only among the highest-ranking chiral occurrences. -/
def majority (p : List RS) := max (p.count .R) (p.count .S)

private theorem size (p : List RS) : p.count .R + p.count .S = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => cases h <;> simp_all <;> omega

private def block (width n : Nat) :=
  List.replicate n true ++ List.replicate (width-n) false

private theorem largest_prefix (p : List RS) (w : RS → List Bool) (h : Prefix p w) :
    ∃ tail, max (w .R) (w .S) = block p.length (majority p) ++ tail := by
  have len := size p
  rcases lt_trichotomy (p.count .R) (p.count .S) with lt|eq|gt
  · refine ⟨h.leftSuffix,?_⟩
    rw [RingReferencePrefix.majority_left_max h lt,h.left]
    simp only [block,majority,max_eq_right (Nat.le_of_lt lt),show p.length - p.count .S = p.count .R by omega]
  · have same : block p.length (majority p) =
        List.replicate (p.count .R) true ++ List.replicate (p.count .S) false := by
      simp [block,majority,eq,show p.length-p.count .S = p.count .S by omega]
    rcases le_total (w .R) (w .S) with l|l
    · exact ⟨_,by rw [max_eq_right l,h.left,same,eq]⟩
    · exact ⟨_,by rw [max_eq_left l,h.right,same]⟩
  · refine ⟨h.rightSuffix,?_⟩
    rw [RingReferencePrefix.majority_right_max h gt,h.right]
    simp only [block,majority,max_eq_left (Nat.le_of_lt gt),show p.length - p.count .R = p.count .S by omega]

private theorem source_prefix {i : Input} {r : Reader i} {q : Arm i} {rev : Bool} {k : Key}
    {hs : List Hit} (ls : Listing i r q hs) (rd : Reads i r rev q k) :
    ∃ tail, k.bestFourB = block (group hs).length (majority (hands hs rev)) ++ tail := by
  obtain ⟨u,l,x,y,z,_,_,rx,ry,_,rfl⟩ := rd
  let w : RS → List Bool := fun h => match h with | .R => x | .S => y
  obtain ⟨p⟩ := RingFullPathReferencePolicy.arm_prefix (w := w) ls (by intro h; cases h <;> assumption)
  simpa only [hands,List.length_map] using largest_prefix (hands hs rev) w p

private theorem fits (hs : List Hit) (rev : Bool) : majority (hands hs rev) ≤ (group hs).length := by
  have len := size (hands hs rev)
  rw [show (hands hs rev).length = (group hs).length by simp [hands]] at len
  unfold majority
  omega

private theorem leading_compare (width a b : Nat) (ba : a ≤ width) (bb : b ≤ width)
    (x y : List Bool) :
    compare (block width a ++ x) (block width b ++ y) =
      (compare a b).then (compare x y) := by
  induction width generalizing a b with
  | zero =>
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp [block]
  | succ width ih =>
    cases a with
    | zero =>
      cases b with
      | zero =>
        simpa [block,List.replicate_succ,List.compare_cons_cons] using ih 0 0 (by omega) (by omega)
      | succ b => simp [block,List.replicate_succ,List.compare_cons_cons,
          show compare false true = .lt by decide,compare_lt_iff_lt.mpr (Nat.zero_lt_succ b)]
    | succ a =>
      cases b with
      | zero => simp [block,List.replicate_succ,List.compare_cons_cons,
          show compare true false = .gt by decide,compare_gt_iff_gt.mpr (Nat.zero_lt_succ a)]
      | succ b =>
        have sc : compare (a+1) (b+1) = compare a b := by
          rcases lt_trichotomy a b with h|rfl|h
          · rw [compare_lt_iff_lt.mpr h,compare_lt_iff_lt.mpr (Nat.succ_lt_succ h)]
          · simp
          · rw [compare_gt_iff_gt.mpr h,compare_gt_iff_gt.mpr (Nat.succ_lt_succ h)]
        simpa [block,List.replicate_succ,List.compare_cons_cons,sc] using ih a b (by omega) (by omega)

private theorem drop_block (width a : Nat) (ok : a ≤ width) (t : List Bool) :
    (block width a ++ t).drop width = t := by
  have len : (block width a).length = width := by simp [block]; omega
  conv_lhs => arg 1; rw [←len]
  simp

/-- Exact residual of the public Rule 4b comparison, including ties. The
common group width is derived from an independent through-4a priority tie. -/
theorem cut {i : Input} {r : Reader i} {a b : Arm i} {rev : Bool}
    {hs ts : List Hit} (la : Listing i r a hs) (lb : Listing i r b ts)
    {u v : RingStereoSiblingPass.Branch} (ua : RingRetainedUnitPass.Reading i r false a u)
    (ub : RingRetainedUnitPass.Reading i r false b v) (tie : u.deep = v.deep)
    {x y : Key} (rx : Reads i r rev a x) (ry : Reads i r rev b y) :
    compare x.bestFourB y.bestFourB =
      (compare (majority (hands hs rev)) (majority (hands ts rev))).then
        (compare (x.bestFourB.drop (group hs).length) (y.bestFourB.drop (group ts).length)) := by
  obtain ⟨px,hx⟩ := source_prefix la rx
  obtain ⟨py,hy⟩ := source_prefix lb ry
  have eq := RingReferenceGroupTransport.Listing.group_length_eq la lb ua ub tie
  rw [hx,hy,drop_block _ _ (fits hs rev),drop_block _ _ (fits ts rev),←eq]
  exact leading_compare _ _ _ (fits hs rev) (eq ▸ fits ts rev) _ _

/-- If all uppercase occurrences belong to the top group, its hand counts
determine the complete 4b component, on either geometry. -/
theorem exhausted {i : Input} {r : Reader i} {q : Arm i} {rev : Bool} {k : Key}
    {hs : List Hit} (ls : Listing i r q hs) (rd : Reads i r rev q k)
    (all : (group hs).length = hs.length) :
    k.bestFourB = List.replicate (majority (hands hs rev)) true ++
      List.replicate ((group hs).length-majority (hands hs rev)) false := by
  obtain ⟨tail,h⟩ := source_prefix ls rd
  have bound := fits hs rev
  have keylen : k.bestFourB.length = hs.length := by
    obtain ⟨u,l,x,y,z,_,_,sr,ss,_,rfl⟩ := rd
    change (max x y).length = _
    rcases le_total x y with le|le
    · rw [max_eq_right le]; exact RingPairWordPopulation.word_length ls ss
    · rw [max_eq_left le]; exact RingPairWordPopulation.word_length ls sr
  rw [h] at keylen
  simp only [block,List.length_append,List.length_replicate] at keylen
  have nil := List.length_eq_zero_iff.mp (show tail.length = 0 by omega)
  simpa only [nil,List.append_nil] using h

private theorem counts_swap (hs : List Hit) :
    (hs.map (fun h => h.hand.swap)).count .R = (hs.map Hit.hand).count .S ∧
    (hs.map (fun h => h.hand.swap)).count .S = (hs.map Hit.hand).count .R := by
  induction hs with
  | nil => exact ⟨rfl,rfl⟩
  | cons h hs ih => cases h with | mk path hand => cases hand <;> simp_all [RS.swap]

theorem mirror_majority (hs : List Hit) (rev : Bool) :
    majority (hands hs rev) = majority (hands hs false) := by
  cases rev with
  | false => rfl
  | true =>
    have swap := counts_swap (group hs)
    simp [majority,hands,swap.1,swap.2,max_comm]

private def overview {i : Input} (r : Reader i) (q : Arm i) := do
  let u ← RingRetainedUnitPass.atArm i r q
  let hits ← RingRetainedReferenceGroup.hits? i r q
  return (u.deep,hits)

open private rank_of from TetraStereo.Engine.RingOccurrenceStereo

private theorem overview_eq {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    {p : RingRetainedStereoDecision.ArmProfile} (h : RingRetainedStereoDecision.Reads i r false q p) :
    overview r q = some (p.unit.deep,p.hits) := by
  have unit := rank_of (os := []) (rev := false) ready valid on h.unit
  change RingRetainedUnitPass.atArm i r q = some p.unit at unit
  have hits : RingRetainedReferenceGroup.hits? i r q = some p.hits :=
    RingAntichainDonors.enumerate_eq ready h.hits valid on _ (Nat.lt_succ_self _)
  simp [overview,unit,hits]

/-- The optional decision computes only earlier priorities and the original
donor populations. It can report either strict direction without constructing
either reference word. Equal maxima leave the residual comparison open. -/
def decide? {i : Input} (r : Reader i) (a b : Arm i) : Option Ordering := do
  let x ← overview r a
  let y ← overview r b
  guard (x.1 = y.1)
  let l := majority (hands x.2 false)
  let h := majority (hands y.2 false)
  guard (l ≠ h)
  return compare l h

private theorem unit_of_key {i : Input} {r : Reader i} {q : Arm i} {rev : Bool}
    {u : RingStereoSiblingPass.Branch} (read : RingRetainedUnitPass.Reading i r false q u)
    {k : Key} (key : Reads i r rev q k) : k.throughFourA = u.deep := by
  obtain ⟨v,l,x,y,z,h,_,_,_,_,rfl⟩ := key
  have eqn : v = u := by
    cases rev with
    | false => exact RingRetainedUnitPass.Reading.unique h read
    | true => exact RingRetainedUnitPass.Reading.unique (RingRetainedStereoRefinement.mirror [] _ _ h) read
  exact congrArg RingStereoSiblingPass.Branch.deep eqn

def Decides {i : Input} (r : Reader i) (a b : Arm i) (rev : Bool) (active : Option Nat) (d : Ordering) : Prop :=
  ∃ ka kb : Key, ∃ m n : Word, ∃ x y : Words,
    RingFullPathEligibility.key? i r rev a = some ka ∧ RingFullPathEligibility.key? i r rev b = some kb ∧
    RingLigandFirstDifference.markWord? r active a = some m ∧ RingLigandFirstDifference.markWord? r active b = some n ∧
    RingLigandFirstDifference.Decomposes ka m x ∧ RingLigandFirstDifference.Decomposes kb n y ∧
    First (directions x y) stages .rule4b d ∧ compare (trialKey ka m) (trialKey kb n) = d

/-- The unreflected highest-group count decides the actual public comparison
on both geometries in every nomination trial. Readiness and the two valid
same-root arms are the standard public scheduling requirements. -/
theorem sound {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    {d : Ordering} (hit : decide? r a b = some d) (rev : Bool) (active : Option Nat) :
    Decides r a b rev active d := by
  obtain ⟨p,hp⟩ := RingGroupedStereo.arm_ready ready a va ra
  obtain ⟨q,hq⟩ := RingGroupedStereo.arm_ready ready b vb rb
  have P := RingGroupedStereo.arm_source hp
  have Q := RingGroupedStereo.arm_source hq
  have left := overview_eq ready va ra P
  have right := overview_eq ready vb rb Q
  by_cases prior : p.unit.deep = q.unit.deep
  · by_cases equal : majority (hands p.hits false) = majority (hands q.hits false)
    · simp [decide?,left,right,prior,equal] at hit
    · have result : compare (majority (hands p.hits false)) (majority (hands q.hits false)) = d := by
        simpa [decide?,left,right,prior,equal] using hit
      have strict : d ≠ .eq := fun z => equal (compare_eq_iff_eq.mp (result.trans z))
      obtain ⟨ka,kb,m,n,x,y,ha,hb,hm,hn,dx,dy,sc⟩ :=
        RingLigandFirstDifference.all_active_arms ready rev a b va vb ra rb active
      have accepted (c : Arm i) (valid : i.certified.LocalizedRerootCursorValid c)
          (on : c.occurrence.val.root = f.val.root) (k : Key)
          (computed : RingFullPathEligibility.key? i r rev c = some k) : Reads i r rev c k := by
        obtain ⟨t,ht,only⟩ := RingFullPathEligibility.key_exact ready rev c valid on
        exact (only k).mpr (Option.some.inj (computed.symm.trans ht))
      have ax := accepted a va ra ka ha
      have by' := accepted b vb rb kb hb
      have before := (unit_of_key P.unit ax).trans (prior.trans (unit_of_key Q.unit by').symm)
      have eq := cut P.hits Q.hits P.unit Q.unit prior ax by'
      rw [mirror_majority _ rev,mirror_majority _ rev,result] at eq
      have value : directions x y .rule4b = d := by
        change compare x.fourB y.fourB = _
        rw [←dx.fourB,←dy.fourB,RingBinaryPairScore.compare_bits,eq]
        cases d <;> simp_all
      rw [dx.through,dy.through] at before
      simp only [List.cons.injEq,and_true] at before
      have first : First (directions x y) stages .rule4b d := by
        apply First.later (by simp [directions,Words.at,before.1])
        apply First.later (by simp [directions,Words.at,before.2.1])
        apply First.later (by simp [directions,Words.at,before.2.2.1])
        apply First.later (by simp [directions,Words.at,before.2.2.2])
        rw [←value]
        exact First.here (value ▸ strict)
      exact ⟨ka,kb,m,n,x,y,ha,hb,hm,hn,dx,dy,first,sc.trans first.scan_value⟩
  · simp [decide?,left,right,prior] at hit

theorem public_decision {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    {d : Ordering} (hit : decide? (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f) a b = some d)
    (rev : Bool) (active : Option Nat) :
    Decides (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f) a b rev active d :=
  sound (RingChemicalGraphProof.ready geom f) a b va vb ra rb hit rev active

end TetraStereo.Engine.RingMajorityBlockComparison
assert_kernel_only TetraStereo.Engine.RingMajorityBlockComparison.cut
assert_kernel_only TetraStereo.Engine.RingMajorityBlockComparison.exhausted
assert_kernel_only TetraStereo.Engine.RingMajorityBlockComparison.public_decision
