import TetraStereo.Engine.RingSingleDonorComparison
import TetraStereo.Engine.RingBinaryPairScore

/-! Native comparisons when the uppercase emitters at each individual
distance all have one hand. The hand may change arbitrarily between spheres. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSphereDonorComparison
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingSpherePopulation (Hierarchy full children)
open RingFullPathPairs (FullVisit Oracle handAt likeAt)
open RingSingleDonorComparison (onGeometry)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey bitWord)
open RingGeometryExchange (Carrier Frozen)
open RingSplitLigandTie (markingReader)
open RingLigandFirstDifference (Words Decomposes directions stages First markWord?)
open private blocks full_on reflected unsigned from TetraStereo.Engine.RingSingleDonorComparison
open private next_perm from TetraStereo.Engine.RingSpherePopulation
attribute [local instance] lexOrd

structure Sphere where
  count : Nat
  hand : RS
  deriving DecidableEq, Repr

def sphere? (hands : List RS) : Option Sphere :=
  let h := hands.headD .R
  if hands = List.replicate hands.length h then some ⟨hands.length,h⟩ else none

/-- Native child order, original unseeded labels, and one count per sphere.
Empty spheres of emitters contribute zero. A mixed-hand sphere rejects. -/
def profile? {i : Input} (r : Reader i) (q : Arm i) : Option (List Sphere) :=
  (full i [q]).mapM fun row => sphere? (row.filterMap (handAt i r false))

def word (ds : List Sphere) (rev : Bool) (seed : RS) :=
  ds.flatMap fun d => List.replicate d.count (onGeometry rev d.hand == seed)

private theorem sphere_sound {hs : List RS} {d : Sphere} (ok : sphere? hs = some d) :
    hs = List.replicate d.count d.hand := by
  dsimp only [sphere?] at ok
  split at ok
  · rename_i eq
    obtain rfl := Option.some.inj ok
    exact eq
  · contradiction

/-- The profile succeeds precisely when any two uppercase occurrences
within the same sphere have the same original hand. -/
theorem profile_complete {i : Input} (r : Reader i) (q : Arm i) :
    (profile? r q).isSome = true ↔ ∀ row ∈ full i [q],
      ∀ h ∈ row.filterMap (handAt i r false), ∀ k ∈ row.filterMap (handAt i r false), h = k := by
  have single (xs : List RS) : (sphere? xs).isSome = true ↔
      ∀ h ∈ xs, ∀ k ∈ xs, h = k := by
    constructor
    · intro success
      obtain ⟨d,hd⟩ := Option.isSome_iff_exists.mp success
      have all := (List.eq_replicate_iff.mp (sphere_sound hd)).2
      exact fun h hm k km => (all h hm).trans (all k km).symm
    · intro uniform
      cases xs with
      | nil => rfl
      | cons h t =>
        have eq : h :: t = List.replicate (h :: t).length h :=
          List.eq_replicate_of_mem (fun x hx => uniform x hx h List.mem_cons_self)
        simp only [sphere?,List.headD_cons,if_pos eq,Option.isSome_some]
  have map_ok {α β : Type} (g : α → Option β) (xs : List α) :
      (xs.mapM g).isSome = true ↔ ∀ x ∈ xs, (g x).isSome = true := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.forall_mem_cons,←ih,List.mapM_cons]
      cases g x <;> cases xs.mapM g <;> simp
  rw [profile?,map_ok]
  exact forall_congr' (fun row => forall_congr' (fun _ => single _))

private theorem profile_rows {i : Input} {r : Reader i} {q : Arm i} {ds : List Sphere}
    (accepted : profile? r q = some ds) :
    List.Forall₂ (fun (row : List (Arm i)) (d : Sphere) =>
      row.filterMap (handAt i r false) = List.replicate d.count d.hand) (full i [q]) ds := by
  unfold profile? at accepted
  generalize full i [q] = rows at accepted ⊢
  induction rows generalizing ds with
  | nil => obtain rfl := (Option.some.inj accepted).symm; exact .nil
  | cons row rows ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨d,hd,tail⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest,hr,eq⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj eq
    exact .cons (sphere_sound hd) (ih hr)

private theorem walk_words {i : Input} {o : Oracle i} {bit : Arm i → Option Bool}
    {xs out : List (FullVisit i)} (walk : o.Walk bit xs out) {front hs}
    (same : (xs.map FullVisit.cursor).Perm front) (hier : Hierarchy i front hs)
    {ds : List Sphere} (b : Sphere → Bool)
    (uniform : List.Forall₂ (fun (row : List (Arm i)) (d : Sphere) =>
      row.filterMap bit = List.replicate d.count (b d)) hs ds) :
    out.filterMap (fun v => bit v.cursor) = ds.flatMap (fun d => List.replicate d.count (b d)) := by
  induction walk generalizing front hs ds with
  | stop =>
    obtain rfl := same.symm.eq_nil
    cases hier
    cases uniform
    rfl
  | @sphere v vs groups sorted tail ex legal walk ih =>
    cases hier with
    | stop => have no := same.eq_nil; simp at no
    | @layer c cs actual rest pars sub =>
      cases uniform with
      | cons note following =>
        have row := same.filterMap bit
        rw [note] at row
        have head := List.perm_replicate.mp row
        have step := (legal.perm.map FullVisit.cursor).trans (List.Perm.of_eq (blocks _ _ ex))
        have nextRow := step.trans ((same.flatMap_right (children i)).trans (next_perm pars).symm)
        simpa only [List.filterMap_append,List.filterMap_map,Function.comp_def,List.flatMap_cons]
          using congrArg₂ List.append head (ih nextRow sub following)

theorem source_word {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) {ds : List Sphere} (accepted : profile? r q = some ds)
    (rev : Bool) (seed : RS) {o : Oracle i} {bits : List Bool}
    (src : o.Source (likeAt i r rev seed) q bits) : bits = word ds rev seed := by
  obtain ⟨visits,walk,rfl⟩ := src
  apply walk_words walk (List.Perm.refl [q]) (RingSpherePopulation.full_complete (by simpa using valid))
  have rows := profile_rows accepted
  suffices ∀ rows' ds', (∀ row ∈ rows', row ∈ full i [q]) →
      List.Forall₂ (fun (row : List (Arm i)) (d : Sphere) =>
        row.filterMap (handAt i r false) = List.replicate d.count d.hand) rows' ds' →
      List.Forall₂ (fun (row : List (Arm i)) (d : Sphere) =>
        row.filterMap (likeAt i r rev seed) = List.replicate d.count (onGeometry rev d.hand == seed)) rows' ds' from
    this _ _ (fun _ mem => mem) rows
  intro rows' ds' sub rel
  induction rel with
  | nil => exact .nil
  | @cons row d rows ds eq _ ih =>
    refine .cons ?_ (ih (fun t ht => sub t (List.mem_cons_of_mem row ht)))
    have h := congrArg (List.map (fun x => onGeometry rev x == seed)) eq
    rw [List.map_filterMap,List.map_replicate] at h
    refine Eq.trans (List.filterMap_congr ?_) h
    intro c member
    have sameRoot := (full_on q valid (List.mem_flatten.mpr ⟨row,sub _ List.mem_cons_self,member⟩)).trans on
    simp only [likeAt,reflected ready c sameRoot rev,Option.map_map,Function.comp_def]

/-- All legal full-path sorting stages and both reference seeds recover the
same word from these counts, on the original or reflected geometry. -/
theorem stage_word {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) {ds : List Sphere} (accepted : profile? r q = some ds)
    (rev : Bool) (os : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i r rev os seed q = some (word ds rev seed) := by
  let o := RingFullPathPairs.stage i r rev os
  obtain ⟨w,hit,unique⟩ := o.source_exact (f := f) (likeAt i r rev seed)
    (RingOccurrenceStereo.rank_total ready rev os) q valid on
  exact hit.trans (congrArg some (source_word ready q valid on accepted rev seed ((unique w).mpr rfl)))

def best (ds : List Sphere) (rev : Bool) := max (word ds rev .R) (word ds rev .S)

private theorem fields {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) {ds : List Sphere} (accepted : profile? r q = some ds)
    (rev : Bool) {k : Key} (read : Reads i r rev q k) :
    k.bestFourB = best ds rev ∧ k.fixedR = word ds rev .R := by
  obtain ⟨_,_,ar,as',fr,_,_,sr,ss,sf,rfl⟩ := read
  rw [source_word ready q valid on accepted rev .R sr,source_word ready q valid on accepted rev .S ss,
    source_word ready q valid on accepted rev .R sf]
  exact ⟨rfl,rfl⟩

open RingLigandFirstDifference (Stage)

/-- The two permitted deciding stages, or an ordinary tie. -/
def decideProfiles (a b : List Sphere) (rev : Bool) : Option (Stage × Ordering) :=
  let four := compare (best a rev) (best b rev)
  let five := compare (word a rev .R) (word b rev .R)
  if four ≠ .eq then some (.rule4b,four)
  else if five ≠ .eq then some (.rule5,five)
  else none

def Agrees (ka kb : Key) (m n : Word) (x y : Words) : Option (Stage × Ordering) → Prop
  | some (s,d) => First (directions x y) stages s d ∧ compare (trialKey ka m) (trialKey kb n) = d
  | none => ka = kb ∧ compare (trialKey ka m) (trialKey kb n) = compare m n

private theorem compare_mark (ka : Key) (m n : Word) :
    compare (trialKey ka m) (trialKey ka n) = compare m n := by
  simp only [trialKey,List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then]
  cases compare m n <;> rfl

private theorem branches {ka kb : Key} {m n : Word} {x y : Words} {a b : List Sphere} {rev : Bool}
    (dx : Decomposes ka m x) (dy : Decomposes kb n y)
    (prior : ka.throughFourA = kb.throughFourA) (lo : ka.fourC = kb.fourC)
    (pa : ka.bestFourB = best a rev ∧ ka.fixedR = word a rev .R)
    (pb : kb.bestFourB = best b rev ∧ kb.fixedR = word b rev .R) :
    Agrees ka kb m n x y (decideProfiles a b rev) := by
  have fields := prior
  rw [dx.through,dy.through] at fields
  simp only [List.cons.injEq,and_true] at fields
  have C := dx.fourC.symm.trans (lo.trans dy.fourC)
  have B : directions x y .rule4b = compare (best a rev) (best b rev) := by
    simp only [directions,Words.at,←dx.fourB,←dy.fourB,pa.1,pb.1,RingBinaryPairScore.compare_bits]
  have F : directions x y .rule5 = compare (word a rev .R) (word b rev .R) := by
    simp only [directions,Words.at,←dx.five,←dy.five,pa.2,pb.2,RingBinaryPairScore.compare_bits]
  have before {s o} (rest : First (directions x y) [.rule4b,.rule4c,.rule5,.activeMark] s o) :
      First (directions x y) stages s o := by
    apply First.later (by simp [directions,Words.at,fields.1])
    apply First.later (by simp [directions,Words.at,fields.2.1])
    apply First.later (by simp [directions,Words.at,fields.2.2.1])
    exact First.later (by simp [directions,Words.at,fields.2.2.2]) rest
  dsimp only [decideProfiles]
  split_ifs with four five
  · have first := before (First.here (by rwa [B] : directions x y .rule4b ≠ .eq))
    exact ⟨B ▸ first,(RingLigandFirstDifference.compare_trial_eq_scan dx dy).trans (first.scan_value.trans B)⟩
  · have mid : directions x y .rule4c = .eq := by simp [directions,Words.at,C]
    have first := before (First.later (B.trans (Classical.not_not.mp four))
      (First.later mid (First.here (by rwa [F] : directions x y .rule5 ≠ .eq))))
    exact ⟨F ▸ first,(RingLigandFirstDifference.compare_trial_eq_scan dx dy).trans (first.scan_value.trans F)⟩
  · have bb := pa.1.trans ((Std.compare_eq_eq_iff_eq.mp (Classical.not_not.mp four)).trans pb.1.symm)
    have ff := pa.2.trans ((Std.compare_eq_eq_iff_eq.mp (Classical.not_not.mp five)).trans pb.2.symm)
    have eq : ka = kb := by cases ka; cases kb; simp_all
    exact ⟨eq,eq ▸ compare_mark _ m n⟩

/-- For any admitted tetrahedral arm pair, the unsorted original counts
predict the native comparison at every active mark and on both geometries.
A surviving ordinary tie passes the decision on to the two actual mark words. -/
theorem comparison {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    (c : Carrier i i) (dom : c.domain a) (dest : c.image a = b)
    (same : Frozen c (markingReader r) (markingReader r))
    {da db : List Sphere} (left : profile? r a = some da) (right : profile? r b = some db)
    (rev : Bool) (active : Option Nat) :
    ∃ ka kb : Key, ∃ m n : Word, ∃ x y : Words,
      RingFullPathEligibility.key? i r rev a = some ka ∧ RingFullPathEligibility.key? i r rev b = some kb ∧
      markWord? r active a = some m ∧ markWord? r active b = some n ∧
      Decomposes ka m x ∧ Decomposes kb n y ∧ Agrees ka kb m n x y (decideProfiles da db rev) := by
  obtain ⟨ka,kb,m,n,x,y,ha,hb,hm,hn,dx,dy,_⟩ :=
    RingLigandFirstDifference.all_active_arms ready rev a b va vb ra rb active
  have accepted (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
      (on : q.occurrence.val.root = f.val.root) (k : Key)
      (hit : RingFullPathEligibility.key? i r rev q = some k) : Reads i r rev q k := by
    obtain ⟨key,eqn,only⟩ := RingFullPathEligibility.key_exact ready rev q valid on
    exact (only k).mpr (Option.some.inj (hit.symm.trans eqn))
  have l := accepted a va ra ka ha
  have t := accepted b vb rb kb hb
  obtain ⟨early,lower⟩ := unsigned c dom dest same l t
  exact ⟨ka,kb,m,n,x,y,ha,hb,hm,hn,dx,dy,branches dx dy early lower
    (fields ready a va ra left rev l) (fields ready b vb rb right rev t)⟩

end TetraStereo.Engine.RingSphereDonorComparison

assert_kernel_only TetraStereo.Engine.RingSphereDonorComparison.profile_complete
assert_kernel_only TetraStereo.Engine.RingSphereDonorComparison.stage_word
assert_kernel_only TetraStereo.Engine.RingSphereDonorComparison.comparison
