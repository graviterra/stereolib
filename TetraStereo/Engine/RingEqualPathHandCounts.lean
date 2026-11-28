import TetraStereo.Engine.RingResidualPairDecision
import TetraStereo.Engine.RingStereoInventoryScores
import TetraStereo.Engine.RingMajorityBlockComparison
import TetraStereo.Engine.RingOppositeDonorArms

/-! Hand counts on a single group of equally ranked donor paths, after
discarding only non-emitting endpoints. The neutral occurrences are still
traversed by the molecular inventory. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingEqualPathHandCounts
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingStereoSphereInventory (Inventory Edge SignedPath project reading sphere inventory?)
open RingFullPathPairs (bitOf bitOf_snoc stepKey)
open RingRetainedChemicalTrace (Word)
open RingUnorderedSphereReading (readRow)
open RingStereoSiblingPass (order legal_order)
open RingRetainedReferenceGroup (Path)
attribute [local instance] lexOrd

def tip (stem : SignedPath) (priority : List Word) (h : RS) : SignedPath :=
  stem ++ [⟨priority,some h⟩]

def lastHand (p : SignedPath) := p.getLast?.bind Edge.hand

def visible (row : Multiset SignedPath) := row.filter (fun p => (lastHand p).isSome)

def quiet (rows : Inventory) : Prop := ∀ row ∈ rows, visible row = 0

/-- One occupied sphere; all its emitting paths agree before the terminal
hand. Neutral endpoints in this or any other sphere may be arbitrary. -/
inductive Orbit (nr ns : Nat) (inv : Inventory) : Prop where
  | empty (r : nr = 0) (s : ns = 0) (silent : quiet inv)
  | single (before after : Inventory) (row : Multiset SignedPath) (stem : SignedPath) (priority : List Word)
      (parts : inv = before ++ row :: after) (prior : quiet before) (later : quiet after)
      (population : visible row = Multiset.replicate nr (tip stem priority .R) +
        Multiset.replicate ns (tip stem priority .S))

private def fits (nr ns : Nat) (row : Multiset SignedPath) (p : SignedPath) : Bool :=
  p.getLast?.any fun e =>
    visible row = Multiset.replicate nr (tip p.dropLast e.earlier .R) +
      Multiset.replicate ns (tip p.dropLast e.earlier .S)

/-- Executable on a complete, unseeded inventory. The first emitting row
supplies its own path template; all remaining rows must be silent. -/
def check (nr ns : Nat) : Inventory → Bool
  | [] => nr == 0 && ns == 0
  | row::rest =>
    if visible row = 0 then check nr ns rest else
      decide (∃ p ∈ row.toFinset, fits nr ns row p = true) &&
        rest.all fun later => decide (visible later = 0)

theorem check_sound {nr ns : Nat} {inv : Inventory} (ok : check nr ns inv = true) : Orbit nr ns inv := by
  induction inv with
  | nil =>
    have zero : nr = 0 ∧ ns = 0 := by simpa [check] using ok
    exact .empty zero.1 zero.2 (by simp [quiet])
  | cons row rest ih =>
    unfold check at ok
    split at ok
    next empty =>
      cases ih ok with
      | empty hr hs silent =>
        exact .empty hr hs (by simpa [quiet,empty] using silent)
      | single before after a p d parts prior later pop =>
        exact .single (row::before) after a p d (congrArg (row :: ·) parts)
          (by simpa [quiet, empty] using prior) later pop
    next =>
      simp only [Bool.and_eq_true] at ok
      obtain ⟨one,all⟩ := ok
      have found : ∃ p ∈ row.toFinset, fits nr ns row p = true := of_decide_eq_true one
      obtain ⟨p,_,fit⟩ := found
      obtain ⟨e,_,matchRow⟩ := (Option.any_eq_true ..).mp fit
      exact .single [] rest row p.dropLast e.earlier rfl (by simp [quiet])
        (fun v hv => of_decide_eq_true (List.all_eq_true.mp all v hv)) (of_decide_eq_true matchRow)

private theorem bit_project (s : RS) (p : SignedPath) :
    bitOf (project s p) = (lastHand p).map (· == s) := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p e _ =>
    simp [project,List.map_append,bitOf_snoc,lastHand]

private theorem sphere_visible (s : RS) (row : Multiset SignedPath) :
    sphere s (visible row) = sphere s row := by
  induction row using Quotient.inductionOn with
  | _ ps =>
    change sphere s (visible (↑ps)) = sphere s (↑ps)
    simp only [visible,Multiset.filter_coe, sphere,Multiset.lift_coe,Bool.decide_coe]
    simpa only [bit_project,Option.isSome_map] using
      RingUnorderedSphereReading.readRow_filter (project s) bitOf ps

private theorem silence {s : RS} {inv : Inventory} (h : quiet inv) : reading s inv = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro row mem
  rw [← sphere_visible,h row mem]
  change readRow (project s) bitOf [] = []
  simp [readRow,order]

def runs (yes no : Nat) := List.replicate yes true ++ List.replicate no false

private theorem sphere_block (s : RS) (p : SignedPath) (d : List Word) (a b : Nat) :
    sphere s (Multiset.replicate a (tip p d s) + Multiset.replicate b (tip p d s.swap)) = runs a b := by
  let x := project s (tip p d s)
  let y := project s (tip p d s.swap)
  have hx : bitOf x = some true := by cases s <;> simp [x,bit_project,tip,lastHand]
  have hy : bitOf y = some false := by cases s <;> simp [y,bit_project,tip,lastHand,RS.swap]
  have lower : y ≤ x := by
    apply le_of_lt
    cases s <;>
      simp only [x,y,tip,project,List.map_append,List.map_cons,List.map_nil] <;>
      apply List.append_left_lt <;> apply List.Lex.rel <;>
      apply List.append_left_lt <;> decide
  let row := List.replicate a x ++ List.replicate b y
  have sorted : row.Pairwise (· ≥ ·) := by
    simp [row,List.pairwise_append]
    grind
  have eqn : order id row = row := List.Perm.eq_of_pairwise
    (fun _ _ _ _ h k => le_antisymm k h) (by simpa using (legal_order id row).descending) sorted
    (legal_order id row).perm
  change readRow (project s) bitOf (List.replicate a (tip p d s) ++ List.replicate b (tip p d s.swap)) = _
  unfold readRow
  simp only [List.map_append,List.map_replicate,← show x = project s (tip p d s) from rfl,
    ← show y = project s (tip p d s.swap) from rfl,List.filter_append,List.filter_replicate,hx,hy]
  change (order id row).filterMap bitOf = _
  rw [eqn]
  simp [row,runs,hx,hy]

private def count (nr ns : Nat) : RS → Nat | .R => nr | .S => ns

theorem word {nr ns : Nat} {inv : Inventory} (h : Orbit nr ns inv) (seed : RS) :
    reading seed inv = runs (count nr ns seed) (count nr ns seed.swap) := by
  cases h with
  | empty hr hs silent => cases seed <;> simp [silence silent,hr,hs,runs,count,RS.swap]
  | single before after row p d parts prior later pop =>
    subst inv
    simp only [reading,List.flatMap_append,List.flatMap_cons]
    rw [show before.flatMap (sphere seed) = [] from silence prior,
      show after.flatMap (sphere seed) = [] from silence later,List.nil_append,List.append_nil,
      ← sphere_visible,pop]
    cases seed with
    | R => exact sphere_block .R p d nr ns
    | S => rw [add_comm]; exact sphere_block .S p d ns nr

open private leading_compare block from TetraStereo.Engine.RingMajorityBlockComparison

private theorem compare_block (a b c d : Nat) (width : a+b=c+d) :
    compare (runs a b) (runs c d) = compare a c := by
  have h := leading_compare (a+b) a c (by omega) (by omega) [] []
  simpa [runs,block,show a+b-c=d by omega] using h

private theorem best (r s : Nat) :
    max (runs r s) (runs s r) = runs (max r s) (min r s) := by
  rcases lt_trichotomy r s with lt|eq|gt
  · have small : runs r s < runs s r := by
      simpa [runs] using RingReferencePrefix.block_lt (b := s) (d := r) lt (by omega) [] []
    rw [max_eq_right small.le,max_eq_right lt.le,min_eq_left lt.le]
  · simp [eq]
  · have big : runs s r < runs r s := by
      simpa [runs] using RingReferencePrefix.block_lt (b := r) (d := s) gt (by omega) [] []
    rw [max_eq_left big.le,max_eq_left gt.le,min_eq_right gt.le]

/-- All molecular observations are taken from the same actual prior and
geometry. Each pass obtains its own unsigned priority stem from the graph. -/
structure Population (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) (nr ns : Nat) : Prop where
  fourB : ∃ inv, inventory? i r rev [] q = some inv ∧ Orbit nr ns inv
  five : ∃ inv, inventory? i r rev [.lowercase] q = some inv ∧ Orbit nr ns inv

def armCheck (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) (nr ns : Nat) : Bool :=
  (inventory? i r rev [] q).any (check nr ns) &&
  (inventory? i r rev [.lowercase] q).any (check nr ns)

theorem armCheck_sound {i : Input} {r : Reader i} {rev : Bool} {q : Arm i} {nr ns : Nat}
    (hit : armCheck i r rev q nr ns = true) : Population i r rev q nr ns := by
  simp only [armCheck,Bool.and_eq_true] at hit
  obtain ⟨a,b⟩ := hit
  obtain ⟨pa,ha,ok⟩ := (Option.any_eq_true ..).mp a
  obtain ⟨pb,hb,ok'⟩ := (Option.any_eq_true ..).mp b
  exact ⟨⟨pa,ha,check_sound ok⟩,pb,hb,check_sound ok'⟩

private theorem key_counts {i : Input} {r : Reader i} {rev : Bool} {a : Arm i} {nr ns : Nat}
    (data : Population i r rev a nr ns) {key : RingFullPathEligibility.Key}
    (hit : RingFullPathEligibility.key? i r rev a = some key) :
    key.bestFourB = runs (max nr ns) (min nr ns) ∧ key.fixedR = runs nr ns := by
  rw [← RingStereoSphereInventory.key_exact] at hit
  unfold RingStereoSphereInventory.key? at hit
  obtain ⟨b,hb,sb⟩ := data.fourB
  obtain ⟨f,hf,sf⟩ := data.five
  obtain ⟨u,_,h⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨l,_,h⟩ := Option.bind_eq_some_iff.mp h
  simp only [hb,hf] at h
  cases h
  simp only [word sb,word sf,count,RS.swap]
  exact ⟨best nr ns,True.intro⟩

/-- Both complete native fixed-reference comparisons, including the
orientation-sensitive magnitude of Rule 5, from unranked population counts. -/
theorem rule5 {i : Input} {r : Reader i} {rev : Bool} {a b : Arm i} {ar as' br bs : Nat}
    (left : Population i r rev a ar as') (right : Population i r rev b br bs)
    (width : ar+as'=br+bs) :
    RingFullPathRule5.score? i r rev a b =
      some (RingOccurrenceStereo.fixedScore (compare ar br) (compare as' bs)) := by
  obtain ⟨x,hx,px⟩ := left.five
  obtain ⟨y,hy,py⟩ := right.five
  unfold RingFullPathRule5.score? RingFullPathRule5.word?
  simp only [← RingStereoSphereInventory.reading_exact,hx,hy,Option.map_some,
    word px,word py]
  change some (RingOccurrenceStereo.fixedScore (compare (runs ar as') (runs br bs))
    (compare (runs as' ar) (runs bs br))) = _
  rw [compare_block _ _ _ _ width,compare_block _ _ _ _ (by omega)]

open RingFullPathTrialReadings (trialKey)
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie

open RingLigandFirstDifference (Stage stages directions)
open RingResidualPairDecision (Verdict words Explains Table TableExact)
open private pick pick_exact explained_order from TetraStereo.Engine.RingResidualPairDecision

def stepVerdict (s : Stage) (o : Ordering) (next : Verdict) : Verdict :=
  match o with
  | .gt => .left s
  | .lt => .right s
  | .eq => next

/-- First distinguishing rule for one equal-path donor group on each arm. -/
def verdict (ar as' br bs : Nat) (marks : Ordering := .eq) : Verdict :=
  stepVerdict .rule4b (compare (max ar as') (max br bs))
    (stepVerdict .rule5 (compare ar br) (stepVerdict .activeMark marks .tie))

/-- The carrier matches only constitutional and unsigned observations. The
hands may be arranged differently on the two arms. Any promoted marks enter
only after the majority and fixed-R counts have tied. -/
theorem trial_stage {i : Input} {r : Reader i} {f : Site i} (ready : RingGroupedStereo.Ready f r)
    (carrier : RingGeometryExchange.Carrier i i)
    (same : RingGeometryExchange.Frozen carrier (RingSplitLigandTie.markingReader r)
      (RingSplitLigandTie.markingReader r)) (a : Arm i) (dom : carrier.domain a)
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid (carrier.image a))
    (oa : a.occurrence.val.root = f.val.root) (ob : (carrier.image a).occurrence.val.root = f.val.root)
    (rev : Bool) {ar as' br bs : Nat} (left : Population i r rev a ar as')
    (right : Population i r rev (carrier.image a) br bs) :
    ∃ x y, RingFullPathEligibility.key? i r rev a = some x ∧
      RingFullPathEligibility.key? i r rev (carrier.image a) = some y ∧
      ∀ m n : Word, compare (trialKey x m) (trialKey y n) =
        (compare (max ar as') (max br bs)).then ((compare ar br).then (compare m n)) ∧
        pick (directions (words x m) (words y n)) stages = verdict ar as' br bs (compare m n) := by
  obtain ⟨x,hx,ex⟩ := RingFullPathEligibility.key_exact ready rev a va oa
  obtain ⟨y,hy,ey⟩ := RingFullPathEligibility.key_exact ready rev (carrier.image a) vb ob
  obtain ⟨mx,fx⟩ := key_counts left hx
  obtain ⟨my,fy⟩ := key_counts right hy
  refine ⟨x,y,hx,hy,?_⟩
  obtain ⟨u,l,xr,xs,xf,hu,hl,_,_,wx,rfl⟩ := (ex x).mpr rfl
  obtain ⟨v,k,yr,ys,yf,hv,hk,_,_,wy,rfl⟩ := (ey y).mpr rfl
  have earlier := carrier.unit same dom (normalized_unit hu) (normalized_unit hv)
  have lower := carrier.refinement same [.lowercase] a dom _ _ (normalized_lower hl) (normalized_lower hk)
  obtain ⟨hs,_,ls⟩ := RingAntichainDonors.listing_exists ready a va oa
  obtain ⟨ts,_,rs⟩ := RingAntichainDonors.listing_exists ready (carrier.image a) vb ob
  have original {q w} (h : RingRetainedStereoRefinement.Derives i r rev [] q w) :
      RingRetainedUnitPass.Reading i r false q w := by
    cases rev with
    | false => exact h
    | true => exact RingRetainedStereoRefinement.mirror [] q w h
  have equalLen : hs.length = ts.length := by
    simpa using (RingReferenceGroupTransport.Listing.paths_perm ls rs
      (original hu) (original hv) (congrArg _ earlier)).length_eq
  have lx := RingPairWordPopulation.rule5_length ls wx
  have ly := RingPairWordPopulation.rule5_length rs wy
  dsimp only at mx my fx fy
  rw [fx] at lx
  rw [fy] at ly
  have width : ar+as'=br+bs := by
    simpa [runs] using lx.trans (equalLen.trans ly.symm)
  intro m n
  have major : max ar as' + min ar as' = max br bs + min br bs := by omega
  constructor
  · simp only [trialKey,earlier,lower,List.compare_cons_cons]
    rw [mx,my,fx,fy]
    simp [RingBinaryPairScore.compare_bits,compare_block _ _ _ _ major,compare_block _ _ _ _ width]
  · simp only [stages,pick,directions,words,RingLigandFirstDifference.Words.at,earlier,lower,
      Std.ReflOrd.compare_self,mx,my,fx,fy,RingBinaryPairScore.compare_bits,compare_block _ _ _ _ major,
      compare_block _ _ _ _ width,verdict,stepVerdict]
    cases compare (max ar as') (max br bs) <;> cases compare ar br <;> cases compare m n <;> rfl

theorem trial {i : Input} {r : Reader i} {f : Site i} (ready : RingGroupedStereo.Ready f r)
    (carrier : RingGeometryExchange.Carrier i i)
    (same : RingGeometryExchange.Frozen carrier (RingSplitLigandTie.markingReader r)
      (RingSplitLigandTie.markingReader r)) (a : Arm i) (dom : carrier.domain a)
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid (carrier.image a))
    (oa : a.occurrence.val.root = f.val.root) (ob : (carrier.image a).occurrence.val.root = f.val.root)
    (rev : Bool) {ar as' br bs : Nat} (left : Population i r rev a ar as')
    (right : Population i r rev (carrier.image a) br bs) :
    ∃ x y, RingFullPathEligibility.key? i r rev a = some x ∧
      RingFullPathEligibility.key? i r rev (carrier.image a) = some y ∧
      ∀ m n : Word, compare (trialKey x m) (trialKey y n) =
        (compare (max ar as') (max br bs)).then ((compare ar br).then (compare m n)) := by
  obtain ⟨x,y,hx,hy,h⟩ := trial_stage ready carrier same a dom va vb oa ob rev left right
  exact ⟨x,y,hx,hy,fun m n => (h m n).1⟩

private theorem verdict_unique {d ss v w} (h : Explains d ss v) (k : Explains d ss w) : v = w := by
  have o := (explained_order h).symm.trans (explained_order k)
  cases v <;> cases w <;> try contradiction
  · rfl
  · exact congrArg _ (h.unique k).1
  · exact congrArg _ (h.unique k).1

open RingNestedActivePair (Frame)
open RingGroupedCentre (cursor)
open RingActivePairReport (Slot)
open private keys_exact from TetraStereo.Engine.RingFullPathPublication

/-- An exact table entry on either geometry for any scheduled nomination.
For an ordinary trial the lawful marks are both empty. -/
theorem table_entry {i : Input} {r : Reader i} {f : Site i} (fr : Frame i f)
    (ready : RingGroupedStereo.Ready f r) (carrier : RingGeometryExchange.Carrier i i)
    (same : RingGeometryExchange.Frozen carrier (RingSplitLigandTie.markingReader r)
      (RingSplitLigandTie.markingReader r)) (a b : Slot) (dom : carrier.domain (cursor fr a))
    (image : carrier.image (cursor fr a) = cursor fr b) {rev : Bool} {ar as' br bs : Nat}
    (left : Population i r rev (cursor fr a) ar as') (right : Population i r rev (cursor fr b) br bs)
    {m : Option Slot} {table : Table} (exactTable : TableExact fr r rev m table)
    {ws : Slot → Word} (marks : RingFullPathTrialReadings.MarkWords fr r rev m ws) :
    table[a.val][b.val] = verdict ar as' br bs (compare (ws a) (ws b)) := by
  obtain ⟨ks,_,only⟩ := keys_exact fr ready rev
  have legal := (only ks).mpr rfl
  obtain ⟨x,y,hx,hy,h⟩ := trial_stage ready carrier same (cursor fr a) dom
    (RingGroupedCentre.valid fr a) (image ▸ RingGroupedCentre.valid fr b)
    (fr.direction a).property.1 (image ▸ (fr.direction b).property.1) rev left (image ▸ right)
  rw [image] at hy
  have identified (s : Slot) (k) (got : RingFullPathEligibility.key? i r rev (cursor fr s) = some k) :
      ks s = k := by
    obtain ⟨v,hv,onlyV⟩ := RingFullPathEligibility.key_exact ready rev (cursor fr s)
      (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact ((onlyV _).mp (legal s)).trans (Option.some.inj (hv.symm.trans got))
  have entry := (exactTable ks ws legal marks a b).1
  rw [identified a x hx,identified b y hy] at entry
  rw [← (h (ws a) (ws b)).2]
  exact verdict_unique entry (pick_exact _ _)

/-- Ordinary trials end in a complete tie when both donor counts agree. -/
theorem ordinary_entry {i : Input} {r : Reader i} {f : Site i} (fr : Frame i f)
    (ready : RingGroupedStereo.Ready f r) (carrier : RingGeometryExchange.Carrier i i)
    (same : RingGeometryExchange.Frozen carrier (RingSplitLigandTie.markingReader r)
      (RingSplitLigandTie.markingReader r)) (a b : Slot) (dom : carrier.domain (cursor fr a))
    (image : carrier.image (cursor fr a) = cursor fr b) {rev : Bool} {ar as' br bs : Nat}
    (left : Population i r rev (cursor fr a) ar as') (right : Population i r rev (cursor fr b) br bs)
    {table : Table} (exactTable : TableExact fr r rev none table) :
    table[a.val][b.val] = verdict ar as' br bs := by
  simpa using table_entry fr ready carrier same a b dom image left right exactTable
    (ws := fun _ => []) (fun _ => rfl)

end TetraStereo.Engine.RingEqualPathHandCounts
assert_kernel_only TetraStereo.Engine.RingEqualPathHandCounts.word
assert_kernel_only TetraStereo.Engine.RingEqualPathHandCounts.armCheck_sound
assert_kernel_only TetraStereo.Engine.RingEqualPathHandCounts.rule5
assert_kernel_only TetraStereo.Engine.RingEqualPathHandCounts.trial
assert_kernel_only TetraStereo.Engine.RingEqualPathHandCounts.table_entry
assert_kernel_only TetraStereo.Engine.RingEqualPathHandCounts.ordinary_entry
