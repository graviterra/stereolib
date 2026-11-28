import TetraStereo.Engine.RingBinaryPairScore
import TetraStereo.Engine.RingStereoPriorityBlocks
import TetraStereo.Engine.RingStereoSphereInventory

/-! A band contains enantiomorphic two-donor branches. Each nearer pair
contains one R and one S. Each distal pair either preserves both hands or
reverses both. Its Boolean records preservation, independent of the seed. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPairedDonorBands
open OneCenter RingStereoPriorityBlocks RingFullPathPairs
open RingStereoSphereInventory (SignedPath project sphere)
open RingRetainedReferenceGroup (Path)
open RingRetainedChemicalTrace (Word)
open private compare_block from TetraStereo.Engine.RingStereoPriorityBlocks

structure Stem where
  parent : Path
  earlier : List Word

def Stem.block (s : Stem) (l u : Nat) : Class := ⟨s.parent,s.earlier,0,l,u⟩
def Stem.path (s : Stem) (b : Bool) := s.parent ++ [stepKey s.earlier (some b)]

structure Band where
  nearStem : Stem
  likeParent : Stem
  unlikeParent : Stem
  preserves : List Bool

private def nearPaths (b : Band) :=
  b.preserves.map (fun _ => b.nearStem.path true) ++ b.preserves.map (fun _ => b.nearStem.path false)
private def farPaths (b : Band) :=
  b.preserves.map b.likeParent.path ++ b.preserves.map (fun x => b.unlikeParent.path (!x))

private def nearClass (b : Band) := b.nearStem.block b.preserves.length b.preserves.length
private def farClasses (b : Band) :=
  [b.likeParent.block (b.preserves.count true) (b.preserves.count false),
   b.unlikeParent.block (b.preserves.count false) (b.preserves.count true)]

private theorem near_pop (b : Band) : nearPaths b = (nearClass b).paths := by
  simp [nearPaths,nearClass,Stem.block,Stem.path,Class.paths,Class.key,List.map_const']

private theorem bool_perm (p : Bool) (bs : List Bool) :
    bs.Perm (List.replicate (bs.count p) p ++ List.replicate (bs.count (!p)) (!p)) := by
  rw [List.perm_iff_count]
  intro x
  cases p <;> cases x <;> simp [List.count_replicate]

private theorem far_pop (b : Band) : (farPaths b).Perm (paths (farClasses b)) := by
  have a := (bool_perm true b.preserves).map b.likeParent.path
  have z := (bool_perm false b.preserves).map (fun x => b.unlikeParent.path (!x))
  simpa [farPaths,paths,farClasses,Stem.block,Class.paths,Class.key,Stem.path,List.append_assoc]
    using a.append z

private def visible (s : RS) (xs : List SignedPath) :=
  (xs.map (project s)).filter fun p => (bitOf p).isSome

/-- The premises inspect only the two unsorted molecular sphere populations
and the earlier-rule separation of the proposed path classes. Other visits
may be silent anywhere in either sphere. -/
structure Realizes (s : RS) (near far : List SignedPath) (bs : List Band) : Prop where
  near_cover : (visible s near).Perm (bs.flatMap nearPaths)
  far_cover : (visible s far).Perm (bs.flatMap farPaths)
  near_order : (bs.map nearClass).Pairwise Separated
  far_order : (bs.flatMap farClasses).Pairwise Separated

def word (bs : List Band) :=
  RingStereoPriorityBlocks.word (bs.map nearClass) ++ RingStereoPriorityBlocks.word (bs.flatMap farClasses)

theorem sphere_words {s : RS} {near far : List SignedPath} {bs : List Band}
    (h : Realizes s near far bs) :
    sphere s (↑near) ++ sphere s (↑far) = word bs := by
  have n : (visible s near).Perm (paths (bs.map nearClass)) := by
    simpa [paths,List.flatMap_map,show nearPaths = (fun b => (nearClass b).paths) from funext near_pop,Function.comp_def] using h.near_cover
  have f : (visible s far).Perm (paths (bs.flatMap farClasses)) := by
    apply h.far_cover.trans
    simpa [paths,List.flatMap_assoc] using List.Perm.flatMap_left bs (fun b _ => far_pop b)
  exact congrArg₂ List.append (order_exact _ (ordered_of_separated _ h.near_order) _ n)
    (order_exact _ (ordered_of_separated _ h.far_order) _ f)

def sizes (bs : List Band) := bs.map fun b => b.preserves.length
def concordances (bs : List Band) := bs.map fun b => b.preserves.count true

private theorem near_same {xs ys : List Band} (width : sizes xs = sizes ys) :
    RingStereoPriorityBlocks.word (xs.map nearClass) = RingStereoPriorityBlocks.word (ys.map nearClass) := by
  let bits := fun (n : Nat) => List.replicate n true ++ List.replicate n false
  simpa [RingStereoPriorityBlocks.word,sizes,nearClass,Class.word,Stem.block,bits,List.flatMap_map,Function.comp_def]
    using congrArg (List.flatMap bits) width

private theorem total (xs : List Bool) : xs.count true + xs.count false = xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp_all <;> omega

private theorem far_compare (xs ys : List Band) (width : sizes xs = sizes ys) :
    compare (RingStereoPriorityBlocks.word (xs.flatMap farClasses))
      (RingStereoPriorityBlocks.word (ys.flatMap farClasses)) = compare (concordances xs) (concordances ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [sizes,concordances]
  | cons x xs ih =>
    cases ys with
    | nil => simp [sizes] at width
    | cons y ys =>
      obtain ⟨w,t⟩ := List.cons.inj width
      have nt := total x.preserves
      have mt := total y.preserves
      let a := x.preserves.count true
      let b := y.preserves.count true
      let u := x.preserves.count false
      let v := y.preserves.count false
      have sum : a+u=b+v := nt.trans (w.trans mt.symm)
      have rev : u+a=v+b := by omega
      simp only [concordances,List.map_cons,List.compare_cons_cons]
      change compare (List.replicate a true ++ List.replicate u false ++
          ((List.replicate u true ++ List.replicate a false) ++ _))
        (List.replicate b true ++ List.replicate v false ++
          ((List.replicate v true ++ List.replicate b false) ++ _)) = _
      simp only [List.append_assoc]
      rw [← List.append_assoc (List.replicate a true),← List.append_assoc (List.replicate b true),
        compare_block _ _ _ _ _ _ sum]
      cases c : compare a b with
      | lt => rfl
      | gt => rfl
      | eq =>
        have same := Std.compare_eq_eq_iff_eq.mp c
        have eqn : u = v := by omega
        rw [← List.append_assoc (List.replicate u true),← List.append_assoc (List.replicate v true),
          compare_block _ _ _ _ _ _ rev,eqn,show compare v v = .eq from Std.ReflCmp.compare_self]
        exact ih ys t

private theorem word_compare_counts {xs ys : List Band} (width : sizes xs = sizes ys) :
    compare (word xs) (word ys) = compare (concordances xs) (concordances ys) := by
  unfold word
  rw [near_same width]
  generalize RingStereoPriorityBlocks.word (ys.map nearClass) = p
  induction p with
  | nil => exact far_compare xs ys width
  | cons v p ih => simpa [List.compare_cons_cons] using ih

/-- Compare the numbers of preserving pairs in successive equal-width
earlier-priority bands. This determines both strict directions and ties. -/
theorem compare_spheres {s t : RS} {an af bn bf : List SignedPath} {xs ys : List Band}
    (a : Realizes s an af xs) (b : Realizes t bn bf ys) (width : sizes xs = sizes ys) :
    compare (sphere s (↑an) ++ sphere s (↑af)) (sphere t (↑bn) ++ sphere t (↑bf)) =
      compare (concordances xs) (concordances ys) := by
  rw [sphere_words a,sphere_words b]
  exact word_compare_counts width

private theorem match_pairs (xs ys : List Band) (width : sizes xs = sizes ys) :
    concordances xs = concordances ys ↔ List.Forall₂ (fun a b : Band => a.preserves.Perm b.preserves) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [sizes,concordances]
  | cons x xs ih =>
    cases ys with
    | nil => simp [sizes] at width
    | cons y ys =>
      obtain ⟨len,rest⟩ := List.cons.inj width
      constructor
      · intro h
        obtain ⟨count,tail⟩ := List.cons.inj h
        refine .cons (List.perm_iff_count.mpr ?_) ((ih ys rest).mp tail)
        intro value
        cases value with
        | true => exact count
        | false =>
          have lx := total x.preserves
          have ly := total y.preserves
          change x.preserves.length = y.preserves.length at len
          change x.preserves.count true = y.preserves.count true at count
          omega
      · intro pairs
        cases pairs with
        | cons head tail => exact congrArg₂ List.cons (head.count_eq true) ((ih ys rest).mpr tail)

/-- A surviving tie permits an exact matching of preserving and reversing
pairs inside each priority band. Actual atom exchanges further require
preservation of the remainder of the molecular graph. -/
theorem tie_iff_matching {s t : RS} {an af bn bf : List SignedPath} {xs ys : List Band}
    (a : Realizes s an af xs) (b : Realizes t bn bf ys) (width : sizes xs = sizes ys) :
    compare (sphere s (↑an) ++ sphere s (↑af)) (sphere t (↑bn) ++ sphere t (↑bf)) = .eq ↔
      List.Forall₂ (fun x y : Band => x.preserves.Perm y.preserves) xs ys := by
  rw [compare_spheres a b width,Std.compare_eq_eq_iff_eq,match_pairs xs ys width]

open RingStereoSphereInventory (Inventory inventory? reading)
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)

def Silent (s : RS) (rows : Inventory) : Prop :=
  ∀ row ∈ rows, ∀ p ∈ row, bitOf (project s p) = none

private theorem silent_reading {s : RS} {rows : Inventory} (h : Silent s rows) : reading s rows = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro row mem
  have silent := h row mem
  induction row using Quotient.inductionOn with
  | _ xs =>
    have empty : ((xs.map (project s)).filter fun k => (bitOf k).isSome) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro k hk
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hk
      simp [silent p hp]
    change (RingStereoSiblingPass.order id _).filterMap bitOf = []
    simp [empty,RingStereoSiblingPass.order]

/-- Identify the actual native stage word from two occupied spheres of its
molecular inventory. Silent spheres may precede, separate or follow them. -/
theorem stage_word {i : Input} {r : Reader i} {rev : Bool} {stages} {s : RS} {q : Arm i}
    {pre gap post : Inventory} {near far : List SignedPath} {bs : List Band}
    (layers : inventory? i r rev stages q = some (pre ++ [(near : Multiset SignedPath)] ++ gap ++ [(far : Multiset SignedPath)] ++ post))
    (hp : Silent s pre) (hg : Silent s gap) (ht : Silent s post) (shape : Realizes s near far bs) :
    stageWords i r rev stages s q = some (word bs) := by
  rw [← RingStereoSphereInventory.reading_exact,layers,Option.map_some]
  apply congrArg some
  have append (x y : Inventory) : reading s (x ++ y) = reading s x ++ reading s y :=
    List.flatMap_append
  simp only [append,silent_reading hp,silent_reading hg,silent_reading ht,List.nil_append,List.append_nil]
  simpa [reading] using sphere_words shape

/-- Both reference hands see the same lists of preserving and reversing
pairs per band. Actual signed path keys can differ between the two reads. -/
def PairedArm {i : Input} (r : Reader i) (rev : Bool) (stages : List RingRetainedStereoRefinement.Observation)
    (q : Arm i) (bs : List Band) : Prop :=
  ∀ s : RS, ∃ (pre gap post : Inventory) (near far : List SignedPath) (groups : List Band),
    inventory? i r rev stages q = some (pre ++ [(near : Multiset SignedPath)] ++ gap ++ [(far : Multiset SignedPath)] ++ post) ∧
    Silent s pre ∧ Silent s gap ∧ Silent s post ∧ Realizes s near far groups ∧
    List.Forall₂ (fun x y : Band => x.preserves.Perm y.preserves) groups bs

private theorem reference_word {i : Input} {r : Reader i} {rev stages} {q : Arm i} {bs : List Band}
    (model : PairedArm r rev stages q bs) (s : RS) : stageWords i r rev stages s q = some (word bs) := by
  obtain ⟨pre,gap,post,near,far,gs,layers,hp,hg,ht,shape,matched⟩ := model s
  have width : sizes gs = sizes bs := by
    clear shape model
    induction matched with
    | nil => rfl
    | cons h _ ih => exact congrArg₂ List.cons h.length_eq ih
  have equal : compare (word gs) (word bs) = .eq := by
    rw [word_compare_counts width,(match_pairs gs bs width).mpr matched]
    exact Std.ReflCmp.compare_self
  rw [stage_word layers hp hg ht shape,Std.compare_eq_eq_iff_eq.mp equal]

def score (ordering : Ordering) : Int :=
  match ordering with | .lt => -1 | .eq => 0 | .gt => 1

theorem rule4b {i : Input} {r : Reader i} {rev} {a b : Arm i} {xs ys : List Band}
    (left : PairedArm r rev [] a xs) (right : PairedArm r rev [] b ys) (width : sizes xs = sizes ys) :
    hanson? i r rev a b = some (score (compare (concordances xs) (concordances ys))) := by
  simp only [hanson?,pairs?,reference_word left,reference_word right,bind,Option.bind,pure,
    RingOccurrenceStereo.fourLists_order,max_self,word_compare_counts width]
  cases compare (concordances xs) (concordances ys) <;> rfl

theorem rule5 {i : Input} {r : Reader i} {rev} {a b : Arm i} {xs ys : List Band}
    (left : PairedArm r rev [.lowercase] a xs) (right : PairedArm r rev [.lowercase] b ys)
    (width : sizes xs = sizes ys) :
    RingFullPathRule5.score? i r rev a b = some (score (compare (concordances xs) (concordances ys))) := by
  simp only [RingFullPathRule5.score?,RingFullPathRule5.word?,reference_word left,reference_word right,
    bind,Option.bind,pure,word_compare_counts width]
  cases compare (concordances xs) (concordances ys) <;> rfl

open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)

private theorem key_fields {i : Input} {r : Reader i} {rev} {q : Arm i} {base fine : List Band}
    (early : PairedArm r rev [] q base) (late : PairedArm r rev [.lowercase] q fine) {k : Key}
    (got : RingFullPathEligibility.key? i r rev q = some k) :
    k.bestFourB = word base ∧ k.fixedR = word fine := by
  unfold RingFullPathEligibility.key? at got
  cases x : RingRetainedStereoRefinement.priority i r rev [] q <;>
    cases y : RingRetainedStereoRefinement.priority i r rev [.lowercase] q <;>
    simp [x,y,pairs?,RingFullPathRule5.word?,reference_word early,reference_word late] at got
  subst k
  exact ⟨rfl,rfl⟩

/-- Every nomination uses the same two population comparisons. Equal counts
pass control to the next rule, down to the nominated-atom comparison. -/
theorem trial_order {i : Input} {r : Reader i} {rev} {a b : Arm i} {x y u v : List Band}
    (ax : PairedArm r rev [] a x) (by' : PairedArm r rev [] b y)
    (au : PairedArm r rev [.lowercase] a u) (bv : PairedArm r rev [.lowercase] b v)
    (earlyWidth : sizes x = sizes y) (lateWidth : sizes u = sizes v)
    {ka kb : Key} (ha : RingFullPathEligibility.key? i r rev a = some ka)
    (hb : RingFullPathEligibility.key? i r rev b = some kb) (ma mb : Word) :
    compare (trialKey ka ma) (trialKey kb mb) =
      (compare ka.throughFourA kb.throughFourA).then ((compare (concordances x) (concordances y)).then
        ((compare ka.fourC kb.fourC).then ((compare (concordances u) (concordances v)).then (compare ma mb)))) := by
  obtain ⟨ex,lu⟩ := key_fields ax au ha
  obtain ⟨ey,lv⟩ := key_fields by' bv hb
  simp [trialKey,List.compare_cons_cons,ex,ey,lu,lv,RingBinaryPairScore.compare_bits,
    word_compare_counts earlyWidth,word_compare_counts lateWidth]

end TetraStereo.Engine.RingPairedDonorBands
assert_kernel_only TetraStereo.Engine.RingPairedDonorBands.sphere_words
assert_kernel_only TetraStereo.Engine.RingPairedDonorBands.compare_spheres
assert_kernel_only TetraStereo.Engine.RingPairedDonorBands.stage_word
assert_kernel_only TetraStereo.Engine.RingPairedDonorBands.tie_iff_matching
assert_kernel_only TetraStereo.Engine.RingPairedDonorBands.rule4b
assert_kernel_only TetraStereo.Engine.RingPairedDonorBands.rule5
assert_kernel_only TetraStereo.Engine.RingPairedDonorBands.trial_order
