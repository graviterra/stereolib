import TetraStereo.Examples.RingPublishedTetraspiro
import TetraStereo.Engine.RingChemicalPriority
import TetraStereo.Engine.RingSeededPairs
import TetraStereo.Engine.RingIsotopePriority
import TetraStereo.Engine.RingNestedActivePair
import TetraStereo.Engine.RingTerminalPair

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 60000

namespace TetraStereo.Examples.RingPublishedTetraspiroAuxiliary
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority RingSeededPairs RingPublishedTetraspiro

/-- A common prefix of accepted comparisons can be removed without
looking inside either tail. -/
theorem common_prefix (u a b : List Bool) :
    compareBits (u ++ a) (u ++ b) = compareBits a b := by
  induction u with
  | nil => rfl
  | cons x xs ih => simpa [compareBits] using ih

/-- For fixed seeds, equal accepted lengths and the first unlike pair suffice.
The subsequent publications may differ arbitrarily. -/
theorem fixed_first {x y : List (Option RS)} {u a b : List RS} {v w seed : RS}
    (left : x.filterMap id = u ++ v :: a) (right : y.filterMap id = u ++ w :: b)
    (diff : v ≠ w) (size : a.length = b.length) :
    listSign? seed x y = some (CentresRing.PairList.pairSign seed v w) := by
  simp only [listSign?,left,right,List.length_append,List.length_cons,size,if_true,List.map_append,
    List.map_cons,common_prefix]
  cases v <;> cases w <;> cases seed <;> simp_all [compareBits,CentresRing.PairList.pairSign]

/-- All complete distance-preserving walks produce the same accepted list
when at most one upper-case publication occurs per sphere. Unlabelled
nodes may occupy different positions and still contribute to Rule 4b. -/
theorem sparse_accepted {s : Spheres} {walk : List (Option RS)}
    (sparse : ∀ row ∈ s, (row.filterMap id).length ≤ 1) (visit : Visits s walk) :
    walk.filterMap id = s.flatten.filterMap id := by
  obtain ⟨actual,rows,rfl⟩ := visit
  induction rows with
  | nil => rfl
  | @cons x y xs ys order _ ih =>
    have bound := sparse y (by simp)
    have perm := order.filterMap id
    have fixed : x.filterMap id = y.filterMap id := by
      cases h : y.filterMap id with
      | nil => exact (h ▸ perm).eq_nil
      | cons head tail =>
        cases tail with
        | nil => exact (h ▸ perm).eq_singleton
        | cons _ _ => simp [h] at bound
    simp [fixed,ih (fun r hr => sparse r (by simp [hr]))]

/-- Unfiltered source pairing can be replaced by accepted bits precisely
under this common mask of occupied positions. -/
theorem aligned_bits (s t : RS) {x y : List (Option RS)}
    (aligned : List.Forall₂ (fun l r : Option RS => l.isSome = r.isSome) x y) :
    compareBits (x.map (like s)) (y.map (like t)) =
      compareBits ((x.filterMap id).map (· == s)) ((y.filterMap id).map (· == t)) := by
  induction aligned with
  | nil => rfl
  | @cons a b _ _ same _ ih =>
    cases a <;> cases b <;> simp_all [like,compareBits]

private def asGeometry (sp : SpatialConfiguration) : Geometry := fun k => sp.positions[k]?

/-- Walk the original retained digraph until the nonterminal breadth-first
queue is empty. The addresses are carried in the cursors' molecular histories. -/
private def layers : Nat → List CanonicalRerootCursor → Option (List (List CanonicalRerootCursor))
  | _,[] => some []
  | 0,_::_ => none
  | n+1,q :: qs => do
    let level := q :: qs
    let next := level.flatMap fun c => (c.children molecule).filter fun b => !(b.children molecule).isEmpty
    return level :: (← layers n next)

/-- Signed publication from the actual original path and its strict
molecular Rule 1a order. The retained arm toward the old root is included. -/
def auxiliary (sp : SpatialConfiguration) (path : List Nat) :=
  atomicAux? molecule (asGeometry sp) path (5-path.length)

def read? (sp : SpatialConfiguration) (q : CanonicalRerootCursor) : Option (Option RS) :=
  if q.node.forcedLeaf || !centers.contains q.node.atom then some none
  else (auxiliary sp q.node.history.reverse).map some

/-- The checked terminal horizon contains every molecular node, even when the
arm first runs back to the old root. The stored comparison key is the exact
sparse encoding of the canonical Rule 1a hierarchy at this common depth. -/
def completeKey? (q : CanonicalRerootCursor) := do
  guard (SiblingConstitution.exhausted molecule 8 q)
  let t ← atomicTree molecule 3 8 q
  return SiblingConstitution.key 3 8 t

def completeOrder? (xs : List CanonicalRerootCursor) : Option Bool := do
  let ks ← xs.mapM completeKey?
  return decide (ks.Pairwise fun x y => LocalizedPhysicalMarkedSparseMarker.compareMarker x y = .gt)

def completeRanking? (path : List Nat) : Option Bool := do
  let rank ← atomicRanking? molecule path (5-path.length)
  completeOrder? (rank.arms.map (·.cursor))

theorem completeKey_source {q k} (produced : completeKey? q = some k) :
    SiblingConstitution.exhausted molecule 8 q = true ∧
    ∃ t, atomicTree molecule 3 8 q = some t ∧ k = SiblingConstitution.key 3 8 t := by
  unfold completeKey? at produced
  obtain ⟨_,guarded,next⟩ := Option.bind_eq_some_iff.mp produced
  have ok : SiblingConstitution.exhausted molecule 8 q = true := by
    cases full : SiblingConstitution.exhausted molecule 8 q <;> simp_all
  obtain ⟨t,built,out⟩ := Option.bind_eq_some_iff.mp next
  exact ⟨ok,t,built,(Option.some.inj out).symm⟩

def observed? (sp : SpatialConfiguration) (root arm : Nat) : Option Spheres := do
  let c ← (occurrenceLigandCursors molecule (canonicalCenterRoot root)).find? (fun c => c.node.atom == arm)
  let ls ← layers 6 [c]
  ls.mapM fun level => level.mapM (read? sp)

def ringPaths (u v w z : Nat) := [[u,v],[u,v,w],[u,v,w,z]]
def paths := ringPaths 2 3 6 9 ++ ringPaths 2 9 6 3 ++ ringPaths 3 6 9 2 ++ ringPaths 3 2 9 6 ++
  ringPaths 6 3 2 9 ++ ringPaths 6 9 2 3 ++ ringPaths 9 6 3 2 ++ ringPaths 9 2 3 6

def hands : List RS := [.S,.R,.S, .S,.S,.S, .R,.R,.S, .S,.S,.R,
                         .R,.S,.R, .R,.R,.R, .S,.R,.R, .R,.S,.S]

/-- A computed sphere summary tests per-level sparsity before discarding
unoccupied positions. Its source computation fails on an unresolved hand. -/
def summary? (sp : SpatialConfiguration) (root arm : Nat) : Option (List RS) := do
  let ls ← observed? sp root arm
  guard (ls.all fun row => (row.filterMap id).length ≤ 1)
  return ls.flatten.filterMap id

theorem summary_source {sp root arm result} (obs : summary? sp root arm = some result) :
    ∃ ls, observed? sp root arm = some ls ∧ ∀ walk, Visits ls walk → walk.filterMap id = result := by
  unfold summary? at obs
  obtain ⟨ls,generated,next⟩ := Option.bind_eq_some_iff.mp obs
  by_cases ok : (ls.all fun row => (row.filterMap id).length ≤ 1) = true
  · have out : ls.flatten.filterMap id = result := by simpa [ok] using next
    exact ⟨ls,generated,fun walk order =>
      (sparse_accepted (fun row mem => of_decide_eq_true (List.all_eq_true.mp ok row mem)) order).trans out⟩
  · simp [ok] at next

def arms : List (Nat × Nat) := [(2,9),(2,3),(3,6),(3,2),(6,9),(6,3),(9,6),(9,2)]
def words : List (List RS) := [[.S,.S,.S],[.S,.R,.S],[.R,.R,.S],[.S,.S,.R],
  [.R,.R,.R],[.R,.S,.R],[.S,.R,.R],[.R,.S,.S]]

/-- Separate fixed references can order the four complete queues independently. -/
theorem double_fixed {s l : RS} {xr yr xs ys : List (Option RS)} {a b c d : List RS}
    (leftR : xr.filterMap id = s :: a) (rightR : yr.filterMap id = l :: b)
    (leftS : xs.filterMap id = s :: c) (rightS : ys.filterMap id = l :: d)
    (opposed : s ≠ l) (sizeR : a.length = b.length) (sizeS : c.length = d.length) :
    (do let r ← listSign? .R xr yr
        let t ← listSign? .S xs ys
        return CentresRing.PairList.combine r t) = some (if s = .R then (2 : Int) else -2) := by
  rw [fixed_first (u := []) leftR rightR opposed sizeR,
    fixed_first (u := []) leftS rightS opposed sizeS]
  cases s <;> cases l <;> simp_all [CentresRing.PairList.pairSign,CentresRing.PairList.combine]

open Certificate.CanonicalSphereKey (Key ckey)

private abbrev Cursor := CanonicalRerootCursor

def projected (q : Cursor) := (q.children molecule).filter fun c => !(c.children molecule).isEmpty

private def deep? (q : Cursor) := (atomicTree molecule 3 1 q).map (ckey 3 1)
private def deep (q : Cursor) : Key Nat := (deep? q).getD []
private def shallow? (_sp : SpatialConfiguration) (q : Cursor) : Option (List Nat) := do
  let atom ← molecule.atoms[q.node.atom]?
  return [atom.element.atomicNumber,if !q.node.forcedLeaf && centers.contains q.node.atom then 2 else 0]
private def shallow (sp : SpatialConfiguration) (q : Cursor) := (shallow? sp q).getD []

/-- A shallow sibling comparison uses atomic number and tetrahedral unit class.
A deep comparison can already stop at the first two molecular atomic-number
spheres. Both independent comparisons give the same strict order at these forks. -/
structure Ranked (sp : SpatialConfiguration) (q : Cursor) (xs : List Cursor) : Prop where
  children : xs.Perm (projected q)
  supported : ∀ x ∈ xs, (deep? x).isSome = true ∧ (shallow? sp x).isSome = true
  constitutional : xs.Pairwise fun x y => deep y < deep x
  currentUnit : xs.Pairwise fun x y => shallow sp y < shallow sp x

def earlier? (sp : SpatialConfiguration) (q : Cursor) : Option {xs // Ranked sp q xs} :=
  let before (x y : Cursor) := deep y ≤ deep x
  let xs := (projected q).insertionSort before
  if h : (∀ x ∈ xs, (deep? x).isSome = true ∧ (shallow? sp x).isSome = true) ∧
      xs.Pairwise (fun x y => deep y < deep x) ∧ xs.Pairwise (fun x y => shallow sp y < shallow sp x) then
    some ⟨xs,List.perm_insertionSort before _,h.1,h.2.1,h.2.2⟩ else none

/-- A source sorter can use either of the two earlier comparisons at an enqueue.
No seed, handedness, or later-rule tie-break is required in this molecule. -/
def Admissible (sp : SpatialConfiguration) (q : Cursor) (xs : List Cursor) : Prop :=
  xs.Perm (projected q) ∧ (xs.Pairwise (fun x y => deep y ≤ deep x) ∨
    xs.Pairwise (fun x y => shallow sp y ≤ shallow sp x))

private theorem unique_by_key {α K : Type} [LinearOrder K] (key : α → K) {xs ys : List α}
    (perm : xs.Perm ys) (strict : xs.Pairwise fun x y => key y < key x)
    (allowed : ys.Pairwise fun x y => key y ≤ key x) : xs = ys := by
  have neq : ys.Pairwise (fun x y => key y ≠ key x) :=
    (perm.pairwise_iff (fun h => Ne.symm h)).mp (strict.imp fun h => ne_of_lt h)
  have ranked := (List.pairwise_and_iff.mpr ⟨allowed,neq⟩).imp (fun h => lt_of_le_of_ne h.1 h.2)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ h k => False.elim (lt_asymm h k)) strict ranked perm

theorem Ranked.unique {sp q xs ys} (proved : Ranked sp q xs) (allowed : Admissible sp q ys) : xs = ys := by
  have perm := proved.children.trans allowed.1.symm
  rcases allowed.2 with lower | lower
  · exact unique_by_key deep perm proved.constitutional lower
  · exact unique_by_key (shallow sp) perm proved.currentUnit lower

inductive Walk (sp : SpatialConfiguration) : List Cursor → List Cursor → Prop where
  | done : Walk sp [] []
  | step {q qs children rest} (allowed : Admissible sp q children) (tail : Walk sp (qs ++ children) rest) :
      Walk sp (q :: qs) (q :: rest)

def queue? (sp : SpatialConfiguration) :
    Nat → List Cursor → Option (List Cursor)
  | _,[] => some []
  | 0,_ :: _ => none
  | fuel+1,q :: qs => do
    let children ← earlier? sp q
    let rest ← queue? sp fuel (qs ++ children.val)
    return q :: rest

theorem queue_exact {sp fuel start result} (computed : queue? sp fuel start = some result)
    {walk} (visited : Walk sp start walk) : walk = result :=  by
  induction fuel generalizing start result walk with
  | zero => cases visited with
    | done => exact Option.some.inj computed
    | step _ _ => contradiction
  | succ fuel ih => cases visited with
    | done => exact Option.some.inj computed
    | step h more =>
      unfold queue? at computed
      obtain ⟨children,_,next⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨rest,rec,out⟩ := Option.bind_eq_some_iff.mp next
      obtain rfl := Option.some.inj out
      rw [children.property.unique h] at rec
      exact congrArg (List.cons _) (ih rec more)

theorem queue_realized {sp fuel start result} (computed : queue? sp fuel start = some result) :
    Walk sp start result := by
  induction fuel generalizing start result with
  | zero => cases start with
    | nil => obtain rfl := Option.some.inj computed; exact .done
    | cons _ _ => contradiction
  | succ n ih => cases start with
    | nil => obtain rfl := Option.some.inj computed; exact .done
    | cons q qs =>
      unfold queue? at computed
      obtain ⟨children,_,next⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨rest,rec,out⟩ := Option.bind_eq_some_iff.mp next
      obtain rfl := Option.some.inj out
      exact .step ⟨children.property.children,.inl (children.property.constitutional.imp fun lt => le_of_lt lt)⟩ (ih rec)

/-- Cross-check every queue enqueue order against the full sparse molecular
hierarchies. This check simultaneously covers all siblings on each arm. -/
def fullQueue? (sp : SpatialConfiguration) (root arm : Nat) : Option Bool := do
  let q ← (occurrenceLigandCursors molecule (canonicalCenterRoot root)).find? (fun c => c.node.atom == arm)
  let visits ← queue? sp 16 [q]
  let orders ← visits.mapM fun c => do
    let cs ← earlier? sp c
    completeOrder? cs.val
  return orders.all id

def sourceWalk? (sp : SpatialConfiguration) (root arm : Nat) : Option (List (Option RS)) := do
  let q ← (occurrenceLigandCursors molecule (canonicalCenterRoot root)).find? (fun c => c.node.atom == arm)
  let actual ← queue? sp 16 [q]
  actual.mapM (read? sp)

/-- Every complete walk using either admissible sibling pass consumes the same
unfiltered vector, including all unlabelled positions. -/
theorem sourceWalk_exact {sp root arm out} (observed : sourceWalk? sp root arm = some out) :
    ∃ q ∈ occurrenceLigandCursors molecule (canonicalCenterRoot root), q.node.atom = arm ∧
      ∀ walk, Walk sp [q] walk → walk.mapM (read? sp) = some out := by
  unfold sourceWalk? at observed
  obtain ⟨q,found,rest⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨xs,checked,read⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨q,List.mem_of_find?_eq_some found,eq_of_beq (List.find?_some
    (p := fun c : Cursor => c.node.atom == arm) found),fun walk h => (queue_exact checked h).symm ▸ read⟩

/-- Each emitted sequence has a complete admissible walk from the selected
original ligand. This supplies existence as well as sorter independence. -/
theorem sourceWalk_realized {sp root arm out} (observed : sourceWalk? sp root arm = some out) :
    ∃ q ∈ occurrenceLigandCursors molecule (canonicalCenterRoot root), q.node.atom = arm ∧
      ∃ walk, Walk sp [q] walk ∧ walk.mapM (read? sp) = some out := by
  unfold sourceWalk? at observed
  obtain ⟨q,found,rest⟩ := Option.bind_eq_some_iff.mp observed
  obtain ⟨xs,checked,read⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨q,List.mem_of_find?_eq_some found,eq_of_beq (List.find?_some
    (p := fun c : Cursor => c.node.atom == arm) found),xs,queue_realized checked,read⟩

/-- Full earlier observations at every original molecular occurrence include
atomic number, ring-duplicate provenance and source mass, and the presence of
an uppercase tetrahedral unit. The remaining real carbons have equivalent
terminal ligands by omitted_carbons. -/
def earlierObservation (root : Nat) (q : Cursor) := do
  let o ← IsotopePriority.fullObservation? molecule [root] q
  return (o,!q.node.forcedLeaf && centers.contains q.node.atom)

def matched? (root left right : Nat) : Option Bool := do
  let row := occurrenceLigandCursors molecule (canonicalCenterRoot root)
  let l ← row.find? (fun q => q.node.atom == left)
  let r ← row.find? (fun q => q.node.atom == right)
  return IsotopePriority.treesMatch molecule (earlierObservation root) (IsotopePriority.budget molecule+1) l r

theorem matched_source {root left right} (ok : matched? root left right = some true) :
    let row := occurrenceLigandCursors molecule (canonicalCenterRoot root)
    ∃ l ∈ row, ∃ r ∈ row, l.node.atom = left ∧ r.node.atom = right ∧
      IsotopePriority.TreesMatch molecule (earlierObservation root) (IsotopePriority.budget molecule+1) l r := by
  unfold matched? at ok
  obtain ⟨l,hl,rest⟩ := Option.bind_eq_some_iff.mp ok
  obtain ⟨r,hr,tied⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨l,List.mem_of_find?_eq_some hl,r,List.mem_of_find?_eq_some hr,
    eq_of_beq (List.find?_some (p := fun q : Cursor => q.node.atom == left) hl),
    eq_of_beq (List.find?_some (p := fun q : Cursor => q.node.atom == right) hr),
    IsotopePriority.treesMatch_sound (Option.some.inj tied)⟩

theorem read_kind {sp q h} (found : read? sp q = some h) :
    h.isSome = (!q.node.forcedLeaf && centers.contains q.node.atom) := by
  cases leaf : q.node.forcedLeaf <;> cases center : centers.contains q.node.atom <;>
    rw [read?,leaf,center] at found
  all_goals first
    | (obtain rfl := (show (none : Option RS) = h from Option.some.inj found); rfl)
    | (obtain ⟨_,_,e⟩ := Option.map_eq_some_iff.mp found; cases e; rfl)

/-- Every molecular reading is uppercase or absent. Projecting an actual
reading into the existing Rule 4c ordinal therefore always yields zero. -/
theorem read_rule4c (h : Option RS) : RingNestedActivePair.lower (h.map (fun x => .chiral x)) = 0 := by
  cases h <;> rfl

theorem read_rule4a {sp q h} (found : read? sp q = some h) :
    RingNestedActivePair.unit (h.map (fun x => .chiral x)) =
      if !q.node.forcedLeaf && centers.contains q.node.atom then 2 else 0 := by
  rw [← read_kind found]
  cases h <;> rfl

def forward? (sp : SpatialConfiguration) (root left right : Nat) : Option Decision := do
  guard (← matched? root left right)
  let x ← sourceWalk? sp root left
  let y ← sourceWalk? sp root right
  fromVisits? x y x y x y

def walksDecision? (sp : SpatialConfiguration) (a b ar br as' bs : List Cursor) : Option Decision := do
  fromVisits? (← a.mapM (read? sp)) (← b.mapM (read? sp)) (← ar.mapM (read? sp))
    (← br.mapM (read? sp)) (← as'.mapM (read? sp)) (← bs.mapM (read? sp))

/-- The actual molecular result survives independent sorter and reference choices
in each of the six passes. Full earlier structural equivalence is required before
the source compares the paired descriptors. -/
theorem forward_source {sp root x y out} (found : forward? sp root x y = some out) :
    matched? root x y = some true ∧
    ∃ l ∈ occurrenceLigandCursors molecule (canonicalCenterRoot root),
    ∃ r ∈ occurrenceLigandCursors molecule (canonicalCenterRoot root),
      l.node.atom = x ∧ r.node.atom = y ∧
      ∀ a b ar br as' bs, Walk sp [l] a → Walk sp [r] b → Walk sp [l] ar → Walk sp [r] br →
        Walk sp [l] as' → Walk sp [r] bs → walksDecision? sp a b ar br as' bs = some out := by
  unfold forward? at found
  obtain ⟨t,tied,steps⟩ := Option.bind_eq_some_iff.mp found
  cases t with
  | false => contradiction
  | true =>
    obtain ⟨_,_,pass⟩ := Option.bind_eq_some_iff.mp steps
    obtain ⟨left,hl,rest⟩ := Option.bind_eq_some_iff.mp pass
    obtain ⟨right,hr,answer⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨l,lm,lid,allL⟩ := sourceWalk_exact hl
    obtain ⟨r,rm,rid,allR⟩ := sourceWalk_exact hr
    refine ⟨tied,l,lm,r,rm,lid,rid,?_⟩
    intro a b ar br as' bs a₁ b₁ a₂ b₂ a₃ b₃
    simpa [walksDecision?,allL _ a₁,allR _ b₁,allL _ a₂,allR _ b₂,allL _ a₃,allR _ b₃] using answer

def edges : List (Nat × Nat × Nat) := [(2,9,3),(3,6,2),(6,9,3),(9,6,2)]


end TetraStereo.Examples.RingPublishedTetraspiroAuxiliary
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.fixed_first
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.double_fixed
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.sparse_accepted
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.aligned_bits

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.Ranked.unique
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.queue_exact
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.sourceWalk_exact

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.matched_source
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.read_kind

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.queue_realized
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.forward_source

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.read_rule4a
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.read_rule4c

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.sourceWalk_realized

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.completeKey_source
