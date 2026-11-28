import TetraStereo.Engine.RingLigandExchange

/-! Match molecular ligand arms by their unordered observed subtrees. The candidate
correspondence uses constitutional observations, frozen reads and the optional atom
mark. Atom IDs and sibling positions do not enter the tree signature. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingObservedTreeMatch
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame Reader)
open RingGroupedCentre (cursor)
open RingGeometryExchange (Carrier Frozen Exchange)
open RingRetainedChemicalTrace (observation?)
open RingBranchMatching (Rows)
open private matchRows from TetraStereo.Engine.RingGeometryExchange
attribute [local instance] lexOrd

/-- Preorder addresses are retained for the certificate, independently of the
labelled subtree encoding used to sort siblings. -/
private structure Tree (i : Input) where
  key : List Nat
  preorder : List (Arm i)

private def labelCode : LocalizedAuxiliaryLabel → Nat
  | .chiral .R => 0
  | .chiral .S => 1
  | .pseudoasymmetric .r => 2
  | .pseudoasymmetric .s => 3

private def readCode : RingActiveDistanceSchedule.Cell → Nat
  | none => 0
  | some none => 1
  | some (some (a,b)) => 2 + 4 * labelCode a + labelCode b

private def tree {i : Input} (r : Reader i) (mark : Option Nat)
    (children : Arm i → List (Arm i)) : Nat → Arm i → Option (Tree i)
  | 0,_ => none
  | n+1,q => do
    let kids := children q
    let ts ← kids.mapM (tree r mark children n)
    let sorted := RingStereoSiblingPass.order Tree.key ts
    let o := observation? i q kids.isEmpty
    let obs := o.elim [0] (fun v => [1,v.atomic,v.duplicate,v.mass])
    let marked := mark.elim 0 (fun a => RingGroupedMark.bit a q)
    let header := readCode (r q.occurrence) :: marked :: kids.length :: obs
    return ⟨header ++ (sorted.map Tree.key).flatMap (fun k => k.length :: k),
      q :: sorted.flatMap Tree.preorder⟩

private abbrev kids {i : Input} := i.certified.executableLocalizedRerootChildren
    (fuel := i.certified.certified.input.molecule.atomCount+1)

private theorem full_children {α β : Type} {fn : α → Option β} (xs : List α)
    (h : ∀ x ∈ xs, ∃ y, fn x = some y) : ∃ ys, xs.mapM fn = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨v,hv⟩ := h x List.mem_cons_self
    obtain ⟨vs,hvs⟩ := ih fun t ht => h t (List.mem_cons_of_mem x ht)
    exact ⟨v::vs,by rw [List.mapM_cons,hv,hvs]; rfl⟩

private theorem total_tree {i : Input} (r : Reader i) (m : Option Nat)
    (n : Nat) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (enough : i.certified.localizedRerootCursorBudget q < n) :
    ∃ t, tree r m kids n q = some t := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    obtain ⟨cs,hc⟩ := full_children (kids q) (fn := tree r m kids n) (fun a ha =>
      ih a (i.certified.localizedRerootChild_valid q a _ frame ha)
        (by have := i.certified.localizedRerootChild_budget_lt q a _ valid frame ha; omega))
    simp [tree,hc]

private theorem same_key {i j : Input} (c : Carrier i j) {r : Reader i} {s : Reader j}
    (frozen : Frozen c r s) (m m' : Option Nat)
    (marked : ∀ q, c.domain q → m.elim 0 (fun a => RingGroupedMark.bit a q) =
      m'.elim 0 (fun a => RingGroupedMark.bit a (c.image q)))
    (n k : Nat) (q : Arm i) (on : c.domain q) {x : Tree i} {y : Tree j}
    (l : tree r m kids n q = some x) (h : tree s m' kids k (c.image q) = some y) :
    x.key = y.key := by
  induction n generalizing q k x y with
  | zero => contradiction
  | succ n ih =>
    cases k with
    | zero => contradiction
    | succ k =>
      obtain ⟨ls,hl,l⟩ := Option.bind_eq_some_iff.mp l
      obtain ⟨rs,hr,h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj l
      obtain rfl := Option.some.inj h
      have edges := c.children q on
      have perm : (ls.map Tree.key).Perm (rs.map Tree.key) := by
        simpa only [← List.map_eq_flatMap] using matchRows edges hl hr (fun t => [t.key]) (fun t => [t.key])
          (fun a ha _ _ hx hy => List.Perm.of_eq (congrArg List.singleton
            (ih _ _ (c.below q on a ha) hx hy)))
      have lsrt := RingStereoSiblingPass.legal_order Tree.key ls
      have rsrt := RingStereoSiblingPass.legal_order Tree.key rs
      have sorted := List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
        lsrt.descending rsrt.descending (((lsrt.perm.map Tree.key).trans perm).trans
          (rsrt.perm.map Tree.key).symm)
      have count : (kids q).length = (kids (c.image q)).length := by simpa using edges.length_eq
      simp only [sorted,count,frozen q on,marked q on,c.observation q on]

/-- Exact canonical encoding on the entire unfolding of a valid cursor.
There is no caller-supplied cutoff. -/
def signature {i : Input} (r : Reader i) (m : Option Nat) (q : Arm i) : Option (List Nat) :=
  (tree r m kids (i.certified.localizedRerootCursorBudget q + 1) q).map Tree.key

/-- An observed tree correspondence always reaches identical, present canonical
signatures, regardless of the depths used by the two executions, sibling
permutations or cursor IDs. A later functional row check separately certifies
that the particular reconstructed matching is consistent across revisits. -/
theorem signature_transport {i j : Input} (c : Carrier i j) {r : Reader i} {s : Reader j}
    (frozen : Frozen c r s) (m m' : Option Nat)
    (marked : ∀ q, c.domain q → m.elim 0 (fun a => RingGroupedMark.bit a q) =
      m'.elim 0 (fun a => RingGroupedMark.bit a (c.image q)))
    (q : Arm i) (on : c.domain q) (valid : i.certified.LocalizedRerootCursorValid q)
    (valid' : j.certified.LocalizedRerootCursorValid (c.image q)) :
    ∃ k, signature r m q = some k ∧ signature s m' (c.image q) = some k := by
  obtain ⟨x,hx⟩ := total_tree r m _ q valid (Nat.lt_succ_self _)
  obtain ⟨y,hy⟩ := total_tree s m' _ (c.image q) valid' (Nat.lt_succ_self _)
  exact ⟨x.key,by simp [signature,hx],by simp [signature,hy,same_key c frozen m m' marked _ _ q on hx hy]⟩

private def candidate {i : Input} (l r : Option (Tree i)) : Option (Rows i) := do
  let a ← l
  let b ← r
  guard (a.key == b.key)
  return a.preorder.zip b.preorder

private def observed {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (mark : Option Nat) (children : Arm i → List (Arm i)) (u : Slot) :=
  let q := cursor fr u
  tree r mark children (i.certified.localizedRerootCursorBudget q + 1) q

private def cachedChildren {i : Input} (f : Site i) : Arm i → List (Arm i) :=
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount+1)) f.val.root
  fun q => (cache.reader.readChildren q).getD []

private theorem children_exact {i : Input} (f : Site i) (q : Arm i) :
    cachedChildren f q = i.certified.executableLocalizedRerootChildren q := by
  unfold cachedChildren
  rw [LocalizedRerootChildReader.readChildren_eq]
  rfl

/-- Propose corresponding occurrence rows from canonical observed subtrees. -/
def propose {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (m : Option Nat)
    (u v : Slot) : Option (Rows i) :=
  let get := observed fr r m (cachedChildren f)
  candidate (get u) (get v)

/-- If an exchange already exists, the automatic proposer always produces
rows, regardless of how that witness orders siblings. The independent
checker still verifies the specific proposed functional correspondence. -/
theorem propose_of_exchange {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    {s u v : Slot} (e : Exchange fr r s u v) :
    (propose fr r (some (RingGroupedTrials.atom fr s)) u v).isSome = true := by
  let m := some (RingGroupedTrials.atom fr s)
  have lhs := RingGroupedCentre.valid fr u
  have rhs := RingGroupedCentre.valid fr v
  obtain ⟨k,hk,hl⟩ := signature_transport e.carrier e.frozen m m e.selected
    (cursor fr u) e.atLigand lhs (e.other.symm ▸ rhs)
  rw [e.other] at hl
  have cache : cachedChildren f = kids := funext (children_exact f)
  unfold signature at hk hl
  obtain ⟨a,ha,ak⟩ := Option.map_eq_some_iff.mp hk
  obtain ⟨b,hb,bk⟩ := Option.map_eq_some_iff.mp hl
  change (propose fr r m u v).isSome = true
  simp [propose,observed,cache,candidate,ha,hb,ak,bk]

/-- A checked pair for one nomination. Equal signatures propose concrete rows.
The branch checker validates their complete child correspondence, elementary
observations, both frozen labels and the nominated atom at every occurrence. -/
def pair {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (s u v : Slot) :
    Option (Exchange fr r s u v) := do
  let rows ← propose fr r (some (RingGroupedTrials.atom fr s)) u v
  RingBranchMatching.check? fr r s u v rows

/-- A correspondence on the complete, unmarked, observed arm. -/
structure Unmarked {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (u v : Slot) where
  carrier : Carrier i i
  start : carrier.domain (cursor fr u)
  target : carrier.image (cursor fr u) = cursor fr v
  frozen : Frozen carrier r r

private def checkUnmarked {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (u v : Slot) (rows : Rows i) : Option (Unmarked fr r u v) := do
  let domain := rows.map Prod.fst
  let image (q : Arm i) := ((rows.find? (fun e => e.1 == q)).map Prod.snd).getD (cursor fr v)
  let children := cachedChildren f
  if start : cursor fr u ∈ domain ∧ image (cursor fr u) = cursor fr v then
    if ok : ∀ q ∈ domain, (∀ h ∈ children q, h ∈ domain) ∧
        ((children q).map image).Perm (children (image q)) ∧
        observation? i q (children q).isEmpty = observation? i (image q) (children (image q)).isEmpty ∧
        r q.occurrence = r (image q).occurrence then
      let c : Carrier i i := {
        image := image
        domain := (· ∈ domain)
        below := fun q h => by simpa only [children,children_exact] using (ok q h).1
        children := fun q h => by simpa only [children,children_exact] using (ok q h).2.1
        observation := fun q h => by simpa only [children,children_exact] using (ok q h).2.2.1 }
      return ⟨c,start.1,start.2,fun q h => (ok q h).2.2.2⟩
    else none
  else none

/-- The same reconstruction without promotion. The resulting tree correspondence
preserves every ordinary full-path key on a ready reader. -/
def unmarked? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (u v : Slot) :
    Option (Unmarked fr r u v) := do
  let rows ← propose fr r none u v
  checkUnmarked fr r u v rows

private def checkedNomination {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (children : Arm i → List (Arm i)) (s : Slot) :=
  let arms := Vector.ofFn (observed fr r (some (RingGroupedTrials.atom fr s)) children)
  (List.finRange 4).any fun u => (List.finRange 4).any fun v => u < v &&
    ((candidate arms[u] arms[v]).bind (RingBranchMatching.check? fr r s u v)).isSome

/-- Search the six unordered pairs for each of the four nominations. Each arm
is normalized once per nomination. Terminal sibling ties use stable ordering.
If one source cursor is revisited, the proposed rows must pass the same functional
consistency check as every other certificate. Failure supplies no descriptor. -/
def check {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Bool :=
  let children := cachedChildren f
  (List.finRange 4).all (checkedNomination fr r children)

theorem check_sound {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (ok : check fr r = true) : RingLigandExchange.PerNomination fr r := by
  intro s
  have good := List.all_eq_true.mp ok s (List.mem_finRange s)
  obtain ⟨u,_,hit⟩ := List.any_eq_true.mp good
  obtain ⟨v,_,found⟩ := List.any_eq_true.mp hit
  obtain ⟨lt,yes⟩ := Bool.and_eq_true_iff.mp found
  exact ⟨u,v,ne_of_lt (of_decide_eq_true lt),⟨Option.get _ yes⟩⟩

end TetraStereo.Engine.RingObservedTreeMatch
assert_kernel_only TetraStereo.Engine.RingObservedTreeMatch.pair
assert_kernel_only TetraStereo.Engine.RingObservedTreeMatch.unmarked?
assert_kernel_only TetraStereo.Engine.RingObservedTreeMatch.check_sound
assert_kernel_only TetraStereo.Engine.RingObservedTreeMatch.signature_transport
assert_kernel_only TetraStereo.Engine.RingObservedTreeMatch.propose_of_exchange
