import TetraStereo.Engine.CentresRing

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.PairList
open OneCenter

/-- Compare the single like/unlike pairing in each list relative to one seed.
The current-root case of the release uses an R seed and an S seed separately. -/
def pairSign (seed left right : RS) : Int :=
  if left = right then 0 else if left = seed then 1 else -1

/-- Rule5New at a comparison root, after the two PairList.compareTo calls. -/
def combine (r s : Int) : Int :=
  if r < 0 then (if s < 0 then -1 else -2)
  else if r > 0 then (if s > 0 then 1 else 2) else 0

theorem doubled_exactly (r s : Int) :
    (combine r s).natAbs = 2 ↔ (r < 0 ∧ 0 ≤ s) ∨ (0 < r ∧ s ≤ 0) := by
  unfold combine
  split_ifs <;> simp_all
  omega

def singletonValue (left right : RS) : Int :=
  combine (pairSign .R left right) (pairSign .S left right)

theorem singleton_exact (left right : RS) :
    (singletonValue left right = 0 ↔ left = right) ∧
    (singletonValue left right = 2 ↔ left = .R ∧ right = .S) ∧
    (singletonValue left right = -2 ↔ left = .S ∧ right = .R) := by
  cases left <;> cases right <;> decide

/-- Paths in the occurrence tree, recorded from the original root forwards.
A label below the assignment is entered through the next step in its address.
Every other reachable label is entered through the assignment's parent. -/
def branchTo (focus other : List Nat) : Option Nat :=
  if focus.isPrefixOf other then other[focus.length]? else focus.reverse[1]?

structure Fact where
  path : List Nat
  hand : RS
  deriving Repr, DecidableEq

/-- Original-root occurrence address and published replay code. The code "-"
represents a completed assignment that returned Unknown. Absence from the
snapshot represents an unpublished occurrence. -/
structure Publication where
  path : List Nat
  code : String
  deriving DecidableEq

def occurrencePublications (t : CenterTrace) : List Publication :=
  t.updates.filterMap fun u => do
    let path ← t.discovered[u.index]?
    return ⟨path.reverse,u.label⟩

def publishedAt (facts : List Publication) (focus : List Nat) : List Publication :=
  facts.filter (fun fact => focus.length < fact.path.length)

theorem publishedAt_exact (facts : List Publication) (focus : List Nat) (f : Publication) :
    f ∈ publishedAt facts focus ↔ f ∈ facts ∧ focus.length < f.path.length := by
  simp [publishedAt]

/-- Only uppercase R/S facts enter the tetrahedral PairList projection. -/
def hands (visible : List Publication) : List Fact :=
  visible.filterMap fun f => do
    let hand ← (match f.code with | "R" => some RS.R | "S" => some RS.S | _ => none)
    return ⟨f.path,hand⟩

def armFacts (focus : List Nat) (ligand : Nat) (facts : List Fact) : List Fact :=
  facts.filter (fun f => branchTo focus f.path == some ligand)

/-- In the singleton case every visitation order gives precisely this descriptor. -/
theorem arm_order_independent {facts visit : List Fact} {focus : List Nat} {a : Nat} {f : Fact}
    (one : armFacts focus a facts = [f]) (order : visit.Perm facts) :
    armFacts focus a visit = [f] := by
  have p := order.filter (fun f => branchTo focus f.path == some a)
  change (armFacts focus a visit).Perm (armFacts focus a facts) at p
  simpa [one] using p

inductive Phase where
  | constitutional | auxiliary | full
  deriving DecidableEq, Repr

structure Site where
  phase : Phase
  focus : List Nat
  mark : Option Nat
  /-- None identifies an adjacent grouping comparison; otherwise the sort trial index. -/
  trial : Option Nat
  visible : List Publication
  comparison : Comparison

/-- At a rerooted focus the old parent is a ligand at its existing address.
All other ligands extend the original path, including ring-closure leaves. -/
def ligandOccurrence (focus : List Nat) (atom : Nat) : List Nat :=
  if focus.reverse[1]? == some atom then focus.dropLast else focus ++ [atom]

theorem ligandOccurrence_parent (rootToParent : List Nat) (parent focus : Nat) :
    ligandOccurrence (rootToParent ++ [parent,focus]) parent = rootToParent ++ [parent] := by
  simp [ligandOccurrence]

theorem ligandOccurrence_child (focus : List Nat) (a : Nat) (down : focus.reverse[1]? ≠ some a) :
    ligandOccurrence focus a = focus ++ [a] := by simp [ligandOccurrence,down]

def Site.leftFacts (s : Site) : List Fact := armFacts s.focus s.comparison.left (hands s.visible)
def Site.rightFacts (s : Site) : List Fact := armFacts s.focus s.comparison.right (hands s.visible)

def Site.derived (s : Site) : Option Int := do
  let [l] := s.leftFacts | none
  let [r] := s.rightFacts | none
  return singletonValue l.hand r.hand

private def sites (phase : Phase) (focus : List Nat) (visible : List Publication) (p : Pass) :
    List Site :=
  let atMark (trial mark : Option Nat) (cs : List Comparison) :=
    cs.map fun c => Site.mk phase focus mark trial visible c
  let groups := atMark none (p.trials.head?.bind Trial.mark) p.groups
  match p.trials with
  | [] => groups
  | first :: rest =>
    atMark (some 0) first.mark first.comparisons ++ groups ++
      rest.zipIdx.flatMap (fun (t,i) => atMark (some (i+1)) t.mark t.comparisons)

/-- Root versus auxiliary chronology of an accepted transcript. Equal-distance
auxiliary results are withheld. At the full root pass every auxiliary is published. -/
def comparisonSites (t : CenterTrace) : List Site :=
  let publications := occurrencePublications t
  let first := t.passes.take 1 |>.flatMap (sites .constitutional [t.atom] [])
  let full := t.passes.drop 1 |>.flatMap (sites .full [t.atom] publications)
  let aux := t.updates.flatMap fun u =>
    match t.discovered[u.index]? with
    | none => []
    | some reversePath =>
      let focus := reversePath.reverse
      sites .auxiliary focus (publishedAt publications focus) u.pass
  first ++ aux ++ full

/-- Lists every observed magnitude greater than one, including grouping calls.
A missing derivation remains visible in the result. -/
def doubledSites (ts : List CenterTrace) : List Site :=
  (ts.flatMap comparisonSites).filter fun s => s.comparison.value.natAbs > 1

end TetraStereo.Engine.CentresRing.PairList
assert_kernel_only TetraStereo.Engine.CentresRing.PairList.doubled_exactly
assert_kernel_only TetraStereo.Engine.CentresRing.PairList.singleton_exact
assert_kernel_only TetraStereo.Engine.CentresRing.PairList.publishedAt_exact
assert_kernel_only TetraStereo.Engine.CentresRing.PairList.arm_order_independent
assert_kernel_only TetraStereo.Engine.CentresRing.PairList.ligandOccurrence_parent
assert_kernel_only TetraStereo.Engine.CentresRing.PairList.ligandOccurrence_child
