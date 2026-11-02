import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-!
  Shared branch ranking for perception layers.

  Both tetrahedral centres and alkene ends need the same question answered: given an atom and one of
  its neighbours, how does that branch rank against another?  This module answers it once, so the
  two perception paths cannot drift apart in strength or in convention.

  Production ranking compiles each branch into a bounded acyclic CIP digraph. Nodes retain their
  parent slot and duplicate provenance; child branches are ordered by complete rule-major keys; and
  each whole sphere is compared before exploration descends. Sparse positional paths represent
  missing phantom slots without materializing an exponentially wide phantom tree.

  ### What this is and is not

  Rules 1a, 1b and 2 are applied exhaustively in rule-major order. Rule 1a includes exact rational
  averaging for every finite localized mancude system via maximum matchings, plus an exact
  shortcut for uniform perfect-matching components;
  Rule 1b compares the root distance assigned to every node; Rule 2 uses exact isotope masses and natural atomic
  weights. Rules 3 through 5 are attached later to the compiled positional paths by
  `SmilesTetrahedral`. Exploration is bounded, and a tied
  truncated key is unresolved rather than a chemical tie. The historical sphere-multiset and local
  paired comparators remain below only as differential diagnostics.

  Everything here is computable and structurally recursive, so results can be evaluated rather than
  only reasoned about.  That rules out `List.mergeSort`, which is well-founded recursion and does not
  reduce in the kernel.

  Ranking is materially sharper when implicit hydrogens have been made explicit.  Hydrogen is the
  lowest-ranking neighbour, so omitting it can turn a sphere that should decide into a tie: `[6,1,1]`
  against `[6,1]` decides on the trailing hydrogen, while `[6]` against `[6]` does not.
-/

/-- Structural insertion into a list ordered by `before`; reduces in the kernel, unlike
`List.mergeSort`. -/
def insertDescBy {α : Type*} (before : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if before x y then x :: y :: ys else y :: insertDescBy before x ys

/-- Structural insertion sort. -/
def sortDescBy {α : Type*} (before : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertDescBy before x (sortDescBy before xs)

namespace RawMolecule

/-- Atomic number of a parsed atom, `0` for an index that is not present. -/
def atomZAt (mol : RawMolecule) (idx : ℕ) : ℕ :=
  match mol.atomAt? idx with
  | some spec => spec.element.atomicNumber
  | none => 0

@[simp] theorem rule2MassPico_hydrogen_eq_protium :
    rule2MassPico Element.H none = rule2MassPico Element.H (some 1) := by
  decide

theorem rule2MassPico_hydrogen_lt_deuterium :
    rule2MassPico Element.H none < rule2MassPico Element.H (some 2) := by
  decide

theorem rule2MassPico_bromine79_lt_ordinary_lt_bromine81 :
    rule2MassPico Element.Br (some 79) < rule2MassPico Element.Br none ∧
      rule2MassPico Element.Br none < rule2MassPico Element.Br (some 81) := by
  decide

@[simp] theorem rule2MassPico_carbon999_unknown :
    rule2MassPico? Element.C (some 999) = none := by
  decide

/-- The production hierarchical comparator and the proof-facing molecular graph read precisely the
same exact Rule-2 datum at every real atom index. -/
theorem atomMassAt_eq_toMoleculeGraph_atomMass (mol : RawMolecule) (idx : ℕ)
    (bound : idx < mol.atomCount) :
    mol.atomMassAt idx = mol.toMoleculeGraph.atomMass ⟨idx, bound⟩ := by
  rfl

/-- Descending insertion.  Structural, so it reduces in the kernel. -/
def insertDescNat (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if y ≤ x then x :: y :: ys else y :: insertDescNat x ys

/-- Descending insertion sort. -/
def sortDescNat : List ℕ → List ℕ
  | [] => []
  | x :: xs => insertDescNat x (sortDescNat xs)

/-- A node of a branch expansion.

`duplicate` marks a CIP duplicate atom: the extra copies a multiple bond contributes, and the
revisited atom that closes a ring.  A duplicate carries the atomic number of the atom it duplicates
but has **no substituents of its own**, so it is a leaf.  Expanding it instead — as replicating the
neighbour and walking both copies does — inflates every sphere beyond a double bond and is not what
the sequence rules describe.

`rootDistance` records how far the duplicated atom sits from the branch root, which is what Rule 1b
ranks duplicates by. -/
structure BranchNode where
  atom : ℕ
  parent : ℕ
  visited : List ℕ
  duplicate : Bool
  rootDistance : ℕ
  deriving DecidableEq, Repr

/-- Neighbours of `current`, with the extra copies a multiple bond contributes marked as duplicates
and one occurrence of `parent` removed. -/
def branchChildren (mol : RawMolecule) (parent current depth : ℕ) : List BranchNode :=
  let neighbours :=
    mol.bonds.flatMap fun bond =>
      if bond.source == current then List.replicate bond.kind.order bond.target
      else if bond.target == current then List.replicate bond.kind.order bond.source
      else []
  let remaining := neighbours.erase parent
  -- Within one neighbour, the first occurrence is the real atom and any further occurrences are
  -- duplicates contributed by the multiple bond.
  (remaining.foldl
    (fun acc atom =>
      let seenBefore := acc.any fun node => node.atom == atom
      acc ++ [{ atom := atom, parent := current, visited := [], duplicate := seenBefore,
                rootDistance := depth + 1 }])
    []).map fun node => node

/-- Children of a frontier node with path revisits marked as CIP ring duplicates.

The closure atom contributes its label once but is a duplicate leaf.  Recording that fact on the
child, rather than merely stopping when it is later expanded, is load-bearing for Rule 1b and Rule 2. -/
def branchChildrenOnPath (mol : RawMolecule) (node : BranchNode) : List BranchNode :=
  let path := node.atom :: node.visited
  (mol.branchChildren node.parent node.atom node.rootDistance).map fun child =>
    { child with
      visited := path
      duplicate := child.duplicate || path.contains child.atom }

/-- One breadth-first step over a branch frontier.

A duplicate never expands.  Nor does an atom already on its own path: that revisit is a ring-closure
duplicate, which contributes its label to the current sphere and stops. -/
def expandBranchFrontier (mol : RawMolecule) (frontier : List BranchNode) : List BranchNode :=
  frontier.flatMap fun node =>
    if node.duplicate || node.visited.contains node.atom then []
    else
      mol.branchChildrenOnPath node

/-- Lexicographic comparison within one sphere; a branch that runs out of atoms loses. -/
def compareSphere : List ℕ → List ℕ → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: as, b :: bs =>
      if b < a then Ordering.gt else if a < b then Ordering.lt else compareSphere as bs

/-- Compare two branch keys sphere by sphere.  Nearer spheres decide first. -/
def compareSpheres : List (List ℕ) → List (List ℕ) → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: as, b :: bs =>
      match compareSphere a b with
      | Ordering.eq => compareSpheres as bs
      | other => other

/-- Cap on how wide one sphere of a branch may get before exploration gives up.

A branch is explored as a tree of simple paths, so a fused polycyclic system multiplies paths and a
frontier can grow without practical bound.  Ordinary molecules resolve within the first few spheres;
a comparison still unresolved once a sphere exceeds this width is refused rather than pursued, so
analysis is always bounded in time. -/
def defaultBranchWidthCap : ℕ := 20000

/-- Compare two branches sphere by sphere under a single ranking key, expanding only as far as the
comparison requires.

`key` is the per-atom value the sequence rule ranks by: atomic number for Rule 1a, isotope mass for
Rule 2.  Keeping it a parameter is what makes rule-major comparison possible — a rule is applied
exhaustively across the whole branch before the next rule is consulted, which is what CIP requires
and what a single blended key cannot express.

Nearer spheres decide first, and expansion stops at the first sphere that separates the branches, so
most comparisons settle within three spheres and the full key is never built.  Returns `none` when
either frontier exceeds `cap`, which callers must treat as a refusal and never as a tie. -/
def compareFrontiersBy (mol : RawMolecule) (key : RawMolecule → BranchNode → ℕ) (cap : ℕ) :
    ℕ → List BranchNode → List BranchNode → Option Ordering
  | 0, _, _ => some Ordering.eq
  | _ + 1, [], [] => some Ordering.eq
  | _ + 1, [], _ :: _ => some Ordering.lt
  | _ + 1, _ :: _, [] => some Ordering.gt
  | fuel + 1, left, right =>
      if cap < left.length || cap < right.length then
        none
      else
        match compareSphere
            (sortDescNat (left.map fun node => key mol node))
            (sortDescNat (right.map fun node => key mol node)) with
        | Ordering.eq =>
            mol.compareFrontiersBy key cap fuel
              (mol.expandBranchFrontier left) (mol.expandBranchFrontier right)
        | other => some other

/-- Atoms reachable from `start` without passing through `blocked`, up to `fuel` steps. -/
def reachableAvoiding (mol : RawMolecule) : ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, seen => seen
  | _ + 1, _, [], seen => seen
  | fuel + 1, blocked, frontier, seen =>
      let next :=
        (frontier.flatMap fun atom =>
          mol.bonds.filterMap fun bond =>
            if bond.source == atom && bond.target != blocked then some bond.target
            else if bond.target == atom && bond.source != blocked then some bond.source
            else none).filter fun atom => !(seen.contains atom)
      let fresh := next.eraseDups
      mol.reachableAvoiding fuel blocked fresh (seen ++ fresh)

/-- How many pairs of a centre's ligands are joined by a path that avoids the centre.

Each such pair is a ring through the centre.  One pair is an ordinary ring stereocentre.  Two or
more means the centre is polycyclic — a fusion or bridgehead atom — and there the sphere-multiset
ranking is unfaithful: branches that rejoin share atoms, so the multiset counts them on both sides
where a branch-wise comparison keeps them apart. -/
def ringPairCount (mol : RawMolecule) (fuel center : ℕ) (ligands : List ℕ) : ℕ :=
  ((List.range ligands.length).flatMap fun i =>
    (List.range ligands.length).filterMap fun j =>
      if i < j then
        let a := ligands.getD i 0
        let b := ligands.getD j 0
        if (mol.reachableAvoiding fuel center [a] [a]).contains b then some (i, j) else none
      else none).length

/-! ### Paired comparison, the way a chemist does it

A chemist never pools every atom at a given distance into one bag.  They rank the atoms attached to
the centre; where two tie they write out that atom's substituent set — `-COOH` is `(O,O,O)`,
`-CH2OH` is `(O,H,H)` — and compare those sets highest-to-highest, second-to-second,
third-to-third.  If the sets still tie they descend into the *highest-ranked* branch of each, and
the two branches stay paired the whole way down.

That pairing is what a sphere multiset destroys: merging everything at depth three into one sorted
list makes a substituent hanging off an oxygen indistinguishable from one hanging off a carbon.
This section keeps nodes paired and compares them set by set, level by level, which is both
sphere-major (nearer levels decide first) and parent-ranked (pairing follows the ranking above). -/

/-- Whether a paired-comparison node has no chemically meaningful descendants. -/
def branchNodeTerminal (mol : RawMolecule) (node : BranchNode) : Bool :=
  node.duplicate || node.visited.contains node.atom ||
    (mol.branchChildrenOnPath node).isEmpty

/-- The substituent set of a node: its children's atomic numbers, highest first, padded with
phantoms so that a missing substituent is compared against a present one rather than shifting the
comparison out of alignment. -/
def nodeSet (mol : RawMolecule) (width : ℕ) (node : BranchNode) : List ℕ :=
  if mol.branchNodeTerminal node then
    List.replicate width 0
  else
    let kids := (mol.branchChildrenOnPath node).map fun k =>
      mol.atomZAt k.atom
    let sorted := sortDescNat kids
    sorted ++ List.replicate (width - min width sorted.length) 0

/-- Local rank of a node: its own atomic number, then its substituent set. -/
def nodeRankBefore (mol : RawMolecule) (width : ℕ) (a b : BranchNode) : Bool :=
  match compare (mol.atomZAt a.atom) (mol.atomZAt b.atom) with
  | Ordering.gt => true
  | Ordering.lt => false
  | Ordering.eq => compareSphere (mol.nodeSet width a) (mol.nodeSet width b) != Ordering.lt

/-- Children of a node in ranked order, padded to `width` with phantom leaves so that two paired
nodes always present the same number of slots. -/
def rankedChildren (mol : RawMolecule) (width : ℕ) (node : BranchNode) : List BranchNode :=
  let kids :=
    if mol.branchNodeTerminal node then []
    else mol.branchChildrenOnPath node
  let sorted := sortDescBy (mol.nodeRankBefore width) kids
  sorted ++ List.replicate (width - min width sorted.length)
    { atom := mol.atomCount, parent := node.atom, visited := [], duplicate := true,
      rootDistance := node.rootDistance + 1 }

/-- Compare two branches level by level with their nodes kept paired.

Each level compares every paired node's substituent set, in ranking order, and the first difference
decides.  Only when a whole level ties does comparison descend, and it descends into every pair at
once — so a nearer level always outranks a farther one, which is what a sphere-flattening comparison
gets wrong in the other direction. -/
def comparePairedLevels (mol : RawMolecule) (width cap : ℕ) :
    ℕ → List (BranchNode × BranchNode) → Option Ordering
  | 0, [] => some Ordering.eq
  | 0, _ :: _ => none
  | _ + 1, [] => some Ordering.eq
  | fuel + 1, pairs =>
      if cap < pairs.length then none
      else
        let decided :=
          pairs.foldl
            (fun acc pair =>
              match acc with
              | Ordering.eq => compareSphere (mol.nodeSet width pair.1) (mol.nodeSet width pair.2)
              | other => other)
            Ordering.eq
        match decided with
        | Ordering.eq =>
            if pairs.all fun pair =>
                mol.branchNodeTerminal pair.1 && mol.branchNodeTerminal pair.2 then
              some Ordering.eq
            else
              let next :=
                pairs.flatMap fun pair =>
                  (mol.rankedChildren width pair.1).zip (mol.rankedChildren width pair.2)
              mol.comparePairedLevels width cap fuel next
        | other => some other

/-- Rule 1a key: atomic number. -/
def rule1aKey (mol : RawMolecule) (node : BranchNode) : ℕ :=
  mol.atomZAt node.atom

/-- Rule 1b key: a duplicate atom ranks below a real one, and among duplicates the one whose
duplicated atom lies closer to the branch root ranks higher.

The offset keeps every value positive while preserving that ordering, so the same descending
sphere comparison applies unchanged. -/
def rule1bKey (_mol : RawMolecule) (node : BranchNode) : ℕ :=
  if node.duplicate then 1000 - min node.rootDistance 999 else 1001

/-- Rule 2 key: isotope mass. -/
def rule2Key (mol : RawMolecule) (node : BranchNode) : ℕ :=
  if node.duplicate then 0 else mol.atomMassAt node.atom

/-- Depth of the parent-preserving cross-check.  Disagreements beyond a few spheres are vanishingly
rare and the check is exponential, so it is deliberately shallow. -/
def crossCheckDepth : ℕ := 6

/-- Parent-preserving comparison of two branches: compare the atoms themselves, then their children
pairwise in ranked order, keeping each child attached to its parent.

This is *not* used to produce descriptors.  It exists only to disagree with the sphere-multiset
ranking exactly where that ranking is unfaithful — a sphere multiset aggregates atoms across
sub-branches, so it can separate two branches for a reason a branch-wise comparison would not
accept, which is how fused ring systems go wrong.  A defect in this function can therefore only
cause an extra refusal, never a wrong descriptor. -/
def compareBranchwise (mol : RawMolecule) :
    ℕ → List ℕ → List ℕ → ℕ → ℕ → ℕ → ℕ → Ordering
  | 0, _, _, _, _, _, _ => Ordering.eq
  | fuel + 1, seenL, seenR, parentL, atomL, parentR, atomR =>
      match compare (mol.atomZAt atomL) (mol.atomZAt atomR) with
      | Ordering.eq =>
          if seenL.contains atomL || seenR.contains atomR then Ordering.eq
          else
            let kidsL := (mol.branchChildren parentL atomL 0).map fun n => n.atom
            let kidsR := (mol.branchChildren parentR atomR 0).map fun n => n.atom
            let rank : ℕ → List ℕ → ℕ → ℕ → Bool := fun p _ a b =>
              mol.compareBranchwise fuel (atomL :: seenL) (atomR :: seenR) p a p b != Ordering.lt
            let sortedL := sortDescBy (fun a b => rank atomL seenL a b) kidsL
            let sortedR := sortDescBy (fun a b => rank atomR seenR a b) kidsR
            let rec walk : List ℕ → List ℕ → Ordering
              | [], [] => Ordering.eq
              | [], _ :: _ => Ordering.lt
              | _ :: _, [] => Ordering.gt
              | a :: as, b :: bs =>
                  match mol.compareBranchwise fuel (atomL :: seenL) (atomR :: seenR)
                      atomL a atomR b with
                  | Ordering.eq => walk as bs
                  | other => other
            walk sortedL sortedR
      | other => other

/-! ### Canonical, parent-ranked hierarchical digraph

The legacy sphere comparator above is retained as a diagnostic and for theorem compatibility.  The
production comparison below keeps duplicate provenance and branch parentage, ranks siblings by a
recursively refined comparison of their complete sub-branches, and then compares each whole sphere
before descending.  This is the sphere-major, parent-ranked order required by the CIP digraph.
-/

/-- Exact Rule-1a label.  A denominator greater than one represents a mancude/Kekulé average. -/
structure CIPAtomicLabel where
  numerator : ℕ
  denominator : ℕ
  deriving DecidableEq, Repr

/-- Positive denominator used by the total label comparator.

Production labels always have a positive denominator.  Totalizing malformed hand-built labels at
one prevents the otherwise degenerate `0/0` value from destroying comparator transitivity. -/
def CIPAtomicLabel.effectiveDenominator (label : CIPAtomicLabel) : ℕ :=
  max label.denominator 1

/-- Exact comparison of nonnegative rational atomic-number labels. -/
def compareCIPAtomicLabel (left right : CIPAtomicLabel) : Ordering :=
  compare (left.numerator * right.effectiveDenominator)
    (right.numerator * left.effectiveDenominator)

@[simp] theorem compareCIPAtomicLabel_self (label : CIPAtomicLabel) :
    compareCIPAtomicLabel label label = Ordering.eq := by
  simp [compareCIPAtomicLabel]

/-- Provenance retained by every node of the production CIP digraph. -/
inductive CanonicalNodeProvenance where
  | realAtom
  | multipleBondDuplicate (rootDistance : ℕ)
  | ringDuplicate (rootDistance : ℕ)
  | phantom (rootDistance : ℕ)
  deriving DecidableEq, Repr

/-- One node in a branch-local, acyclic CIP digraph.  `history` starts at `atom` and ends at the
stereogenic-unit root. -/
structure CanonicalBranchNode where
  atom : ℕ
  parent : ℕ
  history : List ℕ
  provenance : CanonicalNodeProvenance
  deriving DecidableEq, Repr

namespace CanonicalBranchNode

/-- Topological distance of a real node from the stereogenic-unit root. -/
def depth (node : CanonicalBranchNode) : ℕ :=
  node.history.length - 1

/-- Duplicate and phantom nodes are leaves by construction. -/
def forcedLeaf (node : CanonicalBranchNode) : Bool :=
  match node.provenance with
  | CanonicalNodeProvenance.realAtom => false
  | _ => true

/-- Revised Rule-1b root distance.

Ring duplicates use the sphere of the duplicated atom; multiple-bond duplicates use the sphere of
the atom to which they are attached; every other node uses its own sphere.  Assigning a distance to
every node is load-bearing: treating real nodes as "inapplicable" makes the induced branch
comparison non-transitive. -/
def rule1bRootDistance (node : CanonicalBranchNode) : ℕ :=
  match node.provenance with
  | CanonicalNodeProvenance.multipleBondDuplicate distance => distance
  | CanonicalNodeProvenance.ringDuplicate distance => distance
  | CanonicalNodeProvenance.phantom distance => distance
  | CanonicalNodeProvenance.realAtom => node.depth

/-- Compact compiled Rule-1b root distance. -/
def rule1bCode (node : CanonicalBranchNode) : ℕ :=
  node.rule1bRootDistance

end CanonicalBranchNode

/-- Unique graph neighbours in bond-list order. -/
def incidentAtoms (mol : RawMolecule) (atom : ℕ) : List ℕ :=
  (mol.bonds.filterMap fun bond =>
    if bond.source == atom then some bond.target
    else if bond.target == atom then some bond.source
    else none).eraseDups

/-- First zero-based occurrence of an atom in a path. -/
def firstNatIndex? (target : ℕ) : List ℕ → Option ℕ
  | [] => none
  | atom :: atoms =>
      if atom = target then some 0 else (firstNatIndex? target atoms).map Nat.succ

/-- Distance from the stereogenic-unit root to an atom already present in a node history. -/
def canonicalHistoryDistance (node : CanonicalBranchNode) (atom : ℕ) : ℕ :=
  (firstNatIndex? atom node.history.reverse).getD (node.depth + 1)

/-- Search one alternating single/double path while excluding the atom at which the candidate
mancude cycle is rooted. -/
def alternatingPathTo (mol : RawMolecule) (blocked target expectedOrder : ℕ) :
    ℕ → ℕ → List ℕ → Bool
  | 0, current, _ => current == target
  | fuel + 1, current, visited =>
      if current == target then true
      else
        (mol.incidentAtoms current).any fun next =>
          next != blocked && !(visited.contains next) &&
            mol.bondOrder current next == expectedOrder &&
            mol.alternatingPathTo blocked target (if expectedOrder == 1 then 2 else 1)
              fuel next (current :: visited)

/-- First successful result in list order. -/
def firstSome {α β : Type*} (f : α → Option β) : List α → Option β
  | [] => none
  | value :: values =>
      match f value with
      | some result => some result
      | none => firstSome f values

/-- Recover one alternating path, including both endpoints. -/
def alternatingPath? (mol : RawMolecule) (blocked target expectedOrder : ℕ) :
    ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, current, _ => if current == target then some [current] else none
  | fuel + 1, current, visited =>
      if current == target then some [current]
      else
        firstSome
          (fun next =>
            if next != blocked && !(visited.contains next) &&
                mol.bondOrder current next == expectedOrder then
              (mol.alternatingPath? blocked target (if expectedOrder == 1 then 2 else 1)
                fuel next (current :: visited)).map fun path => current :: path
            else
              none)
          (mol.incidentAtoms current)

/-- A simple localized mancude cycle through one written double bond, when the atom at the other end
has exactly one alternate single-bond partner and an alternating path closes the ring. -/
def cycleEdges (cycle : List ℕ) : List (ℕ × ℕ) :=
  match cycle with
  | [] => []
  | first :: _ => cycle.zip (cycle.drop 1 ++ [first])

/-- Whether a candidate cycle shares a second ring path with atoms outside that cycle. -/
def cycleHasExternalReentry (mol : RawMolecule) (cycle : List ℕ) : Bool :=
  cycle.any fun atom =>
    (mol.incidentAtoms atom).any fun neighbor =>
      !(cycle.contains neighbor) &&
        (mol.reachableAvoiding (mol.atomCount + 1) atom [neighbor] [neighbor]).any fun reached =>
          cycle.contains reached

/-- A candidate is maximally noncumulatively unsaturated in its written Kekulé form. -/
def cycleIsMancude (mol : RawMolecule) (cycle : List ℕ) : Bool :=
  let edges := cycleEdges cycle
  let doubleCount := (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
  doubleCount == cycle.length / 2 &&
    cycle.all (fun atom =>
      ((mol.incidentAtoms atom).filter fun neighbor =>
        cycle.contains neighbor && mol.bondOrder atom neighbor == 2).length ≤ 1)

/-- Atoms that may occupy the duplicate position under equivalent Kekulé placements of a fully
conjugated cycle.  For a localized double bond this always includes its written partner; alternate
single-bond neighbours are included exactly when an alternating path closes the cycle. -/
def mancudeDuplicatePartners (mol : RawMolecule) (attached duplicated : ℕ) : List ℕ :=
  if mol.bondOrder attached duplicated != 2 then [duplicated]
  else
    let alternates :=
      (mol.incidentAtoms attached).filter fun candidate =>
        candidate != duplicated && mol.bondOrder attached candidate == 1 &&
          mol.alternatingPathTo attached candidate 1 (mol.atomCount + 1) duplicated
            [attached, duplicated]
    (duplicated :: alternates).eraseDups

/-! #### General bounded mancude averaging

For localized fused systems, possible duplicate positions are the partners of an atom across every
maximum matching of the conjugated ring graph.  Computing that mean directly handles both fused
Kekulé systems and odd rings whose unmatched form contributes atomic number zero.
-/

/-- Number of written noncumulative double bonds incident to an atom. -/
def incidentDoubleBondCount (mol : RawMolecule) (atom : ℕ) : ℕ :=
  (mol.bonds.filter fun bond =>
    bond.kind.order == 2 && (bond.source == atom || bond.target == atom)).length

/-- Vertices admitted to the localized mancude graph.  Matched vertices have one incident written
double bond; a formally negative unmatched vertex supplies the odd-system electron-pair position. -/
def localizedMancudeVertex (mol : RawMolecule) (atom : ℕ) : Bool :=
  mol.incidentDoubleBondCount atom == 1 ||
    (mol.incidentDoubleBondCount atom == 0 &&
      match mol.atomAt? atom with
      | some spec => spec.charge < 0
      | none => false)

/-- Reachability in an undirected edge list while omitting one distinguished edge. -/
def reachableWithoutEdge (blocked : ℕ × ℕ) :
    ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → List ℕ
  | 0, _, _, seen => seen
  | _ + 1, _, [], seen => seen
  | fuel + 1, edges, frontier, seen =>
      let next :=
        (frontier.flatMap fun atom =>
          edges.filterMap fun edge =>
            let isBlocked :=
              (edge.1 == blocked.1 && edge.2 == blocked.2) ||
                (edge.1 == blocked.2 && edge.2 == blocked.1)
            if isBlocked then none
            else if edge.1 == atom then some edge.2
            else if edge.2 == atom then some edge.1
            else none).filter fun atom => !(seen.contains atom)
      let fresh := next.eraseDups
      reachableWithoutEdge blocked fuel edges fresh (seen ++ fresh)

/-- Candidate conjugated edges before bridges are removed. -/
def localizedMancudeCandidateEdges (mol : RawMolecule) : List (ℕ × ℕ) :=
  mol.bonds.filterMap fun bond =>
    if (bond.kind.order == 1 || bond.kind.order == 2) &&
        mol.localizedMancudeVertex bond.source && mol.localizedMancudeVertex bond.target then
      some (bond.source, bond.target)
    else
      none

/-- Ring edges of the localized conjugated graph.  A bridge to a different unsaturated group is not
a resonance edge and is removed because its endpoints cannot reconnect when that edge is omitted. -/
def localizedMancudeEdges (mol : RawMolecule) : List (ℕ × ℕ) :=
  let candidates := mol.localizedMancudeCandidateEdges
  candidates.filter fun edge =>
    (reachableWithoutEdge edge (candidates.length + 1) candidates [edge.1] [edge.1]).contains edge.2

/-- Membership in an undirected edge list. -/
def containsUndirectedEdge (edges : List (ℕ × ℕ)) (left right : ℕ) : Bool :=
  edges.any fun edge =>
    (edge.1 == left && edge.2 == right) || (edge.1 == right && edge.2 == left)

/-- Connected component of one atom in an undirected edge list. -/
def edgeComponent (edges : List (ℕ × ℕ)) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, frontier, seen =>
      let next :=
        (frontier.flatMap fun atom =>
          edges.filterMap fun edge =>
            if edge.1 == atom then some edge.2
            else if edge.2 == atom then some edge.1
            else none).filter fun atom => !(seen.contains atom)
      let fresh := next.eraseDups
      edgeComponent edges fuel fresh (seen ++ fresh)

/-- A simple localized mancude cycle through one written double bond.

The final guard is deliberately stated against the exact localized graph used by the general
matching search: the reported cycle and the attached localized component must have the same vertex
set and the same undirected edge set.  This rejects chords, fused systems, and cycles sharing only
an articulation atom without relying on heuristic raw-graph reentry tests. -/
def simpleMancudeCycle? (mol : RawMolecule) (attached duplicated : ℕ) :
    Option (List ℕ × ℕ) :=
  if mol.bondOrder attached duplicated != 2 then none
  else
    let alternatives :=
      (mol.incidentAtoms attached).filterMap fun candidate =>
        if candidate != duplicated && mol.bondOrder attached candidate == 1 then
          (mol.alternatingPath? attached candidate 1 (mol.atomCount + 1) duplicated
            [attached, duplicated]).map fun path => (path, candidate)
        else
          none
    match alternatives with
    | [(path, candidate)] =>
        let cycle := attached :: path
        let reportedEdges := cycleEdges cycle
        let localizedVertices := edgeComponent mol.localizedMancudeEdges
          (mol.localizedMancudeEdges.length + 1) [attached] [attached]
        let localizedEdges := mol.localizedMancudeEdges.filter fun edge =>
          localizedVertices.contains edge.1 && localizedVertices.contains edge.2
        let exactComponent :=
          cycle.all localizedVertices.contains && localizedVertices.all cycle.contains &&
            reportedEdges.all (fun edge =>
              containsUndirectedEdge localizedEdges edge.1 edge.2) &&
            localizedEdges.all (fun edge =>
              containsUndirectedEdge reportedEdges edge.1 edge.2)
        if 3 ≤ cycle.length && cycle.eraseDups.length == cycle.length &&
            mol.cycleIsMancude cycle && exactComponent then
          some (cycle, candidate)
        else
          none
    | _ => none

/-- Summary of all maximum-cardinality matchings in a finite edge list. -/
structure MancudeMatchingStats where
  size : ℕ
  count : ℕ
  partnerZSum : ℕ
  deriving DecidableEq, Repr

/-- Keep the larger matching family, or combine equally large disjoint families. -/
def combineMancudeStats (left right : MancudeMatchingStats) : MancudeMatchingStats :=
  if left.size < right.size then right
  else if right.size < left.size then left
  else
    { size := left.size
      count := left.count + right.count
      partnerZSum := left.partnerZSum + right.partnerZSum }

/-- Enumerate maximum matchings by excluding or including the first remaining edge. -/
def mancudeMatchingStats (mol : RawMolecule) (attached : ℕ) :
    ℕ → List (ℕ × ℕ) → Option MancudeMatchingStats
  | 0, _ => none
  | _ + 1, [] => some { size := 0, count := 1, partnerZSum := 0 }
  | fuel + 1, edge :: edges => do
      let excluded ← mol.mancudeMatchingStats attached fuel edges
      let remaining := edges.filter fun candidate =>
        candidate.1 != edge.1 && candidate.2 != edge.1 &&
          candidate.1 != edge.2 && candidate.2 != edge.2
      let includedTail ← mol.mancudeMatchingStats attached fuel remaining
      let partnerZ :=
        if edge.1 == attached then mol.atomZAt edge.2
        else if edge.2 == attached then mol.atomZAt edge.1
        else 0
      let included : MancudeMatchingStats :=
        { size := includedTail.size + 1
          count := includedTail.count
          partnerZSum := includedTail.partnerZSum + includedTail.count * partnerZ }
      some (combineMancudeStats excluded included)

/-- Exact maximum-matching average for the finite localized mancude component containing one
written double bond.  Termination is bounded by the component's decreasing edge list. -/
def generalMancudeRule1aLabel? (mol : RawMolecule) (attached duplicated : ℕ) :
    Option CIPAtomicLabel :=
  let allEdges := mol.localizedMancudeEdges
  let vertices := edgeComponent allEdges (allEdges.length + 1) [attached] [attached]
  let edges := allEdges.filter fun edge => vertices.contains edge.1 && vertices.contains edge.2
  if !(vertices.contains duplicated) || edges.isEmpty then none
  else do
    let stats ← mol.mancudeMatchingStats attached (edges.length + 1) edges
    let writtenDoubleCount :=
      (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
    if stats.size != writtenDoubleCount || stats.count == 0 then none
    else some { numerator := stats.partnerZSum, denominator := stats.count }

/-- Exact uniform perfect-matching label for a localized mancude component of any bounded size.

The written noncumulative double bonds are pairwise vertex-disjoint by construction of the
localized mancude graph.  If they cover every component vertex, they exhibit a perfect matching;
therefore every maximum matching is perfect and covers `attached`.  When every possible partner has
the same atomic number, the Kekule-ensemble average is exactly that number without enumerating the
maximum matchings. -/
def uniformPerfectMancudeRule1aLabel? (mol : RawMolecule) (attached duplicated : ℕ) :
    Option CIPAtomicLabel :=
  let allEdges := mol.localizedMancudeEdges
  let vertices := edgeComponent allEdges (allEdges.length + 1) [attached] [attached]
  let edges := allEdges.filter fun edge => vertices.contains edge.1 && vertices.contains edge.2
  let writtenDoubleCount :=
    (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
  let uniformAtomicNumber := vertices.all fun atom =>
    mol.atomZAt atom == mol.atomZAt attached
  if !(vertices.contains duplicated) || edges.isEmpty ||
      vertices.length != 2 * writtenDoubleCount || !uniformAtomicNumber then none
  else some { numerator := mol.atomZAt attached, denominator := 1 }

/-- Closed exact label of one structurally certified simple mancude cycle. -/
def simpleMancudeCycleLabel (mol : RawMolecule)
    (duplicated alternate : ℕ) (cycle : List ℕ) : CIPAtomicLabel :=
  if cycle.length % 2 == 0 then
    { numerator := mol.atomZAt duplicated + mol.atomZAt alternate, denominator := 2 }
  else
    let multiplicity := cycle.length / 2
    { numerator := multiplicity * (mol.atomZAt duplicated + mol.atomZAt alternate)
      denominator := cycle.length }

/-- Exact duplicate label for a localized double bond or a simple mancude cycle.

For an even ring, the atom is matched to either adjacent atom in the two Kekulé forms.  For an odd
ring of length `2k+1`, there are `2k+1` maximum-match Kekulé forms: the atom is unmatched once and
is matched to each adjacent atom `k` times.  The unmatched electron-pair position contributes atomic
number zero.  Non-simple components delegate to the exact finite maximum-matching search. -/
def mancudeRule1aLabel? (mol : RawMolecule) (attached duplicated : ℕ) :
    Option CIPAtomicLabel :=
  if !containsUndirectedEdge mol.localizedMancudeEdges attached duplicated then
    some { numerator := mol.atomZAt duplicated, denominator := 1 }
  else
    match mol.simpleMancudeCycle? attached duplicated with
    | some (cycle, alternate) => some (mol.simpleMancudeCycleLabel duplicated alternate cycle)
    | none => mol.generalMancudeRule1aLabel? attached duplicated

/-- Rule-1a label when all required mancude/Kekulé averaging is supported exactly. -/
def canonicalRule1aLabel? (mol : RawMolecule) (node : CanonicalBranchNode) : Option CIPAtomicLabel :=
  match node.provenance with
  | CanonicalNodeProvenance.phantom _ => some { numerator := 0, denominator := 1 }
  | CanonicalNodeProvenance.multipleBondDuplicate _ =>
      mol.mancudeRule1aLabel? node.parent node.atom
  | _ => some { numerator := mol.atomZAt node.atom, denominator := 1 }

/-- Exact Rule-1a label available to a strict first-sphere comparison.

The first-sphere path tries the certified uniform-perfect shortcut before invoking the exhaustive
general matcher.  The localized-edge guard preserves the ordinary node label for non-mancude
duplicates. -/
def canonicalFirstSphereRule1aLabel? (mol : RawMolecule) (node : CanonicalBranchNode) :
    Option CIPAtomicLabel :=
  match node.provenance with
  | CanonicalNodeProvenance.multipleBondDuplicate _ =>
      if containsUndirectedEdge mol.localizedMancudeEdges node.parent node.atom then
        match mol.uniformPerfectMancudeRule1aLabel? node.parent node.atom with
        | some label => some label
        | none => mol.canonicalRule1aLabel? node
      else mol.canonicalRule1aLabel? node
  | _ => mol.canonicalRule1aLabel? node

/-- Total projection used by checked examples after support has been established. -/
def canonicalRule1aLabel (mol : RawMolecule) (node : CanonicalBranchNode) : CIPAtomicLabel :=
  (mol.canonicalRule1aLabel? node).getD { numerator := 0, denominator := 1 }

/-- P/S oxido cores use the coordination-sphere convention in which a conventionally written
`P=O` or `S=O` bond directly attached to the stereocenter is treated as a single root edge.

This applies to both three-coordinate lone-pair centers and four-coordinate hypervalent centers.
It is deliberately limited to the first edge; ordinary carbonyl and deeper multiple bonds retain
their normal duplicate nodes. -/
def isTrigonalPyramidalOxidoRootEdge (mol : RawMolecule) (center oxygen : ℕ) : Bool :=
  match mol.atomAt? center, mol.atomAt? oxygen with
  | some centerSpec, some oxygenSpec =>
      (centerSpec.element == Element.P || centerSpec.element == Element.S) &&
        oxygenSpec.element == Element.O && mol.bondOrder center oxygen == 2
  | _, _ => false

/-- Bond order used while expanding one canonical node. -/
def canonicalBondOrder (mol : RawMolecule) (node : CanonicalBranchNode) (next : ℕ) : ℕ :=
  match node.history with
  | [current, center] =>
      if next == center && mol.isTrigonalPyramidalOxidoRootEdge center current then 1
      else mol.bondOrder node.atom next
  | _ => mol.bondOrder node.atom next

/-- Remove the real copy of the edge back to the parent, retaining any multiple-bond duplicates. -/
def eraseCanonicalParentCopy (parent : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | copy :: copies =>
      if copy.1 == parent && copy.2 == 0 then copies
      else copy :: eraseCanonicalParentCopy parent copies

/-- Child-copy seeds, with copy index zero denoting the real graph edge. -/
def canonicalChildCopies (mol : RawMolecule) (node : CanonicalBranchNode) : List (ℕ × ℕ) :=
  let copies :=
    mol.bonds.flatMap fun bond =>
      let next? :=
        if bond.source == node.atom then some bond.target
        else if bond.target == node.atom then some bond.source
        else none
      match next? with
      | none => []
      | some next =>
          (List.range (mol.canonicalBondOrder node next)).map fun copyIndex => (next, copyIndex)
  eraseCanonicalParentCopy node.parent copies

/-- Canonical children with ring and multiple-bond duplicate provenance assigned at creation. -/
def canonicalChildren (mol : RawMolecule) (node : CanonicalBranchNode) : List CanonicalBranchNode :=
  if node.forcedLeaf then []
  else
    (mol.canonicalChildCopies node).map fun copy =>
      let next := copy.1
      let provenance :=
        if copy.2 != 0 then
          CanonicalNodeProvenance.multipleBondDuplicate node.depth
        else if node.history.contains next then
          CanonicalNodeProvenance.ringDuplicate (canonicalHistoryDistance node next)
        else
          CanonicalNodeProvenance.realAtom
      { atom := next, parent := node.atom, history := next :: node.history,
        provenance := provenance }

/-- Whether a canonical node has no descendants. -/
def canonicalTerminal (mol : RawMolecule) (node : CanonicalBranchNode) : Bool :=
  node.forcedLeaf || (mol.canonicalChildren node).isEmpty

/-- Explicit lowest-priority padding node. -/
def canonicalPhantom (mol : RawMolecule) (parent distance : ℕ) : CanonicalBranchNode :=
  { atom := mol.atomCount, parent := parent, history := [],
    provenance := CanonicalNodeProvenance.phantom distance }

/-- Rules currently perceived directly from molecular constitution by this assigner. -/
inductive CanonicalRuleStage where
  | rule1a
  | rule1b
  | rule2
  deriving DecidableEq, Repr

/-- Compare two node labels under one rule only. -/
def compareCanonicalNodeRule (mol : RawMolecule) (rule : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Ordering :=
  match rule with
  | CanonicalRuleStage.rule1a =>
      compareCIPAtomicLabel (mol.canonicalRule1aLabel left) (mol.canonicalRule1aLabel right)
  | CanonicalRuleStage.rule1b =>
      if left.rule1bRootDistance < right.rule1bRootDistance then Ordering.gt
      else if right.rule1bRootDistance < left.rule1bRootDistance then Ordering.lt
      else Ordering.eq
  | CanonicalRuleStage.rule2 =>
      let mass : CanonicalBranchNode → ℕ := fun node =>
        match node.provenance with
        | CanonicalNodeProvenance.realAtom => mol.atomMassAt node.atom
        | _ => 0
      compare (mass left) (mass right)

/-- Option-valued node comparison for paths that have not precompiled label support.

The total comparator above is used only after canonical-key construction has established every
Rule-1a label.  Cursor and re-rooted occurrence comparisons do not have that preflight, so an
unsupported mancude average must remain `none` rather than inherit the total projection's phantom
zero label. -/
def compareCanonicalNodeRule? (mol : RawMolecule) (rule : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Option Ordering :=
  match rule with
  | CanonicalRuleStage.rule1a => do
      let leftLabel ← mol.canonicalRule1aLabel? left
      let rightLabel ← mol.canonicalRule1aLabel? right
      some (compareCIPAtomicLabel leftLabel rightLabel)
  | CanonicalRuleStage.rule1b
  | CanonicalRuleStage.rule2 => some (mol.compareCanonicalNodeRule rule left right)

/-- Immediate rule-major comparison used as the base of recursive sibling refinement. -/
def compareCanonicalNodeThrough (mol : RawMolecule) (stage : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Ordering :=
  match mol.compareCanonicalNodeRule CanonicalRuleStage.rule1a left right with
  | Ordering.eq =>
      match stage with
      | CanonicalRuleStage.rule1a => Ordering.eq
      | CanonicalRuleStage.rule1b =>
          mol.compareCanonicalNodeRule CanonicalRuleStage.rule1b left right
      | CanonicalRuleStage.rule2 =>
          match mol.compareCanonicalNodeRule CanonicalRuleStage.rule1b left right with
          | Ordering.eq => mol.compareCanonicalNodeRule CanonicalRuleStage.rule2 left right
          | other => other
  | other => other

/-- Option-valued rule-major node comparison, refusing unsupported Rule-1a labels. -/
def compareCanonicalNodeThrough? (mol : RawMolecule) (stage : CanonicalRuleStage)
    (left right : CanonicalBranchNode) : Option Ordering := do
  let rule1a ← mol.compareCanonicalNodeRule? CanonicalRuleStage.rule1a left right
  match rule1a with
  | Ordering.lt => some Ordering.lt
  | Ordering.gt => some Ordering.gt
  | Ordering.eq =>
      match stage with
      | CanonicalRuleStage.rule1a => some Ordering.eq
      | CanonicalRuleStage.rule1b =>
          mol.compareCanonicalNodeRule? CanonicalRuleStage.rule1b left right
      | CanonicalRuleStage.rule2 => do
          let rule1b ← mol.compareCanonicalNodeRule? CanonicalRuleStage.rule1b left right
          match rule1b with
          | Ordering.eq => mol.compareCanonicalNodeRule? CanonicalRuleStage.rule2 left right
          | decision => some decision

/-- Structural option-valued insertion sort.  Failure to rank siblings propagates as refusal rather
than becoming an enumeration-order tie-break. -/
def insertCanonicalBy? (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (node : CanonicalBranchNode) :
    List CanonicalBranchNode → Option (List CanonicalBranchNode)
  | [] => some [node]
  | head :: tail =>
      match before node head with
      | none => none
      | some Ordering.gt | some Ordering.eq => some (node :: head :: tail)
      | some Ordering.lt =>
          (insertCanonicalBy? before node tail).map fun sorted => head :: sorted

/-- Structural option-valued descending sort. -/
def sortCanonicalBy? (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering) :
    List CanonicalBranchNode → Option (List CanonicalBranchNode)
  | [] => some []
  | node :: nodes => do
      let sorted ← sortCanonicalBy? before nodes
      insertCanonicalBy? before node sorted

/-- Children in recursively refined priority order, padded to three positional slots. -/
def rankedCanonicalChildren? (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (node : CanonicalBranchNode) : Option (List CanonicalBranchNode) := do
  let children := mol.canonicalChildren node
  if 3 < children.length then none
  else
    let sorted ← sortCanonicalBy? before children
    let phantom := mol.canonicalPhantom node.atom (node.rule1bRootDistance + 1)
    some (sorted ++ List.replicate (3 - sorted.length) phantom)

/-- Compare all already parent-ranked nodes in one complete sphere. -/
def compareCanonicalPairLabels (mol : RawMolecule) (rule : CanonicalRuleStage) :
    List (CanonicalBranchNode × CanonicalBranchNode) → Ordering
  | [] => Ordering.eq
  | pair :: pairs =>
      match mol.compareCanonicalNodeRule rule pair.1 pair.2 with
      | Ordering.eq => mol.compareCanonicalPairLabels rule pairs
      | other => other

/-- Expand paired nodes without losing their parent slots. -/
def nextCanonicalPairs? (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering) :
    List (CanonicalBranchNode × CanonicalBranchNode) →
      Option (List (CanonicalBranchNode × CanonicalBranchNode))
  | [] => some []
  | pair :: pairs => do
      let rest ← mol.nextCanonicalPairs? before pairs
      if mol.canonicalTerminal pair.1 && mol.canonicalTerminal pair.2 then
        some rest
      else
        let left ← mol.rankedCanonicalChildren? before pair.1
        let right ← mol.rankedCanonicalChildren? before pair.2
        some (left.zip right ++ rest)

/-- Compare one sequence rule exhaustively, sphere by sphere. -/
def compareCanonicalRule (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (rule : CanonicalRuleStage) (cap : ℕ) :
    ℕ → List (CanonicalBranchNode × CanonicalBranchNode) → Option Ordering
  | 0, pairs =>
      if cap < pairs.length then none
      else
        match mol.compareCanonicalPairLabels rule pairs with
        | Ordering.eq =>
            match mol.nextCanonicalPairs? before pairs with
            | some [] => some Ordering.eq
            | _ => none
        | other => some other
  | fuel + 1, pairs =>
      if cap < pairs.length then none
      else
        match mol.compareCanonicalPairLabels rule pairs with
        | Ordering.eq =>
            match mol.nextCanonicalPairs? before pairs with
            | none => none
            | some [] => some Ordering.eq
            | some next => mol.compareCanonicalRule before rule cap fuel next
        | other => some other

/-- Recursively refined comparison through the requested rule.  Refinement at depth `n+1` ranks
siblings by their complete depth-`n` branch comparison, eliminating raw enumeration tie-breaks. -/
def compareCanonicalBranchAt (mol : RawMolecule) :
    ℕ → CanonicalRuleStage → CanonicalBranchNode → CanonicalBranchNode → Option Ordering
  | 0, stage, left, right => some (mol.compareCanonicalNodeThrough stage left right)
  | fuel + 1, stage, left, right =>
      let before := mol.compareCanonicalBranchAt fuel stage
      let compareRule := fun rule =>
        mol.compareCanonicalRule before rule defaultBranchWidthCap (fuel + 1) [(left, right)]
      match compareRule CanonicalRuleStage.rule1a with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          match stage with
          | CanonicalRuleStage.rule1a => some Ordering.eq
          | CanonicalRuleStage.rule1b =>
              compareRule CanonicalRuleStage.rule1b
          | CanonicalRuleStage.rule2 =>
              match compareRule CanonicalRuleStage.rule1b with
              | some Ordering.eq => compareRule CanonicalRuleStage.rule2
              | other => other

/-- Option-valued sphere labels for descriptor and occurrence paths without compiled-key preflight. -/
def compareCanonicalPairLabels? (mol : RawMolecule) (rule : CanonicalRuleStage) :
    List (CanonicalBranchNode × CanonicalBranchNode) → Option Ordering
  | [] => some Ordering.eq
  | pair :: pairs =>
      match mol.compareCanonicalNodeRule? rule pair.1 pair.2 with
      | none => none
      | some Ordering.eq => mol.compareCanonicalPairLabels? rule pairs
      | some decision => some decision

/-- Option-valued exhaustive rule comparison that preserves unsupported Rule-1a labels as `none`. -/
def compareCanonicalRuleSupported? (mol : RawMolecule)
    (before : CanonicalBranchNode → CanonicalBranchNode → Option Ordering)
    (rule : CanonicalRuleStage) (cap : ℕ) :
    ℕ → List (CanonicalBranchNode × CanonicalBranchNode) → Option Ordering
  | 0, pairs =>
      if cap < pairs.length then none else
        match mol.compareCanonicalPairLabels? rule pairs with
        | none => none
        | some Ordering.eq =>
            match mol.nextCanonicalPairs? before pairs with
            | some [] => some Ordering.eq
            | _ => none
        | some decision => some decision
  | fuel + 1, pairs =>
      if cap < pairs.length then none else
        match mol.compareCanonicalPairLabels? rule pairs with
        | none => none
        | some Ordering.eq =>
            match mol.nextCanonicalPairs? before pairs with
            | none => none
            | some [] => some Ordering.eq
            | some next => mol.compareCanonicalRuleSupported? before rule cap fuel next
        | some decision => some decision

/-- Recursively refined constitutional comparison with explicit Rule-1a support propagation.

This is the entry point for descriptor-rich paths that do not first build a checked canonical key.
The historical total variant remains available to already-preflighted diagnostics. -/
def compareCanonicalBranchAtSupported? (mol : RawMolecule) :
    ℕ → CanonicalRuleStage → CanonicalBranchNode → CanonicalBranchNode → Option Ordering
  | 0, stage, left, right => mol.compareCanonicalNodeThrough? stage left right
  | fuel + 1, stage, left, right =>
      let before := mol.compareCanonicalBranchAtSupported? fuel stage
      let compareRule := fun rule =>
        mol.compareCanonicalRuleSupported? before rule defaultBranchWidthCap (fuel + 1)
          [(left, right)]
      match compareRule CanonicalRuleStage.rule1a with
      | none => none
      | some Ordering.lt => some Ordering.lt
      | some Ordering.gt => some Ordering.gt
      | some Ordering.eq =>
          match stage with
          | CanonicalRuleStage.rule1a => some Ordering.eq
          | CanonicalRuleStage.rule1b => compareRule CanonicalRuleStage.rule1b
          | CanonicalRuleStage.rule2 =>
              match compareRule CanonicalRuleStage.rule1b with
              | some Ordering.eq => compareRule CanonicalRuleStage.rule2
              | decision => decision

/-- Root node for one ligand edge. -/
def canonicalRoot (center atom : ℕ) : CanonicalBranchNode :=
  { atom := atom, parent := center, history := [atom, center],
    provenance := CanonicalNodeProvenance.realAtom }

/-- Historical sphere-multiset comparison retained only for differential validation. -/
def compareBranchesSphere? (mol : RawMolecule) (fuel center left right : ℕ) : Option Ordering :=
  let roots : ℕ → List BranchNode := fun atom =>
    [{ atom := atom, parent := center, visited := [center], duplicate := false, rootDistance := 0 }]
  match mol.compareFrontiersBy rule1aKey defaultBranchWidthCap fuel (roots left) (roots right) with
  | some Ordering.eq =>
      match mol.compareFrontiersBy rule1bKey defaultBranchWidthCap fuel (roots left) (roots right) with
      | some Ordering.eq =>
          mol.compareFrontiersBy rule2Key defaultBranchWidthCap fuel (roots left) (roots right)
      | other => other
  | other => other

/-! ### Compiled canonical keys

The recursive refinement above is a direct executable specification.  For production throughput we
compile each finite branch tree once into sparse, position-tagged sphere layers.  Position paths keep
phantom slots implicit without allowing a later sibling to shift into a missing earlier slot.  Child
keys are sorted by their complete rule-major key before their layers are merged, so the result is the
same sphere-major, parent-ranked hierarchy without repeated subtree comparison.
-/

abbrev CanonicalAtomicEntry := List ℕ × CIPAtomicLabel
abbrev CanonicalNatEntry := List ℕ × ℕ
abbrev CanonicalProvenanceEntry := List ℕ × CanonicalNodeProvenance
abbrev CanonicalNodeEntry := List ℕ × (ℕ × CanonicalNodeProvenance)
abbrev CanonicalSourceEntry := List ℕ × CanonicalBranchNode

/- Recursive proof provenance for one compiled branch.  The mutually inductive forest preserves
child occurrences positionally, including indistinguishable multiple-bond duplicates. -/
mutual
  inductive CanonicalSourceTree where
    | node (source : CanonicalBranchNode) (children : CanonicalSourceForest)
  inductive CanonicalSourceForest where
    | nil
    | cons (head : CanonicalSourceTree) (tail : CanonicalSourceForest)
end

deriving instance DecidableEq for CanonicalSourceTree, CanonicalSourceForest
deriving instance Repr for CanonicalSourceTree, CanonicalSourceForest

namespace CanonicalSourceForest

def ofList : List CanonicalSourceTree → CanonicalSourceForest
  | [] => .nil
  | tree :: trees => .cons tree (ofList trees)

def toList : CanonicalSourceForest → List CanonicalSourceTree
  | .nil => []
  | .cons tree trees => tree :: toList trees

@[simp] theorem toList_ofList (trees : List CanonicalSourceTree) :
    (ofList trees).toList = trees := by
  induction trees <;> simp [ofList, toList, *]

end CanonicalSourceForest

mutual
  /-- Preorder path/source entries of a recursive production source tree. -/
  def CanonicalSourceTree.occurrences : CanonicalSourceTree → List CanonicalSourceEntry
    | .node source children => ([], source) :: children.occurrences 0

  /-- Preorder entries of sibling trees, numbered from the supplied positional slot. -/
  def CanonicalSourceForest.occurrences : CanonicalSourceForest → ℕ → List CanonicalSourceEntry
    | .nil, _ => []
    | .cons tree trees, slot =>
        (tree.occurrences.map fun entry => (slot :: entry.1, entry.2)) ++
          trees.occurrences (slot + 1)
end

mutual
  /-- Look up the recursive source subtree at one positional address. -/
  def CanonicalSourceTree.subtreeAt? :
      CanonicalSourceTree → List ℕ → Option CanonicalSourceTree
    | tree, [] => some tree
    | .node _ children, slot :: address => children.subtreeAt? slot address

  /-- Look up a sibling subtree by its zero-based slot and then descend through an address. -/
  def CanonicalSourceForest.subtreeAt? :
      CanonicalSourceForest → ℕ → List ℕ → Option CanonicalSourceTree
    | .nil, _, _ => none
    | .cons tree _, 0, address => tree.subtreeAt? address
    | .cons _ trees, slot + 1, address => trees.subtreeAt? slot address
end

/-- Source node at one recursive tree address. -/
def CanonicalSourceTree.sourceAt? (tree : CanonicalSourceTree) (address : List ℕ) :
    Option CanonicalBranchNode :=
  (tree.subtreeAt? address).map fun subtree =>
    match subtree with
    | .node source _ => source

@[simp] theorem CanonicalSourceTree.sourceAt?_nil
    (source : CanonicalBranchNode) (children : CanonicalSourceForest) :
    (CanonicalSourceTree.node source children).sourceAt? [] = some source :=
  rfl

/-- Rule-major sparse key for one finite canonical branch. -/
structure CanonicalBranchKey where
  rule1a : List (List CanonicalAtomicEntry)
  rule1b : List (List CanonicalNatEntry)
  rule2 : List (List CanonicalNatEntry)
  /-- Real atom identities in the same sphere and positional-path hierarchy as the rule keys.
  These do not participate in constitutional comparison; descriptor perception uses them to attach
  Rules 3–5 evidence without flattening the digraph. -/
  realAtoms : List (List CanonicalNatEntry)
  /-- Every node occurrence, carrying atom identity and provenance in one path-indexed table.

  Keeping these witnesses together makes their positional alignment true by construction.  Rule
  6 projects atom identities from this table; declarative hierarchy conversion projects both atom
  identity and provenance from the same entries. -/
  sourceNodes : List (List CanonicalSourceEntry) := []
  /-- The same source occurrences in recursive tree order rather than sphere order.

  This proof-facing projection makes parent/child realization independent of transposing the
  sphere-major layers.  It does not participate in comparison. -/
  sourceOccurrences : List CanonicalSourceEntry := []
  /-- Recursive occurrence witness.  This field is proof provenance only: constitutional
  comparison does not inspect it. -/
  sourceTree? : Option CanonicalSourceTree := none
  complete : Bool
  deriving DecidableEq, Repr

/-- Atom/provenance occurrences projected together from the full source-node table. -/
def CanonicalBranchKey.allNodes (key : CanonicalBranchKey) : List (List CanonicalNodeEntry) :=
  key.sourceNodes.map fun layer => layer.map fun entry =>
    (entry.1, (entry.2.atom, entry.2.provenance))

/-- Atom occurrences projected from the unified proof-facing node table. -/
def CanonicalBranchKey.allAtoms (key : CanonicalBranchKey) : List (List CanonicalNatEntry) :=
  key.allNodes.map fun layer => layer.map fun entry => (entry.1, entry.2.1)

/-- Provenance occurrences projected from the unified proof-facing node table. -/
def CanonicalBranchKey.allProvenance (key : CanonicalBranchKey) :
    List (List CanonicalProvenanceEntry) :=
  key.allNodes.map fun layer => layer.map fun entry => (entry.1, entry.2.2)

/-- Lexicographic positional-path comparison. -/
def compareCanonicalPath : List ℕ → List ℕ → Ordering :=
  List.compareLex compare

/-- Compare one sparse positional entry.  Smaller position paths denote earlier sibling slots and
therefore have higher priority; labels break equal-path ties. -/
def compareSparseCanonicalEntry {alpha : Type*} (compareLabel : alpha → alpha → Ordering) :
    (List ℕ × alpha) → (List ℕ × alpha) → Ordering :=
  compareLex
    (Ordering.byKey Prod.fst (flip compareCanonicalPath))
    (Ordering.byKey Prod.snd compareLabel)

/-- Compare one sparse positional layer.  A present slot precedes an absent phantom slot. -/
def compareSparseCanonicalLayer {α : Type*} (compareLabel : α → α → Ordering) :
    List (List ℕ × α) → List (List ℕ × α) → Ordering :=
  List.compareLex (compareSparseCanonicalEntry compareLabel)

/-- Compare sparse layers sphere by sphere, nearer spheres first. -/
def compareSparseCanonicalLayers {α : Type*} (compareLabel : α → α → Ordering) :
    List (List (List ℕ × α)) → List (List (List ℕ × α)) → Ordering :=
  List.compareLex (compareSparseCanonicalLayer compareLabel)

/-- Revised Rule-1b comparison: a smaller root distance has higher priority. -/
def compareRule1bRootDistance : ℕ → ℕ → Ordering :=
  flip compare

/-- Complete rule-major comparison of compiled canonical keys. -/
def compareCanonicalBranchKeys (left right : CanonicalBranchKey) : Ordering :=
  compareLex
    (Ordering.byKey CanonicalBranchKey.rule1a
      (compareSparseCanonicalLayers compareCIPAtomicLabel))
    (compareLex
      (Ordering.byKey CanonicalBranchKey.rule1b
        (compareSparseCanonicalLayers compareRule1bRootDistance))
      (Ordering.byKey CanonicalBranchKey.rule2
        (compareSparseCanonicalLayers compare))) left right

/-- A truncated Rule-1a tie cannot safely fall through to Rule 1b or Rule 2.

A visible Rule-1a difference is final at its first differing sphere.  If Rule 1a ties over a
truncated prefix, however, an unseen later Rule-1a difference must outrank every currently visible
Rule-1b or Rule-2 difference, so the comparison refuses until both keys are complete. -/
def compareCanonicalBranchKeys? (left right : CanonicalBranchKey) : Option Ordering :=
  match compareSparseCanonicalLayers compareCIPAtomicLabel left.rule1a right.rule1a with
  | Ordering.lt => some Ordering.lt
  | Ordering.gt => some Ordering.gt
  | Ordering.eq =>
      if left.complete && right.complete then some (compareCanonicalBranchKeys left right) else none

/-- Every successful safe-key comparison is exactly the underlying rule-major key result. -/
theorem compareCanonicalBranchKeys_eq_of_eq_some (left right : CanonicalBranchKey)
    (outcome : Ordering) (h : compareCanonicalBranchKeys? left right = some outcome) :
    compareCanonicalBranchKeys left right = outcome := by
  unfold compareCanonicalBranchKeys? at h
  split at h <;> cases outcome <;>
    simp_all [compareCanonicalBranchKeys, compareLex, Ordering.byKey]

/-- Structural insertion of a compiled child key. -/
def insertCanonicalKey? (key : CanonicalBranchKey) :
    List CanonicalBranchKey → Option (List CanonicalBranchKey)
  | [] => some [key]
  | head :: tail =>
      match compareCanonicalBranchKeys? key head with
      | none => none
      | some Ordering.gt | some Ordering.eq => some (key :: head :: tail)
      | some Ordering.lt =>
          (insertCanonicalKey? key tail).map fun sorted => head :: sorted

/-- Structural descending sort of compiled child keys. -/
def sortCanonicalKeys? : List CanonicalBranchKey → Option (List CanonicalBranchKey)
  | [] => some []
  | key :: keys => do
      let sorted ← sortCanonicalKeys? keys
      insertCanonicalKey? key sorted

theorem insertCanonicalKey?_perm (key : CanonicalBranchKey) :
    ∀ keys result, insertCanonicalKey? key keys = some result →
      result.Perm (key :: keys)
  | [], result, hresult => by
      simp [insertCanonicalKey?] at hresult
      subst result
      exact List.Perm.refl _
  | head :: tail, result, hresult => by
      unfold insertCanonicalKey? at hresult
      cases hcompare : compareCanonicalBranchKeys? key head with
      | none => simp [hcompare] at hresult
      | some decision =>
          cases decision with
          | gt =>
              simp [hcompare] at hresult
              subst result
              exact List.Perm.refl _
          | eq =>
              simp [hcompare] at hresult
              subst result
              exact List.Perm.refl _
          | lt =>
              simp only [hcompare, Option.map_eq_some_iff] at hresult
              rcases hresult with ⟨inserted, hinserted, rfl⟩
              exact (List.Perm.cons head (insertCanonicalKey?_perm key tail inserted hinserted)).trans
                (List.Perm.swap key head tail)

theorem sortCanonicalKeys?_perm :
    ∀ keys result, sortCanonicalKeys? keys = some result → result.Perm keys
  | [], result, hresult => by
      simp [sortCanonicalKeys?] at hresult
      subst result
      exact List.Perm.refl _
  | key :: keys, result, hresult => by
      unfold sortCanonicalKeys? at hresult
      cases hsorted : sortCanonicalKeys? keys with
      | none => simp [hsorted] at hresult
      | some sorted =>
          have htail := sortCanonicalKeys?_perm keys sorted hsorted
          have hinsert := insertCanonicalKey?_perm key sorted result (by simpa [hsorted] using hresult)
          exact hinsert.trans (List.Perm.cons key htail)

/-- Prefix every sparse position in a layer with its sibling slot. -/
def prefixCanonicalAtomicLayer (slot : ℕ) (layer : List CanonicalAtomicEntry) :
    List CanonicalAtomicEntry :=
  layer.map fun entry => (slot :: entry.1, entry.2)

def prefixCanonicalNatLayer (slot : ℕ) (layer : List CanonicalNatEntry) :
    List CanonicalNatEntry :=
  layer.map fun entry => (slot :: entry.1, entry.2)

def prefixCanonicalSourceLayer (slot : ℕ) (layer : List CanonicalSourceEntry) :
    List CanonicalSourceEntry :=
  layer.map fun entry => (slot :: entry.1, entry.2)

def prefixCanonicalSourceOccurrences (slot : ℕ) (entries : List CanonicalSourceEntry) :
    List CanonicalSourceEntry :=
  entries.map fun entry => (slot :: entry.1, entry.2)

/-- Collect the recursive source trees retained by compiled child keys. -/
def canonicalSourceForest? : List CanonicalBranchKey → Option CanonicalSourceForest
  | [] => some .nil
  | key :: keys => do
      let tree ← key.sourceTree?
      let forest ← canonicalSourceForest? keys
      some (.cons tree forest)

/-- Maximum layer count among child keys. -/
def canonicalChildLayerCount {α : Type*} (children : List CanonicalBranchKey)
    (layers : CanonicalBranchKey → List (List α)) : ℕ :=
  children.foldl (fun longest child => max longest (layers child).length) 0

/-- Merge atomic-number layers in sorted sibling-slot order. -/
def mergeCanonicalAtomicChildren (children : List CanonicalBranchKey) :
    List (List CanonicalAtomicEntry) :=
  let count := canonicalChildLayerCount children (fun child => child.rule1a)
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixCanonicalAtomicLayer child.2 (child.1.rule1a.getD depth [])

/-- Merge natural-number layers in sorted sibling-slot order. -/
def mergeCanonicalNatChildren (layers : CanonicalBranchKey → List (List CanonicalNatEntry))
    (children : List CanonicalBranchKey) : List (List CanonicalNatEntry) :=
  let count := canonicalChildLayerCount children layers
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixCanonicalNatLayer child.2 ((layers child.1).getD depth [])

/-- Merge complete node-witness layers in ranked sibling-slot order. -/
def mergeCanonicalSourceChildren (children : List CanonicalBranchKey) :
    List (List CanonicalSourceEntry) :=
  let count := canonicalChildLayerCount children (fun child => child.sourceNodes)
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixCanonicalSourceLayer child.2 (child.1.sourceNodes.getD depth [])

/-- Number of represented nodes, counted once through Rule 1a. -/
def CanonicalBranchKey.nodeCount (key : CanonicalBranchKey) : ℕ :=
  key.rule1a.foldl (fun total layer => total + layer.length) 0

/-- Root-only key, complete exactly when the node is terminal. -/
def canonicalRootKey (mol : RawMolecule) (node : CanonicalBranchNode) (complete : Bool) :
    CanonicalBranchKey :=
  { rule1a := [[([], mol.canonicalRule1aLabel node)]]
    rule1b := [[([], node.rule1bCode)]]
    rule2 :=
      let mass :=
        match node.provenance with
        | CanonicalNodeProvenance.realAtom => mol.atomMassAt node.atom
        | _ => 0
      [[([], mass)]]
    realAtoms :=
      match node.provenance with
      | CanonicalNodeProvenance.realAtom => [[([], node.atom)]]
      | _ => [[]]
    sourceNodes := [[([], node)]]
    sourceOccurrences := [([], node)]
    sourceTree? := some (.node node .nil)
    complete := complete }

/-- Build a list of child keys while threading the exact remaining-node budget.  Naming this
structural helper exposes the budget discipline to kernel proofs; it is the former local recursion
of `buildCanonicalBranchKey` without any semantic or bound change. -/
def buildCanonicalChildKeys
    (buildChild : ℕ → CanonicalBranchNode → Option CanonicalBranchKey) :
    ℕ → List CanonicalBranchNode → Option (List CanonicalBranchKey)
  | _, [] => some []
  | remaining, child :: rest => do
      let key ← buildChild remaining child
      if remaining < key.nodeCount then none
      else
        let keys ← buildCanonicalChildKeys buildChild (remaining - key.nodeCount) rest
        some (key :: keys)

/-- Assemble a root and its priority-sorted child keys into sparse rule-major spheres. -/
def assembleCanonicalBranchKey (root : CanonicalBranchKey)
    (sorted : List CanonicalBranchKey) : CanonicalBranchKey :=
  { rule1a := root.rule1a ++ mergeCanonicalAtomicChildren sorted
    rule1b := root.rule1b ++ mergeCanonicalNatChildren (fun child => child.rule1b) sorted
    rule2 := root.rule2 ++ mergeCanonicalNatChildren (fun child => child.rule2) sorted
    realAtoms := root.realAtoms ++
      mergeCanonicalNatChildren (fun child => child.realAtoms) sorted
    sourceNodes := root.sourceNodes ++ mergeCanonicalSourceChildren sorted
    sourceOccurrences := root.sourceOccurrences ++
      sorted.zipIdx.flatMap fun child =>
        prefixCanonicalSourceOccurrences child.2 child.1.sourceOccurrences
    sourceTree? := do
      let rootTree ← root.sourceTree?
      let children ← canonicalSourceForest? sorted
      match rootTree with
      | .node source _ => some (.node source children)
    complete := root.complete }

/-- Compile one branch tree bottom-up.  Every child key is built once, sorted by its complete
rule-major priority, and merged into sparse positional spheres. -/
def buildCanonicalBranchKey (mol : RawMolecule) (cap : ℕ) :
    ℕ → CanonicalBranchNode → Option CanonicalBranchKey
  | 0, node => do
      let _ ← mol.canonicalRule1aLabel? node
      some (mol.canonicalRootKey node (mol.canonicalTerminal node))
  | fuel + 1, node =>
      match mol.canonicalRule1aLabel? node with
      | none => none
      | some _ => if mol.canonicalTerminal node then
          some (mol.canonicalRootKey node true)
        else do
          let children := mol.canonicalChildren node
          if 3 < children.length then none
          else
          let childKeys ← buildCanonicalChildKeys
            (fun remaining child => mol.buildCanonicalBranchKey remaining fuel child)
            (cap - 1) children
          let sorted ← sortCanonicalKeys? childKeys
          let root := mol.canonicalRootKey node (sorted.all fun child => child.complete)
          let key := assembleCanonicalBranchKey root sorted
          if cap < key.nodeCount then none else some key

/-- Lexicographic comparison of one priority-sorted Rule-1a sphere. -/
private def compareCanonicalRule1aSphere : List CIPAtomicLabel → List CIPAtomicLabel → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | left :: lefts, right :: rights =>
      match compareCIPAtomicLabel left right with
      | Ordering.eq => compareCanonicalRule1aSphere lefts rights
      | decision => decision

/-- Exact first child sphere, padded to the three substituent slots below a branch root. -/
private def canonicalFirstChildRule1aSphere? (mol : RawMolecule)
    (root : CanonicalBranchNode) : Option (List CIPAtomicLabel) := do
  let children := mol.canonicalChildren root
  if 3 < children.length then none else
  let labels ← children.mapM mol.canonicalFirstSphereRule1aLabel?
  let before := fun left right => compareCIPAtomicLabel left right != Ordering.lt
  let phantom : CIPAtomicLabel := { numerator := 0, denominator := 1 }
  some (sortDescBy before labels ++ List.replicate (3 - labels.length) phantom)

/-- A strict Rule-1a decision in the first child sphere, when every exact label is available.

This shortcut is extensionally a prefix of the compiled key comparison: deeper construction cannot
change a strict earlier-sphere decision.  Besides avoiding redundant compilation in ordinary cases,
it keeps very large uniform fused-mancude branches bounded once their exact averaged duplicate
label has been established without maximum-matching enumeration. -/
private def compareCanonicalFirstChildRule1aSphere? (mol : RawMolecule)
    (leftRoot rightRoot : CanonicalBranchNode) : Option Ordering := do
  let left ← mol.canonicalFirstChildRule1aSphere? leftRoot
  let right ← mol.canonicalFirstChildRule1aSphere? rightRoot
  match compareCanonicalRule1aSphere left right with
  | Ordering.eq => none
  | decision => some decision

/-- Production comparison using one compiled key per ligand. -/
def compareCanonicalBranchesCompiled? (mol : RawMolecule) (depth center left right : ℕ) :
    Option Ordering :=
  let leftRoot := canonicalRoot center left
  let rightRoot := canonicalRoot center right
  match mol.canonicalRule1aLabel? leftRoot, mol.canonicalRule1aLabel? rightRoot with
  | some leftLabel, some rightLabel =>
    match compareCIPAtomicLabel leftLabel rightLabel with
    | Ordering.lt => some Ordering.lt
    | Ordering.gt => some Ordering.gt
    | Ordering.eq =>
      match mol.compareCanonicalFirstChildRule1aSphere? leftRoot rightRoot with
      | some decision => some decision
      | none => do
        let leftKey ← mol.buildCanonicalBranchKey defaultBranchWidthCap depth leftRoot
        let rightKey ← mol.buildCanonicalBranchKey defaultBranchWidthCap depth rightRoot
        compareCanonicalBranchKeys? leftKey rightKey
  | _, _ => none

/-! ### Constitution-automorphism tie witnesses

An explicit rooted graph automorphism is a decisive tie under Rules 1a, 1b and 2, even when the two
ligands are mirror-related or a cyclic digraph admits several equivalent openings.  Checking this
before the operational comparator both enforces relabeling invariance on witnessed symmetries and
prevents constitutionally identical ligands from being assigned an uppercase descriptor merely
because their input atom enumeration differs.
-/

/-- Atom identity relevant to constitutional Rules 1a/2, deliberately excluding input `@`/`@@`
parity.  Remote parity is descriptor information for later sequence rules, not constitution. -/
def sameConstitutionAtom (mol : RawMolecule) (left right : ℕ) : Bool :=
  match mol.atomAt? left, mol.atomAt? right with
  | some leftSpec, some rightSpec =>
      leftSpec.element == rightSpec.element && leftSpec.isotope? == rightSpec.isotope? &&
        leftSpec.charge == rightSpec.charge && leftSpec.aromatic == rightSpec.aromatic &&
        leftSpec.explicitHydrogens? == rightSpec.explicitHydrogens?
  | none, none => true
  | _, _ => false

/-- Equality of immediate neighbour signatures, including the connecting bond order. -/
def cycleContainsEdge (cycle : List ℕ) (left right : ℕ) : Bool :=
  match cycle with
  | [] => false
  | first :: _ =>
      let successors := cycle.drop 1 ++ [first]
      (cycle.zip successors).any fun edge =>
        (edge.1 == left && edge.2 == right) || (edge.1 == right && edge.2 == left)

/-- Whether an edge belongs to a supported simple mancude cycle. -/
def inSimpleMancudeCycle (mol : RawMolecule) (left right : ℕ) : Bool :=
  mol.bonds.any fun bond =>
    if bond.kind.order != 2 then false
    else
      match mol.simpleMancudeCycle? bond.source bond.target with
      | some (cycle, _) => cycleContainsEdge cycle left right
      | none =>
          match mol.simpleMancudeCycle? bond.target bond.source with
          | some (cycle, _) => cycleContainsEdge cycle left right
          | none => false

/-- Undirected edges of every supported simple mancude cycle, computed once per symmetry search. -/
def simpleMancudeEdges (mol : RawMolecule) : List (ℕ × ℕ) :=
  (mol.bonds.flatMap fun bond =>
    if bond.kind.order != 2 then []
    else
      let cycle? :=
        match mol.simpleMancudeCycle? bond.source bond.target with
        | some result => some result
        | none => mol.simpleMancudeCycle? bond.target bond.source
      match cycle? with
      | none => []
      | some (cycle, _) => cycleEdges cycle).eraseDups

/-- Bond class for constitutional symmetry.  All localized single/double placements in one supported
mancude cycle share a resonance class; non-mancude bonds retain their exact order. -/
def constitutionBondClass (mol : RawMolecule) (mancudeEdges : List (ℕ × ℕ))
    (left right : ℕ) : ℕ :=
  let order := mol.bondOrder left right
  if order == 0 then 0 else if containsUndirectedEdge mancudeEdges left right then 4 else order

/-- Equality of immediate neighbour signatures, including the constitutional bond class. -/
def sameConstitutionNeighbor (mol : RawMolecule) (mancudeEdges : List (ℕ × ℕ))
    (leftOwner left rightOwner right : ℕ) : Bool :=
  mol.constitutionBondClass mancudeEdges leftOwner left ==
      mol.constitutionBondClass mancudeEdges rightOwner right &&
    mol.sameConstitutionAtom left right

/-- Fast, permutation-invariant first-shell filter for automorphism candidates. -/
def sameConstitutionShell (mol : RawMolecule) (mancudeEdges : List (ℕ × ℕ))
    (left right : ℕ) : Bool :=
  let leftNeighbors := mol.incidentAtoms left
  let rightNeighbors := mol.incidentAtoms right
  leftNeighbors.length == rightNeighbors.length &&
    leftNeighbors.all (fun neighbor =>
      (leftNeighbors.filter fun candidate =>
        mol.sameConstitutionNeighbor mancudeEdges left neighbor left candidate).length ==
      (rightNeighbors.filter fun candidate =>
        mol.sameConstitutionNeighbor mancudeEdges left neighbor right candidate).length) &&
    rightNeighbors.all (fun neighbor =>
      (rightNeighbors.filter fun candidate =>
        mol.sameConstitutionNeighbor mancudeEdges right neighbor right candidate).length ==
      (leftNeighbors.filter fun candidate =>
        mol.sameConstitutionNeighbor mancudeEdges right neighbor left candidate).length)

/-- Extending `mapping` by `left ↦ right` preserves every bond/nonbond relation already exposed. -/
def constitutionMappingConsistent (mol : RawMolecule) (mancudeEdges : List (ℕ × ℕ))
    (mapping : List (ℕ × ℕ)) (left right : ℕ) : Bool :=
  mapping.all fun pair =>
    mol.constitutionBondClass mancudeEdges left pair.1 ==
      mol.constitutionBondClass mancudeEdges right pair.2

/-- Deterministic witness search for a constitution-preserving bijection on one connected component.

The first locally admissible target is followed without backtracking, keeping the precheck linear on
large symmetric molecules.  This may miss an existing automorphism, but every successful result has
checked atom labels, injectivity, and every bond/nonbond relation, so it can only add sound ties. -/
def searchConstitutionAutomorphism (mol : RawMolecule) (mancudeEdges : List (ℕ × ℕ))
    (vertices : List ℕ) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => true
  | left :: remaining, mapping =>
      match (vertices.filter fun right =>
        !(mapping.any fun pair => pair.2 == right) &&
          mol.sameConstitutionAtom left right &&
          mol.sameConstitutionShell mancudeEdges left right &&
          mol.constitutionMappingConsistent mancudeEdges mapping left right) with
      | [] => false
      | right :: _ =>
          mol.searchConstitutionAutomorphism mancudeEdges vertices remaining
            ((left, right) :: mapping)

/-- Unweighted constitutional distance, used only as an automorphism invariant.

Any bond-preserving bijection preserves ordinary graph distance.  Precomputing distance profiles to
the seeded vertices therefore prunes impossible targets without excluding any automorphism. -/
private def constitutionDistanceFrom? (mol : RawMolecule) (target : ℕ) :
    ℕ → List ℕ → List ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, frontier, seen =>
      if frontier.contains target then some 0 else
        let next := (frontier.flatMap mol.incidentAtoms).filter fun atom => !seen.contains atom
        let fresh := next.eraseDups
        (constitutionDistanceFrom? mol target fuel fresh (seen ++ fresh)).map Nat.succ

private def constitutionDistanceProfile (mol : RawMolecule) (anchors : List ℕ)
    (atom : ℕ) : List (Option ℕ) :=
  anchors.map fun anchor =>
    constitutionDistanceFrom? mol anchor (mol.atomCount + 1) [atom] [atom]

private def constitutionProfileAt? (profiles : List (ℕ × List (Option ℕ)))
    (atom : ℕ) : Option (List (Option ℕ)) :=
  (profiles.find? fun entry => entry.1 == atom).map Prod.snd

/-- All targets that extend a partial constitutional injection at one source vertex. -/
def exactConstitutionCandidates (mol : RawMolecule) (mancudeEdges : List (ℕ × ℕ))
    (vertices : List ℕ) (mapping : List (ℕ × ℕ)) (left : ℕ) : List ℕ :=
  vertices.filter fun right =>
    !(mapping.any fun pair => pair.2 == right) &&
      mol.sameConstitutionAtom left right &&
      mol.constitutionMappingConsistent mancudeEdges mapping left right

/-- Complete backtracking automorphism search with a dynamic minimum-candidate ordering.

Choosing the still-unmapped source vertex with the fewest currently admissible targets preserves
exhaustiveness while avoiding the factorial dead ends produced by fixed vertex order on large
cyclic components. Candidate admission uses only the defining partial-isomorphism obligations:
fresh target, identical constitutional atom label, and preservation of every bond/nonbond relation
already exposed by the mapping. The former shell and distance-profile filters were useful
optimizations, but are deliberately absent here until their invariance is independently proved.
`fuel` is exactly the number of unmapped vertices at the public entry point, so it is solely a
structural termination measure and does not bound or approximate the search. -/
def searchConstitutionAutomorphismExactAux (mol : RawMolecule)
    (mancudeEdges : List (ℕ × ℕ)) (vertices : List ℕ) :
    ℕ → List ℕ → List (ℕ × ℕ) → Bool
  | 0, remaining, _ => remaining.isEmpty
  | fuel + 1, remaining, mapping =>
      match remaining with
      | [] => true
      | _ =>
          let candidates := mol.exactConstitutionCandidates mancudeEdges vertices mapping
          let ordered := sortDescBy (fun left right => left.1 ≤ right.1)
            (remaining.map fun left => ((candidates left).length, left))
          match ordered.head? with
          | none => false
          | some (_, left) =>
              (candidates left).any fun right =>
                searchConstitutionAutomorphismExactAux mol mancudeEdges vertices
                  fuel (remaining.erase left)
                  ((left, right) :: mapping)

/-- Complete seeded search for a constitution-preserving bijection.

Unlike `searchConstitutionAutomorphism`, a `false` result is a proof of absence: every admissible
target assignment has been explored. -/
def searchConstitutionAutomorphismExact (mol : RawMolecule) (mancudeEdges : List (ℕ × ℕ))
    (vertices remaining : List ℕ) (mapping : List (ℕ × ℕ)) : Bool :=
  searchConstitutionAutomorphismExactAux mol mancudeEdges vertices
    remaining.length remaining mapping

/-- Whether a constitutional automorphism fixes `center` and exchanges two ligand roots.

The negative result is exhaustive at every component size.  A greedy miss is not sufficient here:
callers retain strict canonical branch verdicts only after this symmetry alternative is disproved. -/
def hasConstitutionAutomorphismSwapping (mol : RawMolecule) (center left right : ℕ) : Bool :=
  let mancudeEdges := mol.localizedMancudeEdges
  if left == right then true
  else if !(mol.sameConstitutionAtom left right) ||
      mol.constitutionBondClass mancudeEdges center left !=
        mol.constitutionBondClass mancudeEdges center right then false
  else
    let vertices := mol.reachableAvoiding (mol.atomCount + 1) mol.atomCount [center] [center]
    let remaining := (vertices.erase center).erase left
    let seed := [(left, right), (center, center)]
    mol.searchConstitutionAutomorphismExact mancudeEdges vertices remaining seed

/-- Cheap guard restricting exact symmetry search to cyclic ligand roots, where alternative ring
openings can otherwise create an enumeration-dependent strict result. -/
def atomLiesInCycle (mol : RawMolecule) (fuel atom : ℕ) : Bool :=
  0 < mol.ringPairCount fuel atom (mol.incidentAtoms atom)

/-- Lexicographic comparison of already priority-sorted natural-number labels. -/
def compareCanonicalNatLists : List ℕ → List ℕ → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | left :: lefts, right :: rights =>
      match compare left right with
      | Ordering.eq => compareCanonicalNatLists lefts rights
      | decision => decision

/-- Exact Rule-2 shell for a branch whose complete child sphere consists only of terminal real
hydrogens.  Returning `some` proves there is no deeper Rule-1a or Rule-1b information. -/
def terminalHydrogenMasses? (mol : RawMolecule) (root : CanonicalBranchNode) : Option (List ℕ) :=
  let children := mol.canonicalChildren root
  if children.all fun child =>
      child.provenance == CanonicalNodeProvenance.realAtom && mol.atomZAt child.atom == 1 &&
        mol.canonicalTerminal child then
    some (sortDescNat (children.map fun child => mol.atomMassAt child.atom))
  else none

/-- Complete root-plus-terminal-hydrogen comparison through Rule 2.

Equal child counts and the all-terminal-hydrogen witness exhaust Rules 1a and 1b over both branches,
so the root/child mass comparison is rule-major exact rather than a premature root-isotope test. -/
def compareTerminalHydrogenShellRoots? (mol : RawMolecule) (left right : CanonicalBranchNode) :
    Option Ordering := do
  let leftMasses ← mol.terminalHydrogenMasses? left
  let rightMasses ← mol.terminalHydrogenMasses? right
  if leftMasses.length != rightMasses.length then none else
  match mol.compareCanonicalNodeThrough? CanonicalRuleStage.rule2 left right with
  | some Ordering.eq => some (compareCanonicalNatLists leftMasses rightMasses)
  | decision => decision

/-- Exact structurally recursive comparison through Rule 2.

Every non-leaf canonical child either adds a previously unseen real atom to `history`, or is a
duplicate/phantom node forced to be a leaf.  Consequently a branch has depth at most `atomCount`;
the extra step below also lets the terminal sphere establish completeness.  Unlike a bounded root
or shallow-shell Rule-2 comparison, any `some` returned here has therefore exhausted Rule 1a over
the complete branches before consulting Rules 1b and 2.  The caller's fuel remains an upper bound:
when the caller does not provide that complete depth this precheck returns `none` and leaves the original
compiled path in control. -/
def compareCanonicalBranchesStructurally? (mol : RawMolecule)
    (fuel center left right : ℕ) : Option Ordering :=
  let completeDepth := mol.atomCount + 1
  if completeDepth ≤ fuel then
    mol.compareCanonicalBranchAtSupported? completeDepth CanonicalRuleStage.rule2
      (canonicalRoot center left) (canonicalRoot center right)
  else none

/-- Compare two branches leaving the same atom, or refuse if exploration exceeds the width cap. -/
def compareBranches? (mol : RawMolecule) (fuel center left right : ℕ) : Option Ordering :=
  let leftRoot := canonicalRoot center left
  let rightRoot := canonicalRoot center right
  match mol.compareCanonicalNodeRule CanonicalRuleStage.rule1a leftRoot rightRoot with
  | Ordering.lt => some Ordering.lt
  | Ordering.gt => some Ordering.gt
  | Ordering.eq =>
      match mol.compareTerminalHydrogenShellRoots? leftRoot rightRoot with
      | some decision => some decision
      | none =>
          let automorphismTie :=
            mol.atomLiesInCycle fuel left && mol.atomLiesInCycle fuel right &&
              mol.hasConstitutionAutomorphismSwapping center left right
          if automorphismTie then some Ordering.eq else
            match mol.compareCanonicalBranchesStructurally? fuel center left right with
            | some Ordering.eq => some Ordering.eq
            | some decision => some decision
            | none => mol.compareCanonicalBranchesCompiled? fuel center left right

/-- Compare two branches, refusing when the sphere ranking and the parent-preserving cross-check
disagree.

**Measured and not currently used.**  Gating tetrahedral ranking on this agreement removed 2 of the
5 remaining suite errors but cost 50 correct assignments — 25 sacrificed per error — and still left
3.  A cheap agreement heuristic is not a route to zero wrong answers; the hierarchical digraph is.
Kept because the measurement is worth preserving and the cross-check is sound in the sense that it
can only ever cause extra refusals. -/
def compareBranchesGated? (mol : RawMolecule) (fuel center left right : ℕ) : Option Ordering :=
  match mol.compareBranches? fuel center left right with
  | some verdict =>
      let branchwise := mol.compareBranchwise crossCheckDepth [] [] center left center right
      if verdict == Ordering.eq || branchwise == Ordering.eq || verdict == branchwise then
        some verdict
      else
        none
  | none => none

/-- Compare two branches, reporting an exploration overflow as a tie.

Callers that must distinguish overflow from a genuine tie use `compareBranches?`. -/
def compareBranches (mol : RawMolecule) (fuel center left right : ℕ) : Ordering :=
  (mol.compareBranches? fuel center left right).getD Ordering.eq

/-- A comparison result that preserves the distinction between chemical equality and an analysis
that could not establish an ordering. -/
inductive BranchComparisonStatus where
  | lower
  | tied
  | higher
  | unresolved
  deriving DecidableEq, Repr

/-- Classify a branch comparison without turning bounded-search failure or a known loss of
parent/child information into a chemical tie.

The production sphere comparator supplies strict results.  When it ties, the parent-preserving
comparator must independently tie as well before the branches are called equal; disagreement or
exhaustion means that the current engine cannot decide the pair. -/
def compareBranchesStatus (mol : RawMolecule) (fuel center left right : ℕ) :
    BranchComparisonStatus :=
  match mol.compareBranches? fuel center left right with
  | none => BranchComparisonStatus.unresolved
  | some Ordering.lt => BranchComparisonStatus.lower
  | some Ordering.gt => BranchComparisonStatus.higher
  | some Ordering.eq => BranchComparisonStatus.tied

/-- Rank branches from highest to lowest priority, refusing on any tie.

Returns *positions into `branches`* rather than atom indices, so a caller can recover the
permutation from the order it supplied to priority order. -/
def rankBranchPositions? (mol : RawMolecule) (fuel center : ℕ) (branches : List ℕ) :
    Option (List ℕ) :=
  let atomOf : ℕ → ℕ := fun position => branches.getD position 0
  let before : ℕ → ℕ → Bool := fun a b =>
    mol.compareBranches fuel center (atomOf a) (atomOf b) != Ordering.lt
  let sorted := sortDescBy before (List.range branches.length)
  -- Refuse unless every adjacent pair is *strictly* ordered and no comparison overflowed.
  let strict :=
    (List.range (sorted.length - 1)).all fun index =>
      match sorted[index]?, sorted[index + 1]? with
      | some left, some right =>
          mol.compareBranches? fuel center (atomOf left) (atomOf right) == some Ordering.gt
      | _, _ => false
  if strict then some sorted else none

/-- The single highest-ranking branch, when it strictly outranks every other. -/
def topBranch? (mol : RawMolecule) (fuel center : ℕ) (branches : List ℕ) : Option ℕ :=
  match mol.rankBranchPositions? fuel center branches with
  | some (best :: _) => branches[best]?
  | _ => none

end RawMolecule

end OneCenter
end TetraStereo
