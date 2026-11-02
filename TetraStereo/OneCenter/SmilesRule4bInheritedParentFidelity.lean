
























































































import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace TetraStereo.OneCenter
namespace Rule4bInheritedParentDiagnostic

open TetraStereo.OneCenter

/-! ## Diagnostic copy of the candidate selector (replacement REGION A)

The following definitions are copied verbatim from the supplied replacement file.  They live in
this diagnostic namespace only; they are not additions to `TetraStereo.OneCenter`. -/

/-- Uppercase chiral descriptor carried by one frontier occurrence, if its live auxiliary fact is
an uppercase real-atom fact. -/
def occurrenceUppercaseDescriptor? (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option RS :=
  match cursor.node.provenance, state.factAt? cursor.node with
  | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
      if fact.uppercase then some fact.descriptor else none
  | _, _ => none

/-- The frontier occurrences that carry an uppercase chiral descriptor. -/
def occurrenceChiralFrontierCursors (state : OccurrenceAuxState)
    (frontier : List CanonicalRerootCursor) : List CanonicalRerootCursor :=
  frontier.filterMap fun cursor =>
    (occurrenceUppercaseDescriptor? state cursor).map fun _ => cursor

/-- `true` when `cursor` is not strictly below any member of `others` under the pre-Rule-4b
ordering.  `none` propagates an incomplete comparison instead of guessing. -/
def occurrencePreRule4bMaximal? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) (cursor : CanonicalRerootCursor) :
    List CanonicalRerootCursor → Option Bool
  | [] => some true
  | other :: rest =>
      match before cursor other with
      | none => none
      | some Ordering.lt => some false
      | some _ => occurrencePreRule4bMaximal? before cursor rest

/-- First chiral occurrence that is maximal in the pre-Rule-4b order among all chiral occurrences
of the layer. -/
def occurrenceFirstMaximalChiral? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) :
    List CanonicalRerootCursor → List CanonicalRerootCursor →
      Option CanonicalRerootCursor
  | [], _ => none
  | cursor :: rest, all =>
      match occurrencePreRule4bMaximal? before cursor all with
      | none => none
      | some true => some cursor
      | some false => occurrenceFirstMaximalChiral? before rest all

/-- Descriptor contribution of one occurrence inside the selected class. -/
def occurrenceClassDescriptor? (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) : Option (List RS) :=
  match cursor.node.provenance, state.factAt? cursor.node with
  | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
      if fact.uppercase then some [fact.descriptor] else some []
  | _, _ => none

/-- P-92.5.2.1(b)/(c) population of the equivalence class represented by `representative`. -/
def occurrenceClassPopulation? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) (state : OccurrenceAuxState)
    (representative : CanonicalRerootCursor) :
    List CanonicalRerootCursor → Option (List RS)
  | [] => some []
  | cursor :: rest =>
      match before representative cursor with
      | none => none
      | some Ordering.eq =>
          match occurrenceClassDescriptor? state cursor with
          | none => none
          | some descriptors =>
              match occurrenceClassPopulation? before state representative rest with
              | none => none
              | some tail => some (descriptors ++ tail)
      | some _ => occurrenceClassPopulation? before state representative rest

/-- P-92.5.2.1(b)/(c) reference choice inside one class population. -/
def occurrenceRule4bReferencesFromPopulation (descriptors : List RS) : List RS :=
  if descriptors.isEmpty then []
  else
    let rCount := (descriptors.filter fun descriptor => descriptor == RS.R).length
    let sCount := (descriptors.filter fun descriptor => descriptor == RS.S).length
    if sCount < rCount then [RS.R]
    else if rCount < sCount then [RS.S]
    else [RS.R, RS.S]

/-- Highest equivalence class of one frontier layer, then (b)/(c) majority inside it. -/
def occurrenceLayerHighestClassReferences? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) (state : OccurrenceAuxState)
    (frontier : List CanonicalRerootCursor) : Option (List RS) := do
  let candidates := occurrenceChiralFrontierCursors state frontier
  let representative ← occurrenceFirstMaximalChiral? before candidates candidates
  let population ← occurrenceClassPopulation? before state representative frontier
  some (occurrenceRule4bReferencesFromPopulation population)

/-- Option-valued P-92.5.2.1 Rule-4b reference selection over the actual reroot children of an
occurrence.  This is the candidate selector under test. -/
def occurrenceRule4bClassReferences? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) (mol : RawMolecule)
    (state : OccurrenceAuxState) :
    ℕ → List CanonicalRerootCursor → Option (List RS)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, frontier =>
      if (occurrenceChiralFrontierCursors state frontier).isEmpty then
        occurrenceRule4bClassReferences? before mol state fuel
          (frontier.flatMap fun cursor => cursor.children mol)
      else occurrenceLayerHighestClassReferences? before state frontier

/-- Pre-Rule-4b ordering of two occurrences: constitution (Rules 1a--2), then Rule 4a.  Copied
from the candidate replacement; this is the actual ordering used by the candidate selector. -/
def occurrencePreRule4bCompare? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (left right : CanonicalRerootCursor) : Option Ordering :=
  match compareCursorBranchAt mol fuel RawMolecule.CanonicalRuleStage.rule2 left right with
  | none => none
  | some Ordering.eq =>
      compareOccurrenceDescriptorAtTiedRoot? mol state fuel .rule4a left right
  | some decision => some decision





















/-- Lexicographic strict order on rank paths: smaller means senior. -/
def inheritedPathLtAux : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | left :: leftRest, right :: rightRest =>
      if left < right then true
      else if right < left then false
      else inheritedPathLtAux leftRest rightRest

def inheritedPathLt (left right : List Nat) : Bool :=
  inheritedPathLtAux left right

/-- Minimum path of a nonempty list of paths (the empty list for the empty input). -/
def inheritedMinimalPath : List (List Nat) → List Nat
  | [] => []
  | first :: rest =>
      rest.foldl (fun best candidate => if inheritedPathLt candidate best then candidate else best)
        first

/-- Assign class ids to an already sorted (senior first) sibling list.  Comparator-equal
neighbours share an id; an id is incremented only between strict classes.  The accumulator is
always passed explicitly, including the initial empty list. -/
def inheritedAssignClassIds? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) :
    List CanonicalRerootCursor → List (CanonicalRerootCursor × Nat) →
      Option (List (CanonicalRerootCursor × Nat))
  | [], acc => some acc.reverse
  | cursor :: rest, [] =>
      inheritedAssignClassIds? before rest [(cursor, 0)]
  | cursor :: rest, (previous, classId) :: acc =>
      match before cursor previous with
      | none => none
      | some Ordering.eq =>
          inheritedAssignClassIds? before rest ((cursor, classId) :: (previous, classId) :: acc)
      | some _ =>
          inheritedAssignClassIds? before rest ((cursor, classId + 1) :: (previous, classId) :: acc)

/-- One breadth level of inherited rank-path expansion.  Each equal-parent-path group is handled
separately; its pooled children are sorted by the complete pre-Rule-4b comparator and receive
class ids; the child id is appended to the inherited parent path. -/
def inheritedNextLevel? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) (mol : RawMolecule) :
    Nat → List (List Nat × CanonicalRerootCursor) →
      Option (List (List Nat × CanonicalRerootCursor))
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, entry :: rest =>
      let path := entry.1
      let group := entry :: rest.filter (fun candidate => candidate.1 == path)
      let others := rest.filter (fun candidate => !(candidate.1 == path))
      match sortCursorsBy? before (group.flatMap (fun candidate => candidate.2.children mol)) with
      | none => none
      | some sorted =>
          match inheritedAssignClassIds? before sorted [] with
          | none => none
          | some classed =>
              match inheritedNextLevel? before mol fuel others with
              | none => none
              | some tail =>
                  some (classed.map (fun classedEntry =>
                    (path ++ [classedEntry.2], classedEntry.1)) ++ tail)

/-- Diagnostic inherited-rank reference selection.  At the first level carrying uppercase
evidence, take the minimum rank path and count every uppercase descriptor at exactly that path.
Otherwise descend one level, preserving inherited parent paths. -/
def inheritedReferences? (before : CanonicalRerootCursor →
      CanonicalRerootCursor → Option Ordering) (state : OccurrenceAuxState)
    (mol : RawMolecule) :
    Nat → List (List Nat × CanonicalRerootCursor) → Option (List RS)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, frontier =>
      let candidates : List (List Nat × RS) := frontier.filterMap fun entry =>
        match occurrenceUppercaseDescriptor? state entry.2 with
        | none => none
        | some descriptor => some (entry.1, descriptor)
      if candidates.isEmpty then
        match inheritedNextLevel? before mol (frontier.length + 1) frontier with
        | none => none
        | some next => inheritedReferences? before state mol fuel next
      else
        let minimum := inheritedMinimalPath (candidates.map fun candidate => candidate.1)
        let selected := candidates.filter fun candidate => candidate.1 == minimum
        some (occurrenceRule4bReferencesFromPopulation
          (selected.map fun candidate => candidate.2))

/-! ## The concrete molecule -/

/-- Aliphatic carbon with an input tetrahedral parity annotation. -/
def tetraCarbon (parity : TetrahedralInputParity) : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some parity }

def carbonAtom : AtomSpec := AtomSpec.aliphatic Element.C
def hydrogenAtom : AtomSpec := AtomSpec.aliphatic Element.H
def oxygenAtom : AtomSpec := AtomSpec.aliphatic Element.O
def nitrogenAtom : AtomSpec := AtomSpec.aliphatic Element.N
def fluorineAtom : AtomSpec := AtomSpec.aliphatic Element.F
def chlorineAtom : AtomSpec := AtomSpec.aliphatic Element.Cl
def bromineAtom : AtomSpec := AtomSpec.aliphatic Element.Br
def iodineAtom : AtomSpec := AtomSpec.aliphatic Element.I

/-- The concrete witness, built directly as a `RawMolecule` value.

Atom indices:

| index | element | role |
|-------|---------|------|
| 0  | C | methyl carbon (tree root, no stereogenic claim) |
| 1  | C | ligand root |
| 2  | O | senior parent branch (Z = 8) |
| 3  | C | chiral carbon A (input `.anticlockwise`, authoritative `R`) |
| 4  | F | A substituent |
| 5  | Cl| A substituent |
| 6  | H | A substituent |
| 7  | N | junior parent branch (Z = 7) |
| 8  | C | chiral carbon B (input `.clockwise`, authoritative `S`) |
| 9  | H | hydrogen completing N's valence |
| 10 | Br| B substituent |
| 11 | I | B substituent |
| 12 | H | B substituent |
| 13,14,15 | H | hydrogens of methyl carbon 0 |
| 16 | C | second methyl carbon on the ligand root |
| 17,18,19 | H | hydrogens of methyl carbon 16 |

The graph is an acyclic all-single-bond tree.  Atom `1` has the two structurally identical methyl
arms `0` and `16` (each `C(H,H,H)`), so it is not a stereogenic centre.  The bond-list order is the
written order used for the parity permutations. -/
def counterexampleMolecule : RawMolecule where
  atoms :=
    [ carbonAtom,                  -- 0  methyl carbon / tree root
      carbonAtom,                  -- 1  ligand root
      oxygenAtom,                  -- 2  O parent of A
      tetraCarbon .anticlockwise,  -- 3  chiral carbon A
      fluorineAtom,                -- 4
      chlorineAtom,                -- 5
      hydrogenAtom,                -- 6  H on A
      nitrogenAtom,                -- 7  N parent of B
      tetraCarbon .clockwise,      -- 8  chiral carbon B
      hydrogenAtom,                -- 9  H on N
      bromineAtom,                 -- 10
      iodineAtom,                  -- 11
      hydrogenAtom,                -- 12 H on B
      hydrogenAtom,                -- 13 H on methyl 0
      hydrogenAtom,                -- 14
      hydrogenAtom,                -- 15
      carbonAtom,                  -- 16 second methyl carbon
      hydrogenAtom,                -- 17 H on methyl 16
      hydrogenAtom,                -- 18
      hydrogenAtom ]               -- 19
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 13, kind := .single },
      { source := 0, target := 14, kind := .single },
      { source := 0, target := 15, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 1, target := 7, kind := .single },
      { source := 1, target := 16, kind := .single },
      { source := 2, target := 3, kind := .single },
      { source := 3, target := 4, kind := .single },
      { source := 3, target := 5, kind := .single },
      { source := 3, target := 6, kind := .single },
      { source := 7, target := 8, kind := .single },
      { source := 7, target := 9, kind := .single },
      { source := 8, target := 10, kind := .single },
      { source := 8, target := 11, kind := .single },
      { source := 8, target := 12, kind := .single },
      { source := 16, target := 17, kind := .single },
      { source := 16, target := 18, kind := .single },
      { source := 16, target := 19, kind := .single } ]

/-! ### Canonical nodes and reroot cursors used by the witness -/

def centerNode : RawMolecule.CanonicalBranchNode := canonicalCenterRoot 0

def ligandRootNode : RawMolecule.CanonicalBranchNode := RawMolecule.canonicalRoot 0 1

def oxygenNode : RawMolecule.CanonicalBranchNode :=
  { atom := 2, parent := 1, history := [2, 1, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

def nitrogenNode : RawMolecule.CanonicalBranchNode :=
  { atom := 7, parent := 1, history := [7, 1, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

def ligandMethylNode : RawMolecule.CanonicalBranchNode :=
  { atom := 16, parent := 1, history := [16, 1, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

def chiralANode : RawMolecule.CanonicalBranchNode :=
  { atom := 3, parent := 2, history := [3, 2, 1, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

def chiralBNode : RawMolecule.CanonicalBranchNode :=
  { atom := 8, parent := 7, history := [8, 7, 1, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

def nitrogenHydrogenNode : RawMolecule.CanonicalBranchNode :=
  { atom := 9, parent := 7, history := [9, 7, 1, 0],
    provenance := RawMolecule.CanonicalNodeProvenance.realAtom }

def ligandRootCursor : CanonicalRerootCursor :=
  { node := ligandRootNode, previous? := some centerNode }

def oxygenCursor : CanonicalRerootCursor :=
  { node := oxygenNode, previous? := some ligandRootNode }

def nitrogenCursor : CanonicalRerootCursor :=
  { node := nitrogenNode, previous? := some ligandRootNode }

def ligandMethylCursor : CanonicalRerootCursor :=
  { node := ligandMethylNode, previous? := some ligandRootNode }

def chiralACursor : CanonicalRerootCursor :=
  { node := chiralANode, previous? := some oxygenNode }

def chiralBCursor : CanonicalRerootCursor :=
  { node := chiralBNode, previous? := some nitrogenNode }

def nitrogenHydrogenCursor : CanonicalRerootCursor :=
  { node := nitrogenHydrogenNode, previous? := some nitrogenNode }

/-! ### Structural equivalence of the two methyl arms at the ligand root

The atom-index involution swaps the tree-root methyl `0` (with hydrogens `13`, `14`, `15`) with
the second methyl `16` (with hydrogens `17`, `18`, `19`).  It fixes the ligand root `1` and every
other atom.  The checks below establish that it preserves atom labels and the whole undirected
bond relation, and that it maps the canonical subtree of one methyl arm onto the other.  Hence
atom `1` has two structurally identical substituents and is not a stereogenic centre; this
conclusion does not depend on the auxiliary fact environment. -/

/-- Index involution exchanging the two methyl arms; identity elsewhere. -/
def armSwap (i : ℕ) : ℕ :=
  if i = 0 then 16
  else if i = 16 then 0
  else if i = 13 then 17
  else if i = 17 then 13
  else if i = 14 then 18
  else if i = 18 then 14
  else if i = 15 then 19
  else if i = 19 then 15
  else i

/-- Apply `armSwap` to a canonical branch node, including its occurrence history. -/
def swapBranchNode (node : RawMolecule.CanonicalBranchNode) :
    RawMolecule.CanonicalBranchNode :=
  { atom := armSwap node.atom
    parent := armSwap node.parent
    history := node.history.map armSwap
    provenance := node.provenance }

/-- Root of the canonical branch from the ligand root into methyl carbon `0`. -/
def methyl0Node : RawMolecule.CanonicalBranchNode := RawMolecule.canonicalRoot 1 0

/-- Root of the canonical branch from the ligand root into methyl carbon `16`. -/
def methyl16Node : RawMolecule.CanonicalBranchNode := RawMolecule.canonicalRoot 1 16

/-! ### The actual authoritative auxiliary environment -/

/-- The live fail-closed builder run on the witness, at the same fuel and centre used by the
public occurrence evaluator.  No facts are supplied by hand; the state is produced by the
authoritative occurrence classification over the canonical tree. -/
def counterexampleState? : Option OccurrenceAuxState :=
  buildOccurrenceAuxStateFullyAuthoritative? counterexampleMolecule 8 0

/-! ### Evaluated outcomes -/

/-- Candidate selector output on the single ligand-root occurrence. -/
def counterexampleCandidateReferences? : Option (List RS) :=
  counterexampleState?.bind (fun state =>
    occurrenceRule4bClassReferences? (occurrencePreRule4bCompare? counterexampleMolecule state 8)
      counterexampleMolecule state 8 [ligandRootCursor])

/-- Inherited-rank diagnostic output on the same occurrence. -/
def counterexampleInheritedReferences? : Option (List RS) :=
  counterexampleState?.bind (fun state =>
    inheritedReferences? (occurrencePreRule4bCompare? counterexampleMolecule state 8) state
      counterexampleMolecule 8 [([], ligandRootCursor)])

/-- The class population used by the candidate selector (representative `B`). -/
def counterexampleCandidatePopulation? : Option (List RS) :=
  counterexampleState?.bind (fun state =>
    occurrenceClassPopulation? (occurrencePreRule4bCompare? counterexampleMolecule state 8)
      state chiralBCursor [chiralACursor, chiralBCursor, nitrogenHydrogenCursor])

/-- The candidate selector's chosen representative. -/
def counterexampleFirstMaximal? : Option CanonicalRerootCursor :=
  counterexampleState?.bind (fun state =>
    occurrenceFirstMaximalChiral? (occurrencePreRule4bCompare? counterexampleMolecule state 8)
      [chiralACursor, chiralBCursor] [chiralACursor, chiralBCursor])

/-- First inherited rank level after the ligand root. -/
def counterexampleLevelOne? : Option (List (List Nat × Nat)) :=
  counterexampleState?.bind (fun state =>
    (inheritedNextLevel? (occurrencePreRule4bCompare? counterexampleMolecule state 8)
      counterexampleMolecule 2 [([], ligandRootCursor)]).map
      (fun level => level.map (fun entry => (entry.1, entry.2.node.atom))))

/-- Second inherited rank level: the first chiral depth. -/
def counterexampleSecondLevel? : Option (List (List Nat × CanonicalRerootCursor)) :=
  counterexampleState?.bind (fun state =>
    (inheritedNextLevel? (occurrencePreRule4bCompare? counterexampleMolecule state 8)
      counterexampleMolecule 2 [([], ligandRootCursor)]).bind (fun levelOne =>
        inheritedNextLevel? (occurrencePreRule4bCompare? counterexampleMolecule state 8)
          counterexampleMolecule (levelOne.length + 1) levelOne))

def counterexampleSecondLevelAtoms? : Option (List (List Nat × Nat)) :=
  counterexampleSecondLevel?.map (fun level =>
    level.map (fun entry => (entry.1, entry.2.node.atom)))

/-! ## Closed kernel checks

Every theorem below is a closed computation (`by decide`).  There are no hypotheses, no supplied
facts, and no oracle: the occurrences, descriptors, orderings and selections are produced by the
actual definitions above. -/

theorem counterexample_atomCount : counterexampleMolecule.atomCount = 20 := by
  decide

theorem counterexample_admissible : counterexampleMolecule.admissible? = true := by
  decide

theorem counterexample_stereochemicalAdmissible :
    counterexampleMolecule.stereochemicalAdmissible? = true := by
  decide

theorem counterexample_rule2MassesKnown : counterexampleMolecule.rule2MassesKnown? = true := by
  decide

/-- The ligand root is fixed by the arm-exchange involution, which swaps the two methyl arms. -/
theorem counterexample_armSwap_fixesLigandRoot : armSwap 1 = 1 := by
  decide

/-- The two arms are genuinely distinct indices. -/
theorem counterexample_armSwap_swapsArms : armSwap 0 = 16 ∧ armSwap 16 = 0 := by
  decide

/-- The involution is a bijection on the witness atom range. -/
theorem counterexample_armSwap_involutive :
    (List.range 20).all (fun i => armSwap (armSwap i) == i) = true := by
  decide

/-- The involution preserves every atom label in the witness. -/
theorem counterexample_armSwap_preservesAtomLabels :
    (List.range 20).all (fun i =>
      decide (counterexampleMolecule.atomAt? (armSwap i) =
        counterexampleMolecule.atomAt? i)) = true := by
  decide

/-- The involution preserves the full undirected bond relation of the witness: adjacency of every
pair of atoms is unchanged.  Combined with label preservation and involutivity this is a graph
automorphism fixing the ligand root and exchanging the two methyl arms. -/
theorem counterexample_armSwap_preservesBonds :
    (List.range 20).all (fun u => (List.range 20).all (fun v =>
      counterexampleMolecule.bonds.any (fun bond => bond.connects u v) ==
        counterexampleMolecule.bonds.any (fun bond =>
          bond.connects (armSwap u) (armSwap v)))) = true := by
  decide

/-- The canonical subtree of methyl arm `0` maps onto that of methyl arm `16` under the
involution. -/
theorem counterexample_methylArms_branchChildren :
    (counterexampleMolecule.canonicalChildren methyl0Node).map swapBranchNode =
      counterexampleMolecule.canonicalChildren methyl16Node := by
  decide

/-- Both methyl arms are terminal `C(H,H,H)` branches: every child of the arm root is itself
terminal, so the mapped equality above covers the whole subtree. -/
theorem counterexample_methylArms_childrenTerminal :
    (counterexampleMolecule.canonicalChildren methyl0Node).all
        (fun node => counterexampleMolecule.canonicalTerminal node) = true ∧
      (counterexampleMolecule.canonicalChildren methyl16Node).all
        (fun node => counterexampleMolecule.canonicalTerminal node) = true := by
  decide

/-- The two methyl arms are constitutionally indistinguishable under the actual Rules-1a--2 branch
comparator. -/
theorem counterexample_methylArms_constitutionalTie :
    counterexampleMolecule.compareCanonicalBranchAtSupported? 4
        RawMolecule.CanonicalRuleStage.rule2 methyl0Node methyl16Node =
      some Ordering.eq := by
  decide

/-- Bundled structural non-stereogenicity certificate for the ligand root: the root is fixed, the
swap is an atom-label- and bond-preserving involution, and the two canonical methyl subtrees are
mapped onto each other and terminal.  Hence atom `1` carries two identical substituents rather
than a descriptor-free stereogenic centre. -/
theorem counterexample_ligandRoot_equivalentMethylArms :
    armSwap 1 = 1 ∧
      armSwap 0 = 16 ∧
      armSwap 16 = 0 ∧
      (List.range 20).all (fun i => armSwap (armSwap i) == i) = true ∧
      (List.range 20).all (fun i =>
        decide (counterexampleMolecule.atomAt? (armSwap i) =
          counterexampleMolecule.atomAt? i)) = true ∧
      (List.range 20).all (fun u => (List.range 20).all (fun v =>
        counterexampleMolecule.bonds.any (fun bond => bond.connects u v) ==
          counterexampleMolecule.bonds.any (fun bond =>
            bond.connects (armSwap u) (armSwap v)))) = true ∧
      (counterexampleMolecule.canonicalChildren methyl0Node).map swapBranchNode =
        counterexampleMolecule.canonicalChildren methyl16Node ∧
      (counterexampleMolecule.canonicalChildren methyl0Node).all
          (fun node => counterexampleMolecule.canonicalTerminal node) = true ∧
        (counterexampleMolecule.canonicalChildren methyl16Node).all
          (fun node => counterexampleMolecule.canonicalTerminal node) = true ∧
      counterexampleMolecule.compareCanonicalBranchAtSupported? 4
          RawMolecule.CanonicalRuleStage.rule2 methyl0Node methyl16Node =
        some Ordering.eq := by
  decide

/-- The fail-closed authoritative builder succeeds on the witness. -/
theorem counterexample_state_available : counterexampleState?.isSome = true := by
  decide

/-- The authoritative fact at `A` is `R`, uppercase. -/
theorem counterexample_factA :
    ((counterexampleState?.bind (fun state => state.factAt? chiralANode)).map
        (fun fact => (fact.atom, fact.descriptor, fact.uppercase))) =
      some (3, RS.R, true) := by
  decide

/-- The authoritative fact at `B` is `S`, uppercase. -/
theorem counterexample_factB :
    ((counterexampleState?.bind (fun state => state.factAt? chiralBNode)).map
        (fun fact => (fact.atom, fact.descriptor, fact.uppercase))) =
      some (8, RS.S, true) := by
  decide

/-- The builder assigns no uppercase descriptor to the ligand root; the structural certificate
above shows that this absence is justified rather than assumed. -/
theorem counterexample_ligandRoot_noDescriptor :
    (counterexampleState?.bind (fun state => state.factAt? ligandRootNode)).isSome = false := by
  decide

/-- Source priority at the branch point: oxygen outranks nitrogen by Rule-1a atomic number. -/
theorem counterexample_sourcePriority :
    compareCursorBranchAt counterexampleMolecule 8 RawMolecule.CanonicalRuleStage.rule2
        oxygenCursor nitrogenCursor =
      some Ordering.gt := by
  decide

/-- The same source priority under the actual pre-Rule-4b wrapper. -/
theorem counterexample_sourcePriority_pre4b :
    counterexampleState?.bind (fun state =>
        occurrencePreRule4bCompare? counterexampleMolecule state 8 oxygenCursor nitrogenCursor) =
      some Ordering.gt := by
  decide

/-- Freshly rerooted descendants: `A`'s subtree `[Cl, F, H]` is below `B`'s `[I, Br, H]`. -/
theorem counterexample_rerootedPriority :
    compareCursorBranchAt counterexampleMolecule 8 RawMolecule.CanonicalRuleStage.rule2
        chiralACursor chiralBCursor =
      some Ordering.lt := by
  decide

theorem counterexample_rerootedPriority_reverse :
    compareCursorBranchAt counterexampleMolecule 8 RawMolecule.CanonicalRuleStage.rule2
        chiralBCursor chiralACursor =
      some Ordering.gt := by
  decide

/-- The fresh-reroot reversal under the actual pre-Rule-4b wrapper. -/
theorem counterexample_rerootedPriority_pre4b :
    counterexampleState?.bind (fun state =>
        occurrencePreRule4bCompare? counterexampleMolecule state 8 chiralACursor chiralBCursor) =
      some Ordering.lt := by
  decide

/-- The decisive fresh-reroot label is `I (53) > Cl (17)`, not a hand-supplied ordering. -/
theorem counterexample_iodineAboveChlorine :
    RawMolecule.compareCanonicalNodeRule? counterexampleMolecule
        RawMolecule.CanonicalRuleStage.rule1a
        (RawMolecule.canonicalRoot 0 11) (RawMolecule.canonicalRoot 0 5) =
      some Ordering.gt := by
  decide

/-- First inherited level: the ligand root branches O, N, then the methyl carbon 16, ranked by
atomic number. -/
theorem counterexample_levelOne :
    counterexampleLevelOne? = some [([0], 2), ([1], 7), ([2], 16)] := by
  decide

/-- First chiral depth: A inherits `[0,0]` under O; B inherits `[1,0]` under N; the N hydrogen
inherits `[1,1]`; the three hydrogens of the second methyl share `[2,0]`. -/
theorem counterexample_secondLevel :
    counterexampleSecondLevelAtoms? =
      some [([0, 0], 3), ([1, 0], 8), ([1, 1], 9),
            ([2, 0], 17), ([2, 0], 18), ([2, 0], 19)] := by
  decide

/-- Lexicographic inherited precedence: `A`'s path is strictly senior to `B`'s. -/
theorem counterexample_inheritedPathPrecedence :
    inheritedPathLt [0, 0] [1, 0] = true := by
  decide

theorem counterexample_inheritedPathPrecedence_reverse :
    inheritedPathLt [1, 0] [0, 0] = false := by
  decide

/-- The candidate selector's representative is `B` (the fresh-reroot maximum). -/
theorem counterexample_candidateRepresentative :
    counterexampleFirstMaximal? = some chiralBCursor := by
  decide

/-- The candidate class population is the single uppercase `S` of `B`. -/
theorem counterexample_candidatePopulation :
    counterexampleCandidatePopulation? = some [RS.S] := by
  decide

/-- The candidate selector returns `S`. -/
theorem counterexample_candidateReferences :
    counterexampleCandidateReferences? = some [RS.S] := by
  decide

/-- The inherited-rank selection returns `R`. -/
theorem counterexample_inheritedReferences :
    counterexampleInheritedReferences? = some [RS.R] := by
  decide

/-- The candidate and inherited selections disagree on the actual molecule. -/
theorem counterexample_discrepancy :
    counterexampleCandidateReferences? ≠ counterexampleInheritedReferences? := by
  decide

/-- Bundled statement of the failure: the candidate selector picks the `S` descriptor of the
junior N branch although the senior O branch's carbon carries `R`. -/
theorem counterexample_failure :
    counterexampleCandidateReferences? = some [RS.S] ∧
      counterexampleInheritedReferences? = some [RS.R] :=
  ⟨counterexample_candidateReferences, counterexample_inheritedReferences⟩

/-- Bundled statement of the mechanism: inherited source priority says `O > N`, the fresh rerooted
subtrees say `B > A`, the inherited rank paths say `A` is senior, and the ligand root's two methyl
arms are constitutionally indistinguishable.  The full automorphism certificate is
`counterexample_ligandRoot_equivalentMethylArms`. -/
theorem counterexample_mechanism :
    counterexampleState?.bind (fun state =>
        occurrencePreRule4bCompare? counterexampleMolecule state 8 oxygenCursor nitrogenCursor) =
        some Ordering.gt ∧
      counterexampleState?.bind (fun state =>
        occurrencePreRule4bCompare? counterexampleMolecule state 8 chiralACursor chiralBCursor) =
        some Ordering.lt ∧
      inheritedPathLt [0, 0] [1, 0] = true ∧
      counterexampleMolecule.compareCanonicalBranchAtSupported? 4
          RawMolecule.CanonicalRuleStage.rule2 methyl0Node methyl16Node =
        some Ordering.eq :=
  ⟨counterexample_sourcePriority_pre4b, counterexample_rerootedPriority_pre4b,
    counterexample_inheritedPathPrecedence, counterexample_methylArms_constitutionalTie⟩

/-! ## Kernel-authority guards

Each main endpoint below is checked to depend only on kernel authority: no external evaluator
trust, no project-level assumptions, and no unfinished placeholders. -/

assert_kernel_only counterexample_atomCount
assert_kernel_only counterexample_admissible
assert_kernel_only counterexample_stereochemicalAdmissible
assert_kernel_only counterexample_rule2MassesKnown
assert_kernel_only counterexample_ligandRoot_equivalentMethylArms
assert_kernel_only counterexample_state_available
assert_kernel_only counterexample_factA
assert_kernel_only counterexample_factB
assert_kernel_only counterexample_ligandRoot_noDescriptor
assert_kernel_only counterexample_sourcePriority
assert_kernel_only counterexample_sourcePriority_pre4b
assert_kernel_only counterexample_rerootedPriority
assert_kernel_only counterexample_rerootedPriority_reverse
assert_kernel_only counterexample_rerootedPriority_pre4b
assert_kernel_only counterexample_iodineAboveChlorine
assert_kernel_only counterexample_levelOne
assert_kernel_only counterexample_secondLevel
assert_kernel_only counterexample_inheritedPathPrecedence
assert_kernel_only counterexample_inheritedPathPrecedence_reverse
assert_kernel_only counterexample_candidateRepresentative
assert_kernel_only counterexample_candidatePopulation
assert_kernel_only counterexample_candidateReferences
assert_kernel_only counterexample_inheritedReferences
assert_kernel_only counterexample_discrepancy
assert_kernel_only counterexample_failure
assert_kernel_only counterexample_mechanism

end Rule4bInheritedParentDiagnostic
end TetraStereo.OneCenter
