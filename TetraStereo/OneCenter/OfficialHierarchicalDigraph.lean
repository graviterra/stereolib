import TetraStereo.OneCenter.CIPOfficialRules

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

section

/-!
  Official hierarchical-digraph provenance.

  The older descriptor engine compares flattened finite key lists.  This module starts the next
  layer: a proof-facing hierarchical digraph whose nodes remember why they exist.  The generated
  nodes distinguish real atoms, multiple-bond duplicates, ring/cycle duplicates, and explicit
  phantom/lone-pair/auxiliary placeholders, then compare breadth-first layers by official rule
  traces.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Placeholder classes needed by a production official CIP hierarchical digraph. -/
inductive OfficialPhantomNodeKind where
  | phantom
  | lonePair
  | auxiliary
  deriving DecidableEq, Repr

/-- Provenance for a node in the official hierarchical digraph.

The distance field records the distance from the digraph root to the atom whose duplicate is being
represented.  Smaller duplicate-root distance has higher Rule-1b priority. -/
inductive OfficialCIPNodeProvenance where
  | realAtom
  | multipleBondDuplicate (duplicateRootDistance : ℕ)
  | ringDuplicate (duplicateRootDistance : ℕ)
  | placeholder (kind : OfficialPhantomNodeKind) (rootDistance : ℕ)
  deriving DecidableEq, Repr

namespace OfficialCIPNodeProvenance

/-- Duplicate-root distance, when the node is a duplicate or placeholder carrying distance data. -/
def duplicateRootDistance? : OfficialCIPNodeProvenance → Option ℕ
  | realAtom => none
  | multipleBondDuplicate distance => some distance
  | ringDuplicate distance => some distance
  | placeholder _ distance => some distance

/-- Whether this node is a duplicate leaf in the current graph-generated digraph. -/
def isDuplicateLeaf : OfficialCIPNodeProvenance → Bool
  | multipleBondDuplicate _ => true
  | ringDuplicate _ => true
  | _ => false

@[simp] theorem duplicateRootDistance?_realAtom :
    duplicateRootDistance? realAtom = none :=
  rfl

@[simp] theorem duplicateRootDistance?_multipleBondDuplicate (distance : ℕ) :
    duplicateRootDistance? (multipleBondDuplicate distance) = some distance :=
  rfl

@[simp] theorem duplicateRootDistance?_ringDuplicate (distance : ℕ) :
    duplicateRootDistance? (ringDuplicate distance) = some distance :=
  rfl

@[simp] theorem isDuplicateLeaf_multipleBondDuplicate (distance : ℕ) :
    isDuplicateLeaf (multipleBondDuplicate distance) = true :=
  rfl

@[simp] theorem isDuplicateLeaf_ringDuplicate (distance : ℕ) :
    isDuplicateLeaf (ringDuplicate distance) = true :=
  rfl

@[simp] theorem isDuplicateLeaf_realAtom :
    isDuplicateLeaf realAtom = false :=
  rfl

end OfficialCIPNodeProvenance

/-- First zero-based index of `target` in a list. -/
def firstIndexOf? {α : Type*} [DecidableEq α] (target : α) : List α → Option ℕ
  | [] => none
  | value :: values =>
      if value = target then
        some 0
      else
        (firstIndexOf? target values).map Nat.succ

@[simp] theorem firstIndexOf?_cons_self {α : Type*} [DecidableEq α]
    (target : α) (values : List α) :
    firstIndexOf? target (target :: values) = some 0 := by
  simp [firstIndexOf?]

/-- A node of the official hierarchical digraph.  `current? = none` is reserved for explicit
phantom/lone-pair/auxiliary placeholders; graph-generated nodes always carry `some atom`. -/
structure OfficialCIPNode (V : Type*) where
  current? : Option V
  history : List V
  provenance : OfficialCIPNodeProvenance
  deriving DecidableEq, Repr

namespace OfficialCIPNode

variable {V : Type*} [DecidableEq V]

/-- A real, non-duplicate branch whose history is a simple atom path. -/
def ActiveSimple (node : OfficialCIPNode V) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧ node.history.Nodup

/-- Root node at a real atom. -/
def root (atom : V) : OfficialCIPNode V where
  current? := some atom
  history := [atom]
  provenance := OfficialCIPNodeProvenance.realAtom

/-- Root edge used for ligand comparison: the current ligand remembers the stereocenter parent. -/
def rootFromEdge (parent current : V) : OfficialCIPNode V where
  current? := some current
  history := [current, parent]
  provenance := OfficialCIPNodeProvenance.realAtom

/-- Explicit placeholder node.  Placeholder nodes are leaves. -/
def placeholder (kind : OfficialPhantomNodeKind) (rootDistance : ℕ) : OfficialCIPNode V where
  current? := none
  history := []
  provenance := OfficialCIPNodeProvenance.placeholder kind rootDistance

/-- Explicit phantom-node leaf. -/
def phantom (rootDistance : ℕ) : OfficialCIPNode V :=
  placeholder OfficialPhantomNodeKind.phantom rootDistance

/-- Explicit lone-pair-node leaf. -/
def lonePair (rootDistance : ℕ) : OfficialCIPNode V :=
  placeholder OfficialPhantomNodeKind.lonePair rootDistance

/-- Explicit auxiliary-descriptor-node leaf. -/
def auxiliary (rootDistance : ℕ) : OfficialCIPNode V :=
  placeholder OfficialPhantomNodeKind.auxiliary rootDistance

/-- The immediate predecessor in the stored branch history. -/
def parent? (node : OfficialCIPNode V) : Option V :=
  match node.history with
  | _ :: parent :: _ => some parent
  | _ => none

/-- Branch depth from the root. -/
def depth (node : OfficialCIPNode V) : ℕ :=
  node.history.length - 1

/-- Is the node a duplicate leaf? -/
def isDuplicateLeaf (node : OfficialCIPNode V) : Bool :=
  node.provenance.isDuplicateLeaf

/-- Distance from the root to the atom being duplicated.  If the atom has not occurred on the
branch yet, the duplicated root is the child position itself. -/
def duplicateRootDistance (node : OfficialCIPNode V) (atom : V) : ℕ :=
  (firstIndexOf? atom node.history.reverse).getD (node.depth + 1)

/-- Total Rule-1b observation. Real nodes use their own sphere; duplicate and placeholder nodes
retain the sphere of their duplicated root. Totality is essential: treating real nodes as
inapplicable makes equality nontransitive against duplicate nodes. -/
def rule1bRootDistance (node : OfficialCIPNode V) : ℕ :=
  match node.provenance with
  | OfficialCIPNodeProvenance.realAtom => node.depth
  | OfficialCIPNodeProvenance.multipleBondDuplicate distance => distance
  | OfficialCIPNodeProvenance.ringDuplicate distance => distance
  | OfficialCIPNodeProvenance.placeholder _ distance => distance

/-- Provenance assigned to a generated child copy.  Copy index `0` is the real graph edge; later
copies are multiple-bond duplicate nodes.  A zero-index child whose atom is already in the branch
is a ring/cycle duplicate.  A multiple-bond duplicate is rooted at the atom to which it is
attached, so its Rule-1b distance is the parent node's sphere. -/
def childProvenance (node : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    OfficialCIPNodeProvenance :=
  if copyIndex = 0 then
    if next ∈ node.history then
      OfficialCIPNodeProvenance.ringDuplicate (node.duplicateRootDistance next)
    else
      OfficialCIPNodeProvenance.realAtom
  else
    OfficialCIPNodeProvenance.multipleBondDuplicate node.depth

/-- Extend a graph-generated node by one child copy. -/
def extend (node : OfficialCIPNode V) (next : V) (copyIndex : ℕ) : OfficialCIPNode V where
  current? := some next
  history := next :: node.history
  provenance := node.childProvenance next copyIndex

@[simp] theorem extend_current? (node : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    (node.extend next copyIndex).current? = some next :=
  rfl

@[simp] theorem extend_history (node : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    (node.extend next copyIndex).history = next :: node.history :=
  rfl

@[simp] theorem extend_history_length (node : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    (node.extend next copyIndex).history.length = node.history.length + 1 := by
  simp [extend]

omit [DecidableEq V] in
theorem activeSimple_rootFromEdge {parent current : V} (h : current ≠ parent) :
    (rootFromEdge parent current).ActiveSimple := by
  constructor
  · rfl
  · simp [rootFromEdge, h]

omit [DecidableEq V] in
@[simp] theorem parent?_rootFromEdge (parent current : V) :
    (rootFromEdge parent current).parent? = some parent := by
  rfl

@[simp] theorem childProvenance_copy_pos (node : OfficialCIPNode V) (next : V)
    {copyIndex : ℕ} (h : copyIndex ≠ 0) :
    node.childProvenance next copyIndex =
      OfficialCIPNodeProvenance.multipleBondDuplicate node.depth := by
  simp [childProvenance, h]

@[simp] theorem childProvenance_ring_duplicate (node : OfficialCIPNode V) (next : V)
    (h : next ∈ node.history) :
    node.childProvenance next 0 =
      OfficialCIPNodeProvenance.ringDuplicate (node.duplicateRootDistance next) := by
  simp [childProvenance, h]

@[simp] theorem childProvenance_real (node : OfficialCIPNode V) (next : V)
    (h : next ∉ node.history) :
    node.childProvenance next 0 = OfficialCIPNodeProvenance.realAtom := by
  simp [childProvenance, h]

@[simp] theorem extend_provenance (node : OfficialCIPNode V) (next : V) (copyIndex : ℕ) :
    (node.extend next copyIndex).provenance = node.childProvenance next copyIndex :=
  rfl

omit [DecidableEq V] in
@[simp] theorem placeholder_isDuplicateLeaf (kind : OfficialPhantomNodeKind)
    (rootDistance : ℕ) :
    (placeholder (V := V) kind rootDistance).isDuplicateLeaf = false :=
  rfl

omit [DecidableEq V] in
@[simp] theorem phantom_current? (rootDistance : ℕ) :
    (phantom (V := V) rootDistance).current? = none :=
  rfl

omit [DecidableEq V] in
@[simp] theorem lonePair_current? (rootDistance : ℕ) :
    (lonePair (V := V) rootDistance).current? = none :=
  rfl

omit [DecidableEq V] in
@[simp] theorem auxiliary_current? (rootDistance : ℕ) :
    (auxiliary (V := V) rootDistance).current? = none :=
  rfl

end OfficialCIPNode

namespace CIPRuleEngine

/-- Compare an official hierarchical-digraph trace first; if it ties, consult descriptor-rich
official ligand contexts in the same Rule 3/4/5 order used by the key-based engine. -/
def compareDigraphThenOfficialTrace (digraphTrace : List CIPRuleDecision)
    (left right : OfficialLigandRuleContext) : List CIPRuleDecision :=
  if cipTraceOutcome digraphTrace = Ordering.eq then
    digraphTrace ++ compareOfficialContextTrace left right
  else
    digraphTrace

/-- Proof-carrying comparison with an official hierarchical-digraph trace before context rules. -/
def compareDigraphThenOfficialCertificate (digraphTrace : List CIPRuleDecision)
    (left right : OfficialLigandRuleContext) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace (compareDigraphThenOfficialTrace digraphTrace left right)

@[simp] theorem compareDigraphThenOfficialCertificate_outcome
    (digraphTrace : List CIPRuleDecision) (left right : OfficialLigandRuleContext) :
    (compareDigraphThenOfficialCertificate digraphTrace left right).outcome =
      cipTraceOutcome (compareDigraphThenOfficialTrace digraphTrace left right) :=
  rfl

theorem compareDigraphThenOfficialTrace_outcome_of_digraph_eq
    {digraphTrace : List CIPRuleDecision} {left right : OfficialLigandRuleContext}
    (h : cipTraceOutcome digraphTrace = Ordering.eq) :
    cipTraceOutcome (compareDigraphThenOfficialTrace digraphTrace left right) =
      cipTraceOutcome (compareOfficialContextTrace left right) := by
  simp [compareDigraphThenOfficialTrace, h, cipTraceOutcome_append_of_left_eq h]

theorem compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq
    {digraphTrace : List CIPRuleDecision} {left right : OfficialLigandRuleContext}
    (h : cipTraceOutcome digraphTrace ≠ Ordering.eq) :
    cipTraceOutcome (compareDigraphThenOfficialTrace digraphTrace left right) =
      cipTraceOutcome digraphTrace := by
  simp [compareDigraphThenOfficialTrace, h]

end CIPRuleEngine

namespace MoleculeGraph

open OfficialCIPNodeProvenance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Neighbor copies with copy indices.  For a bond order `n`, copy indices are `0, ..., n-1`. -/
noncomputable def officialNeighborCopies (m : MoleculeGraph V) (atom : V) : List (V × ℕ) :=
  (m.neighborFinset atom).toList.flatMap fun neighbor =>
    (List.range (m.bond atom neighbor)).map fun copyIndex => (neighbor, copyIndex)

/-- Child copies for a non-root node remove exactly the zero-index parent occurrence, matching the
old raw-CIP convention while preserving multiplicity provenance for remaining copies. -/
noncomputable def officialChildCopies (m : MoleculeGraph V) (node : OfficialCIPNode V) : List (V × ℕ) :=
  match node.current? with
  | none => []
  | some current =>
      match node.parent? with
      | none => m.officialNeighborCopies current
      | some parent =>
          (m.officialNeighborCopies current).filter fun copy =>
            !(copy.1 == parent && copy.2 == 0)

/-- Official hierarchical-digraph children.  Duplicate nodes and placeholders are leaves. -/
noncomputable def officialCIPChildren (m : MoleculeGraph V) (node : OfficialCIPNode V) :
    List (OfficialCIPNode V) :=
  if node.isDuplicateLeaf then
    []
  else
    (m.officialChildCopies node).map fun copy => node.extend copy.1 copy.2

/-- One breadth-first layer step in the official hierarchical digraph. -/
noncomputable def officialCIPNextFrontier (m : MoleculeGraph V) (frontier : List (OfficialCIPNode V)) :
    List (OfficialCIPNode V) :=
  frontier.flatMap fun node => m.officialCIPChildren node

/-- A terminal official frontier is a layer whose nodes have no expandable children. -/
def OfficialTerminalFrontier (m : MoleculeGraph V) (frontier : List (OfficialCIPNode V)) :
    Prop :=
  ∀ node, node ∈ frontier → m.officialCIPChildren node = []

/-- A frontier is active-simple when every expandable/non-duplicate node is a real atom with a
duplicate-free branch history.  Duplicate leaves are allowed because they do not expand further. -/
def OfficialFrontierActiveSimple (_m : MoleculeGraph V) (frontier : List (OfficialCIPNode V)) :
    Prop :=
  ∀ node, node ∈ frontier → node.isDuplicateLeaf = false → node.ActiveSimple

/-- Iterate official hierarchical-digraph frontiers. -/
noncomputable def officialCIPFrontier (m : MoleculeGraph V) :
    ℕ → List (OfficialCIPNode V) → List (OfficialCIPNode V)
  | 0, frontier => frontier
  | fuel + 1, frontier => m.officialCIPFrontier fuel (m.officialCIPNextFrontier frontier)

/-- Label of an official node. Duplicate nodes retain atomic number under Rule 1a but carry zero
Rule-2 mass, matching the total production/declarative hierarchy. Placeholders are zero-label
leaves. -/
def officialNodeAtomLabel (m : MoleculeGraph V) (node : OfficialCIPNode V) :
    AtomLabel :=
  match node.current? with
  | some atom =>
      match node.provenance with
      | OfficialCIPNodeProvenance.realAtom => m.rawCIPAtomLabel atom
      | _ => toLex (m.atomZ atom, 0)
  | none => toLex (0, 0)

/-- Closer duplicate roots have higher priority. -/
def compareCloserRootDistance (left right : ℕ) : Ordering :=
  if left < right then Ordering.gt else if right < left then Ordering.lt else Ordering.eq

/-- Rule-1b root-proximity decision over the total distance observation of every node. -/
def duplicateRootDistanceDecision (left right : OfficialCIPNode V) : CIPRuleDecision where
  rule := CIPRuleFamily.duplicateAtom
  outcome := compareCloserRootDistance left.rule1bRootDistance right.rule1bRootDistance

/-- Node-provenance trace consulted after atom-label comparison. -/
def compareOfficialNodeProvenanceTrace (left right : OfficialCIPNode V) :
    List CIPRuleDecision :=
  [duplicateRootDistanceDecision left right]

/-- Compare two official digraph nodes in normative rule order: Rule 1a atomic number, Rule 1b
total root distance, then Rule 2 mass. -/
def compareOfficialNodeTrace (m : MoleculeGraph V) (left right : OfficialCIPNode V) :
    List CIPRuleDecision :=
  let leftLabel := m.officialNodeAtomLabel left
  let rightLabel := m.officialNodeAtomLabel right
  [CIPRuleEngine.priorityNatDecision CIPRuleFamily.atomicNumber
      (ofLex leftLabel).1 (ofLex rightLabel).1,
    duplicateRootDistanceDecision left right,
    CIPRuleEngine.priorityNatDecision CIPRuleFamily.isotopeMass
      (ofLex leftLabel).2 (ofLex rightLabel).2]

/-- Unary key used only to canonicalize a sphere before its rule-by-rule comparison. Atomic number
and mass are descending; the `OrderDual` fields make a nearer Rule-1b root and a shorter stored
history sort first. Because this is a unary key in a linear order, layer canonicalization cannot
depend on the input enumeration. -/
abbrev OfficialNodeSortKey :=
  ℕ ×ₗ (OrderDual ℕ ×ₗ (ℕ ×ₗ OrderDual ℕ))

def officialNodeSortKey (m : MoleculeGraph V) (node : OfficialCIPNode V) :
    OfficialNodeSortKey :=
  let label := m.officialNodeAtomLabel node
  toLex ((ofLex label).1,
    toLex ((node.rule1bRootDistance : OrderDual ℕ),
      toLex ((ofLex label).2, (node.history.length : OrderDual ℕ))))

/-- Executable comparison of the four unary sort observations. This direct comparator avoids
executing the proof-oriented nested `Lex` order while remaining extensionally equal to it. -/
def compareOfficialNodesForSort (m : MoleculeGraph V)
    (left right : OfficialCIPNode V) : Ordering :=
  compareLex
    (Ordering.byKey (fun node => (ofLex (m.officialNodeAtomLabel node)).1) compare)
    (compareLex
      (Ordering.byKey OfficialCIPNode.rule1bRootDistance (flip compare))
      (compareLex
        (Ordering.byKey (fun node => (ofLex (m.officialNodeAtomLabel node)).2) compare)
        (Ordering.byKey (fun node : OfficialCIPNode V => node.history.length) (flip compare))))
    left right

/-- The executable comparator is exactly comparison of the proof-facing unary key. -/
theorem compareOfficialNodesForSort_eq_compare_sortKey (m : MoleculeGraph V)
    (left right : OfficialCIPNode V) :
    m.compareOfficialNodesForSort left right =
      compare (m.officialNodeSortKey left) (m.officialNodeSortKey right) := by
  simp only [compareOfficialNodesForSort, officialNodeSortKey, Prod.Lex.compare_def,
    compareLex, compareOn, Ordering.byKey, Ordering.then, ofLex_toLex,
    OrderDual.instOrd, flip]

/-- Deterministic descending node order for layer comparison, defined by a unary linear-order key.
The former pairwise relation tied every real node against every duplicate; that equality was not
transitive and therefore made merge-sort output depend on enumeration order. -/
def officialNodeBefore (m : MoleculeGraph V) (left right : OfficialCIPNode V) : Bool :=
  m.compareOfficialNodesForSort left right != Ordering.lt

/-- Boolean executable ordering and descending unary-key ordering coincide. -/
theorem officialNodeBefore_eq_decide_sortKey_ge (m : MoleculeGraph V)
    (left right : OfficialCIPNode V) :
    m.officialNodeBefore left right =
      decide (m.officialNodeSortKey right ≤ m.officialNodeSortKey left) := by
  unfold officialNodeBefore
  rw [m.compareOfficialNodesForSort_eq_compare_sortKey]
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne, decide_eq_true_eq]
  constructor
  · intro notCompared
    exact le_of_not_gt fun lower => notCompared (compare_lt_iff_lt.mpr lower)
  · intro reverseLe compared
    exact (not_lt_of_ge reverseLe) (compare_lt_iff_lt.mp compared)

/-- Sort one official digraph layer in descending official node order. -/
def sortOfficialLayer (m : MoleculeGraph V) (layer : List (OfficialCIPNode V)) :
    List (OfficialCIPNode V) :=
  layer.mergeSort (m.officialNodeBefore)

/-- Rule-traced comparison of two already-sorted official layers. -/
def compareOfficialNodeListTrace (m : MoleculeGraph V) :
    List (OfficialCIPNode V) → List (OfficialCIPNode V) → List CIPRuleDecision
  | [], [] => []
  | [], _ :: _ => [CIPRuleEngine.frontierExhaustionDecision Ordering.lt]
  | _ :: _, [] => [CIPRuleEngine.frontierExhaustionDecision Ordering.gt]
  | left :: lefts, right :: rights =>
      m.compareOfficialNodeTrace left right ++ m.compareOfficialNodeListTrace lefts rights

/-- Rule-traced comparison of two official breadth-first layers. -/
def compareOfficialLayerTrace (m : MoleculeGraph V)
    (left right : List (OfficialCIPNode V)) : List CIPRuleDecision :=
  m.compareOfficialNodeListTrace (m.sortOfficialLayer left) (m.sortOfficialLayer right)

/-- Fuelled official hierarchical-digraph comparison.  Each step compares one breadth-first layer;
if it ties, comparison proceeds to the next layer. -/
noncomputable def compareOfficialHierarchicalDigraphTrace (m : MoleculeGraph V) :
    ℕ → List (OfficialCIPNode V) → List (OfficialCIPNode V) → List CIPRuleDecision
  | 0, _, _ => []
  | fuel + 1, left, right =>
      let layerTrace := m.compareOfficialLayerTrace left right
      if cipTraceOutcome layerTrace = Ordering.eq then
        layerTrace ++
          m.compareOfficialHierarchicalDigraphTrace fuel
            (m.officialCIPNextFrontier left) (m.officialCIPNextFrontier right)
      else
        layerTrace

/-- Proof-carrying official hierarchical-digraph comparison. -/
noncomputable def compareOfficialHierarchicalDigraphCertificate (m : MoleculeGraph V) (fuel : ℕ)
    (left right : List (OfficialCIPNode V)) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace (m.compareOfficialHierarchicalDigraphTrace fuel left right)

/-- Compare two ligand branches as official hierarchical digraphs rooted at a shared center. -/
noncomputable def compareOfficialHierarchicalDigraphFrom (m : MoleculeGraph V) (fuel : ℕ)
    (center left right : V) : CIPTraceCertificate :=
  m.compareOfficialHierarchicalDigraphCertificate fuel
    [OfficialCIPNode.rootFromEdge center left] [OfficialCIPNode.rootFromEdge center right]

/-- Compare two ligand branches by official hierarchical digraph first, then official descriptor
contexts if the digraph trace ties. -/
noncomputable def compareOfficialHierarchicalDigraphThenContextFrom (m : MoleculeGraph V) (fuel : ℕ)
    (center left right : V) (leftContext rightContext : CIPRuleEngine.OfficialLigandRuleContext) :
    CIPTraceCertificate :=
  CIPRuleEngine.compareDigraphThenOfficialCertificate
    (m.compareOfficialHierarchicalDigraphTrace fuel
      [OfficialCIPNode.rootFromEdge center left] [OfficialCIPNode.rootFromEdge center right])
    leftContext rightContext

@[simp] theorem compareCloserRootDistance_self (distance : ℕ) :
    compareCloserRootDistance distance distance = Ordering.eq := by
  simp [compareCloserRootDistance]

theorem compareCloserRootDistance_eq_gt_of_lt {left right : ℕ} (h : left < right) :
    compareCloserRootDistance left right = Ordering.gt := by
  simp [compareCloserRootDistance, h]

theorem compareCloserRootDistance_eq_lt_of_lt {left right : ℕ} (h : right < left) :
    compareCloserRootDistance left right = Ordering.lt := by
  have hnot : ¬ left < right := Nat.not_lt_of_ge h.le
  simp [compareCloserRootDistance, hnot, h]

/-- Rule 1b's total natural-number comparator is ordinary comparison with its orientation reversed.
This identity transfers the standard global ordering laws to Rule 1b. -/
theorem compareCloserRootDistance_eq_flip_compare (left right : ℕ) :
    compareCloserRootDistance left right = flip compare left right := by
  by_cases leftRight : left < right
  · have compared : compare right left = Ordering.gt := Nat.compare_eq_gt.mpr leftRight
    simp [compareCloserRootDistance, leftRight, flip, compared]
  · by_cases rightLeft : right < left
    · have compared : compare right left = Ordering.lt := Nat.compare_eq_lt.mpr rightLeft
      simp [compareCloserRootDistance, leftRight, rightLeft, flip, compared]
    · have equal : left = right := Nat.le_antisymm (Nat.le_of_not_gt rightLeft)
          (Nat.le_of_not_gt leftRight)
      subst right
      simp [compareCloserRootDistance, flip]

/-- In particular, corrected total Rule 1b is an oriented transitive comparator. This excludes the
old `duplicate < real = duplicate` nontransitivity at the comparator level. -/
theorem compareCloserRootDistance_transCmp : Std.TransCmp compareCloserRootDistance := by
  have comparatorEquality : compareCloserRootDistance = flip compare := by
    funext left right
    exact compareCloserRootDistance_eq_flip_compare left right
  rw [comparatorEquality]
  infer_instance

/-- Projecting the canonicalized layer to its unary sort keys is exactly sorting those keys in
descending linear order. -/
theorem map_officialNodeSortKey_sortOfficialLayer (m : MoleculeGraph V)
    (layer : List (OfficialCIPNode V)) :
    (m.sortOfficialLayer layer).map m.officialNodeSortKey =
      (layer.map m.officialNodeSortKey).mergeSort
        (fun left right => decide (right ≤ left)) := by
  unfold sortOfficialLayer
  apply List.map_mergeSort
  intro left _leftPresent right _rightPresent
  exact m.officialNodeBefore_eq_decide_sortKey_ge left right

private theorem sortOfficialNodeKeys_eq_of_perm
    {left right : List OfficialNodeSortKey} (permutation : left.Perm right) :
    left.mergeSort (fun first second => decide (second ≤ first)) =
      right.mergeSort (fun first second => decide (second ≤ first)) := by
  let descending : OfficialNodeSortKey → OfficialNodeSortKey → Prop :=
    fun first second => second ≤ first
  haveI : IsTrans OfficialNodeSortKey descending :=
    ⟨by
      intro first second third firstSecond secondThird
      exact le_trans secondThird firstSecond⟩
  haveI : Std.Total descending :=
    ⟨by
      intro first second
      simpa [descending, or_comm] using (le_total first second)⟩
  haveI : Std.Antisymm descending :=
    ⟨by
      intro first second firstSecond secondFirst
      exact le_antisymm secondFirst firstSecond⟩
  have leftPermutation :=
    List.mergeSort_perm left (fun first second => decide (second ≤ first))
  have rightPermutation :=
    List.mergeSort_perm right (fun first second => decide (second ≤ first))
  have sortedPermutation :=
    leftPermutation.trans (permutation.trans rightPermutation.symm)
  have leftSorted :
      (left.mergeSort (fun first second => decide (second ≤ first))).Pairwise descending := by
    simpa [descending] using (List.pairwise_mergeSort' (r := descending) left)
  have rightSorted :
      (right.mergeSort (fun first second => decide (second ≤ first))).Pairwise descending := by
    simpa [descending] using (List.pairwise_mergeSort' (r := descending) right)
  exact List.Perm.eq_of_pairwise' leftSorted rightSorted sortedPermutation

/-- A permutation of a layer produces the same canonical sequence of unary node keys. -/
theorem sortOfficialLayer_keys_eq_of_perm (m : MoleculeGraph V)
    {left right : List (OfficialCIPNode V)} (permutation : left.Perm right) :
    (m.sortOfficialLayer left).map m.officialNodeSortKey =
      (m.sortOfficialLayer right).map m.officialNodeSortKey := by
  rw [m.map_officialNodeSortKey_sortOfficialLayer,
    m.map_officialNodeSortKey_sortOfficialLayer]
  apply sortOfficialNodeKeys_eq_of_perm
  exact permutation.map m.officialNodeSortKey

/-- Equal unary sort keys make a node interchangeable in the left position of a chemical trace.
The history-length field is deliberately stronger than needed: chemistry uses only the first three
fields, while the fourth canonically orders chemically tied occurrences. -/
theorem compareOfficialNodeTrace_eq_of_sortKey_eq_left (m : MoleculeGraph V)
    {left replacement right : OfficialCIPNode V}
    (keyEquality : m.officialNodeSortKey left = m.officialNodeSortKey replacement) :
    m.compareOfficialNodeTrace left right = m.compareOfficialNodeTrace replacement right := by
  have outer := congrArg ofLex keyEquality
  simp only [officialNodeSortKey, ofLex_toLex] at outer
  have atomicNumberEquality := congrArg Prod.fst outer
  have tail := congrArg Prod.snd outer
  have middle := congrArg ofLex tail
  simp only [ofLex_toLex] at middle
  have rootDistanceEquality := congrArg Prod.fst middle
  have massTail := congrArg Prod.snd middle
  have inner := congrArg ofLex massTail
  simp only [ofLex_toLex] at inner
  have massEquality := congrArg Prod.fst inner
  simp at atomicNumberEquality rootDistanceEquality massEquality
  simp only [compareOfficialNodeTrace, duplicateRootDistanceDecision]
  rw [atomicNumberEquality, rootDistanceEquality, massEquality]

/-- Equal unary sort keys make a node interchangeable in the right position of a chemical trace. -/
theorem compareOfficialNodeTrace_eq_of_sortKey_eq_right (m : MoleculeGraph V)
    {left right replacement : OfficialCIPNode V}
    (keyEquality : m.officialNodeSortKey right = m.officialNodeSortKey replacement) :
    m.compareOfficialNodeTrace left right = m.compareOfficialNodeTrace left replacement := by
  have outer := congrArg ofLex keyEquality
  simp only [officialNodeSortKey, ofLex_toLex] at outer
  have atomicNumberEquality := congrArg Prod.fst outer
  have tail := congrArg Prod.snd outer
  have middle := congrArg ofLex tail
  simp only [ofLex_toLex] at middle
  have rootDistanceEquality := congrArg Prod.fst middle
  have massTail := congrArg Prod.snd middle
  have inner := congrArg ofLex massTail
  simp only [ofLex_toLex] at inner
  have massEquality := congrArg Prod.fst inner
  simp at atomicNumberEquality rootDistanceEquality massEquality
  simp only [compareOfficialNodeTrace, duplicateRootDistanceDecision]
  rw [atomicNumberEquality, rootDistanceEquality, massEquality]

/-- Node-list comparison depends only on the corresponding unary sort-key sequences. -/
theorem compareOfficialNodeListTrace_eq_of_map_sortKey_eq (m : MoleculeGraph V) :
    ∀ {left replacementLeft right replacementRight : List (OfficialCIPNode V)},
      left.map m.officialNodeSortKey = replacementLeft.map m.officialNodeSortKey →
      right.map m.officialNodeSortKey = replacementRight.map m.officialNodeSortKey →
      m.compareOfficialNodeListTrace left right =
        m.compareOfficialNodeListTrace replacementLeft replacementRight
  | [], [], [], [], _, _ => rfl
  | [], [], [], _ :: _, _, rightEquality => by simp at rightEquality
  | [], [], _ :: _, [], _, rightEquality => by simp at rightEquality
  | [], [], _ :: _, _ :: _, _, _ => rfl
  | [], _ :: _, _, _, leftEquality, _ => by simp at leftEquality
  | _ :: _, [], _, _, leftEquality, _ => by simp at leftEquality
  | _ :: _, _ :: _, [], [], _, _ => rfl
  | _ :: _, _ :: _, [], _ :: _, _, rightEquality => by simp at rightEquality
  | _ :: _, _ :: _, _ :: _, [], _, rightEquality => by simp at rightEquality
  | leftNode :: lefts, replacementLeftNode :: replacementLefts,
      rightNode :: rights, replacementRightNode :: replacementRights,
      leftEquality, rightEquality => by
      simp only [List.map_cons, List.cons.injEq] at leftEquality rightEquality
      simp only [compareOfficialNodeListTrace]
      rw [m.compareOfficialNodeTrace_eq_of_sortKey_eq_left leftEquality.1,
        m.compareOfficialNodeTrace_eq_of_sortKey_eq_right rightEquality.1]
      rw [m.compareOfficialNodeListTrace_eq_of_map_sortKey_eq
        leftEquality.2 rightEquality.2]

/-- The complete rule trace for a breadth-first layer is invariant under arbitrary enumeration of
either input multiset. This is the formal regression theorem for the former Rule-1b sorting bug. -/
theorem compareOfficialLayerTrace_eq_of_perm (m : MoleculeGraph V)
    {left replacementLeft right replacementRight : List (OfficialCIPNode V)}
    (leftPermutation : left.Perm replacementLeft)
    (rightPermutation : right.Perm replacementRight) :
    m.compareOfficialLayerTrace left right =
      m.compareOfficialLayerTrace replacementLeft replacementRight := by
  unfold compareOfficialLayerTrace
  apply m.compareOfficialNodeListTrace_eq_of_map_sortKey_eq
  · exact m.sortOfficialLayer_keys_eq_of_perm leftPermutation
  · exact m.sortOfficialLayer_keys_eq_of_perm rightPermutation

/-- Every node-level observation ties against itself. -/
@[simp] theorem compareOfficialNodeTrace_self_outcome (m : MoleculeGraph V)
    (node : OfficialCIPNode V) :
    cipTraceOutcome (m.compareOfficialNodeTrace node node) = Ordering.eq := by
  simp [compareOfficialNodeTrace, CIPRuleEngine.priorityNatDecision,
    CIPRuleEngine.comparePriorityNat_self, duplicateRootDistanceDecision,
    compareCloserRootDistance]

/-- An already canonicalized node list ties against itself. -/
theorem compareOfficialNodeListTrace_self_outcome (m : MoleculeGraph V) :
    ∀ nodes, cipTraceOutcome (m.compareOfficialNodeListTrace nodes nodes) = Ordering.eq
  | [] => rfl
  | node :: nodes => by
      simp [compareOfficialNodeListTrace,
        cipTraceOutcome_append_of_left_eq (m.compareOfficialNodeTrace_self_outcome node),
        m.compareOfficialNodeListTrace_self_outcome nodes]

/-- Sorting the same layer on both sides preserves reflexive comparison. -/
@[simp] theorem compareOfficialLayerTrace_self_outcome (m : MoleculeGraph V)
    (nodes : List (OfficialCIPNode V)) :
    cipTraceOutcome (m.compareOfficialLayerTrace nodes nodes) = Ordering.eq := by
  exact m.compareOfficialNodeListTrace_self_outcome (m.sortOfficialLayer nodes)

/-- The complete fuelled hierarchical comparator is reflexive at every expansion depth. -/
@[simp] theorem compareOfficialHierarchicalDigraphTrace_self_outcome (m : MoleculeGraph V) :
    ∀ fuel nodes,
      cipTraceOutcome (m.compareOfficialHierarchicalDigraphTrace fuel nodes nodes) = Ordering.eq
  | 0, _nodes => rfl
  | fuel + 1, nodes => by
      rw [compareOfficialHierarchicalDigraphTrace]
      have layer := m.compareOfficialLayerTrace_self_outcome nodes
      simp [layer, cipTraceOutcome_append_of_left_eq layer,
        m.compareOfficialHierarchicalDigraphTrace_self_outcome fuel
          (m.officialCIPNextFrontier nodes)]

@[simp] theorem officialCIPChildren_of_duplicateLeaf (m : MoleculeGraph V)
    {node : OfficialCIPNode V} (h : node.isDuplicateLeaf = true) :
    m.officialCIPChildren node = [] := by
  simp [officialCIPChildren, h]

@[simp] theorem officialCIPChildren_placeholder (m : MoleculeGraph V)
    (kind : OfficialPhantomNodeKind) (rootDistance : ℕ) :
    m.officialCIPChildren (OfficialCIPNode.placeholder (V := V) kind rootDistance) = [] := by
  rfl

theorem officialCIPChild_history_length (m : MoleculeGraph V)
    {node child : OfficialCIPNode V} (hchild : child ∈ m.officialCIPChildren node) :
    child.history.length = node.history.length + 1 := by
  by_cases hdup : node.isDuplicateLeaf = true
  · simp [officialCIPChildren, hdup] at hchild
  · simp [officialCIPChildren, hdup] at hchild
    rcases hchild with ⟨next, copyIndex, _hcopy, rfl⟩
    simp

theorem activeSimple_of_mem_officialCIPChildren_of_not_duplicateLeaf
    (m : MoleculeGraph V) {node child : OfficialCIPNode V}
    (hnode : node.ActiveSimple) (hchild : child ∈ m.officialCIPChildren node)
    (hchildNondup : child.isDuplicateLeaf = false) :
    child.ActiveSimple := by
  rcases hnode with ⟨hnodeProvenance, hnodeNodup⟩
  have hnodeNondup : node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, hnodeProvenance]
  simp [officialCIPChildren, hnodeNondup] at hchild
  rcases hchild with ⟨next, copyIndex, _hcopy, rfl⟩
  have hnextNotMem : next ∉ node.history := by
    intro hmem
    cases copyIndex with
    | zero =>
        simp [OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.childProvenance, hmem] at hchildNondup
    | succ copyIndex =>
        simp [OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.childProvenance] at hchildNondup
  constructor
  · cases copyIndex with
    | zero =>
        simp [OfficialCIPNode.childProvenance, hnextNotMem]
    | succ copyIndex =>
        exfalso
        simp [OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.childProvenance] at hchildNondup
  · simp [hnextNotMem, hnodeNodup]

@[simp] theorem officialCIPFrontier_zero (m : MoleculeGraph V)
    (frontier : List (OfficialCIPNode V)) :
    m.officialCIPFrontier 0 frontier = frontier :=
  rfl

theorem officialCIPFrontier_add (m : MoleculeGraph V) (fuel extra : ℕ)
    (frontier : List (OfficialCIPNode V)) :
    m.officialCIPFrontier (fuel + extra) frontier =
      m.officialCIPFrontier fuel (m.officialCIPFrontier extra frontier) := by
  induction extra generalizing frontier with
  | zero =>
      simp [officialCIPFrontier]
  | succ extra ih =>
      rw [show fuel + (extra + 1) = (fuel + extra) + 1 by omega]
      change m.officialCIPFrontier (fuel + extra) (m.officialCIPNextFrontier frontier) =
        m.officialCIPFrontier fuel (m.officialCIPFrontier (extra + 1) frontier)
      rw [ih (m.officialCIPNextFrontier frontier)]
      rfl

@[simp] theorem officialCIPNextFrontier_nil (m : MoleculeGraph V) :
    m.officialCIPNextFrontier ([] : List (OfficialCIPNode V)) = [] := by
  simp [officialCIPNextFrontier]

theorem officialTerminalFrontier_nil (m : MoleculeGraph V) :
    m.OfficialTerminalFrontier ([] : List (OfficialCIPNode V)) := by
  intro node hnode
  simp at hnode

theorem officialFrontierActiveSimple_nil (m : MoleculeGraph V) :
    m.OfficialFrontierActiveSimple ([] : List (OfficialCIPNode V)) := by
  intro node hnode _hnondup
  simp at hnode

theorem officialFrontierActiveSimple_singleton_rootFromEdge (m : MoleculeGraph V)
    {center ligand : V} (hligand : ligand ≠ center) :
    m.OfficialFrontierActiveSimple [OfficialCIPNode.rootFromEdge center ligand] := by
  intro node hnode _hnondup
  simp at hnode
  subst node
  exact OfficialCIPNode.activeSimple_rootFromEdge hligand

theorem officialFrontierActiveSimple_officialCIPNextFrontier (m : MoleculeGraph V)
    {frontier : List (OfficialCIPNode V)}
    (hfront : m.OfficialFrontierActiveSimple frontier) :
    m.OfficialFrontierActiveSimple (m.officialCIPNextFrontier frontier) := by
  intro child hchild hchildNondup
  rcases (List.mem_flatMap).1 (by simpa [officialCIPNextFrontier] using hchild) with
    ⟨node, hnode, hchildNode⟩
  have hnodeNondup : node.isDuplicateLeaf = false := by
    by_cases hdup : node.isDuplicateLeaf = true
    · have hchildren : m.officialCIPChildren node = [] :=
        m.officialCIPChildren_of_duplicateLeaf hdup
      simp [hchildren] at hchildNode
    · exact Bool.eq_false_iff.mpr hdup
  exact m.activeSimple_of_mem_officialCIPChildren_of_not_duplicateLeaf
    (hfront node hnode hnodeNondup) hchildNode hchildNondup

theorem officialFrontierActiveSimple_officialCIPFrontier (m : MoleculeGraph V) :
    ∀ fuel {frontier : List (OfficialCIPNode V)},
      m.OfficialFrontierActiveSimple frontier →
        m.OfficialFrontierActiveSimple (m.officialCIPFrontier fuel frontier)
  | 0, frontier, hfront => by
      simpa [officialCIPFrontier] using hfront
  | fuel + 1, frontier, hfront => by
      simpa [officialCIPFrontier] using
        m.officialFrontierActiveSimple_officialCIPFrontier fuel
          (m.officialFrontierActiveSimple_officialCIPNextFrontier hfront)

theorem officialCIPFrontier_history_length (m : MoleculeGraph V) :
    ∀ fuel {frontier : List (OfficialCIPNode V)} {node : OfficialCIPNode V},
      node ∈ m.officialCIPFrontier fuel frontier →
        ∃ root, root ∈ frontier ∧ node.history.length = root.history.length + fuel
  | 0, frontier, node, hnode => by
      exact ⟨node, by simpa [officialCIPFrontier] using hnode, by simp⟩
  | fuel + 1, frontier, node, hnode => by
      have hnodeNext :
          node ∈ m.officialCIPFrontier fuel (m.officialCIPNextFrontier frontier) := by
        simpa [officialCIPFrontier] using hnode
      rcases m.officialCIPFrontier_history_length fuel hnodeNext with
        ⟨childRoot, hchildRoot, hnodeLength⟩
      rcases (List.mem_flatMap).1 (by simpa [officialCIPNextFrontier] using hchildRoot) with
        ⟨root, hroot, hchildRootNode⟩
      have hchildRootLength := m.officialCIPChild_history_length hchildRootNode
      refine ⟨root, hroot, ?_⟩
      omega

theorem officialCIPFrontier_only_duplicateLeaves_of_activeSimple_length_bound
    (m : MoleculeGraph V) {fuel : ℕ} {frontier : List (OfficialCIPNode V)}
    (hfront : m.OfficialFrontierActiveSimple frontier)
    (hlen : ∀ root, root ∈ frontier → Fintype.card V < root.history.length + fuel) :
    ∀ node, node ∈ m.officialCIPFrontier fuel frontier → node.isDuplicateLeaf = true := by
  intro node hnode
  by_cases hdup : node.isDuplicateLeaf = true
  · exact hdup
  · have hnodeNondup : node.isDuplicateLeaf = false := Bool.eq_false_iff.mpr hdup
    have hfrontierSimple :=
      m.officialFrontierActiveSimple_officialCIPFrontier fuel hfront
    rcases hfrontierSimple node hnode hnodeNondup with ⟨_hprovenance, hnodup⟩
    have hlengthLe : node.history.length ≤ Fintype.card V := hnodup.length_le_card
    rcases m.officialCIPFrontier_history_length fuel hnode with
      ⟨root, hroot, hnodeLength⟩
    have hlengthGt : Fintype.card V < node.history.length := by
      have hrootLength := hlen root hroot
      omega
    omega

theorem officialCIPNextFrontier_eq_nil_of_terminalFrontier (m : MoleculeGraph V)
    {frontier : List (OfficialCIPNode V)} (hfront : m.OfficialTerminalFrontier frontier) :
    m.officialCIPNextFrontier frontier = [] := by
  induction frontier with
  | nil =>
      simp
  | cons node nodes ih =>
      have hnode : m.officialCIPChildren node = [] := hfront node (by simp)
      have htail : m.OfficialTerminalFrontier nodes := by
        intro tailNode htailNode
        exact hfront tailNode (List.mem_cons_of_mem node htailNode)
      change m.officialCIPChildren node ++ m.officialCIPNextFrontier nodes = []
      rw [hnode, ih htail]
      rfl

theorem officialTerminalFrontier_of_duplicateLeaves (m : MoleculeGraph V)
    {frontier : List (OfficialCIPNode V)}
    (hdup : ∀ node, node ∈ frontier → node.isDuplicateLeaf = true) :
    m.OfficialTerminalFrontier frontier := by
  intro node hnode
  exact m.officialCIPChildren_of_duplicateLeaf (hdup node hnode)

@[simp] theorem officialCIPFrontier_nil (m : MoleculeGraph V) :
    ∀ fuel, m.officialCIPFrontier fuel ([] : List (OfficialCIPNode V)) = []
  | 0 => rfl
  | fuel + 1 => by
      simp [officialCIPFrontier, officialCIPFrontier_nil m fuel]

theorem officialCIPFrontier_eq_nil_of_terminalFrontier (m : MoleculeGraph V)
    {frontier : List (OfficialCIPNode V)} (hfront : m.OfficialTerminalFrontier frontier) :
    ∀ extra, m.officialCIPFrontier (extra + 1) frontier = []
  | 0 => by
      simp [officialCIPFrontier, m.officialCIPNextFrontier_eq_nil_of_terminalFrontier hfront]
  | extra + 1 => by
      simp [officialCIPFrontier, m.officialCIPNextFrontier_eq_nil_of_terminalFrontier hfront]

theorem officialCIPFrontier_terminal_of_activeSimple_length_bound
    (m : MoleculeGraph V) {fuel : ℕ} {frontier : List (OfficialCIPNode V)}
    (hfront : m.OfficialFrontierActiveSimple frontier)
    (hlen : ∀ root, root ∈ frontier → Fintype.card V < root.history.length + fuel) :
    m.OfficialTerminalFrontier (m.officialCIPFrontier fuel frontier) := by
  exact m.officialTerminalFrontier_of_duplicateLeaves
    (m.officialCIPFrontier_only_duplicateLeaves_of_activeSimple_length_bound hfront hlen)

theorem officialCIPFrontier_eq_nil_of_activeSimple_length_bound
    (m : MoleculeGraph V) {fuel : ℕ} {frontier : List (OfficialCIPNode V)}
    (hfront : m.OfficialFrontierActiveSimple frontier)
    (hlen : ∀ root, root ∈ frontier → Fintype.card V < root.history.length + fuel) :
    m.officialCIPFrontier (fuel + 1) frontier = [] := by
  have hterminal :
      m.OfficialTerminalFrontier (m.officialCIPFrontier fuel frontier) :=
    m.officialCIPFrontier_terminal_of_activeSimple_length_bound hfront hlen
  have hempty : m.officialCIPFrontier 1 (m.officialCIPFrontier fuel frontier) = [] := by
    simpa using m.officialCIPFrontier_eq_nil_of_terminalFrontier hterminal 0
  rw [show fuel + 1 = 1 + fuel by omega]
  simpa [m.officialCIPFrontier_add 1 fuel frontier] using hempty

theorem officialCIPFrontier_rootFromEdge_eq_nil_card_add_one (m : MoleculeGraph V)
    {center ligand : V} (hligand : ligand ≠ center) :
    m.officialCIPFrontier (Fintype.card V + 1)
      [OfficialCIPNode.rootFromEdge center ligand] = [] := by
  exact m.officialCIPFrontier_eq_nil_of_activeSimple_length_bound
    (m.officialFrontierActiveSimple_singleton_rootFromEdge hligand)
    (by
      intro root hroot
      simp at hroot
      subst root
      simp [OfficialCIPNode.rootFromEdge])

@[simp] theorem compareOfficialLayerTrace_nil_nil (m : MoleculeGraph V) :
    m.compareOfficialLayerTrace ([] : List (OfficialCIPNode V)) [] = [] := by
  simp [compareOfficialLayerTrace, compareOfficialNodeListTrace, sortOfficialLayer]

@[simp] theorem compareOfficialHierarchicalDigraphTrace_one (m : MoleculeGraph V)
    (left right : List (OfficialCIPNode V)) :
    m.compareOfficialHierarchicalDigraphTrace 1 left right =
      m.compareOfficialLayerTrace left right := by
  by_cases houtcome : cipTraceOutcome (m.compareOfficialLayerTrace left right) = Ordering.eq
  · simp [compareOfficialHierarchicalDigraphTrace, houtcome]
  · simp [compareOfficialHierarchicalDigraphTrace, houtcome]

@[simp] theorem compareOfficialHierarchicalDigraphTrace_nil_nil (m : MoleculeGraph V) :
    ∀ fuel, m.compareOfficialHierarchicalDigraphTrace fuel
      ([] : List (OfficialCIPNode V)) [] = []
  | 0 => rfl
  | fuel + 1 => by
      simp [compareOfficialHierarchicalDigraphTrace,
        compareOfficialHierarchicalDigraphTrace_nil_nil m fuel]

/-- Once both official hierarchical-digraph frontiers are empty at depth `fuel`, adding more fuel
cannot change the comparison trace.  This is the first stabilization theorem for the official
digraph comparator: finite fuel is harmless after both breadth-first expansions have exhausted. -/
theorem compareOfficialHierarchicalDigraphTrace_eq_of_frontiers_nil
    (m : MoleculeGraph V) :
    ∀ fuel {left right : List (OfficialCIPNode V)},
      m.officialCIPFrontier fuel left = [] →
      m.officialCIPFrontier fuel right = [] →
      ∀ extra,
        m.compareOfficialHierarchicalDigraphTrace (fuel + extra) left right =
          m.compareOfficialHierarchicalDigraphTrace fuel left right
  | 0, left, right, hleft, hright, extra => by
      have hleft' : left = [] := by
        simpa [officialCIPFrontier] using hleft
      have hright' : right = [] := by
        simpa [officialCIPFrontier] using hright
      subst left
      subst right
      simp [compareOfficialHierarchicalDigraphTrace_nil_nil]
  | fuel + 1, left, right, hleft, hright, extra => by
      have hleftNext :
          m.officialCIPFrontier fuel (m.officialCIPNextFrontier left) = [] := by
        simpa [officialCIPFrontier] using hleft
      have hrightNext :
          m.officialCIPFrontier fuel (m.officialCIPNextFrontier right) = [] := by
        simpa [officialCIPFrontier] using hright
      cases extra with
      | zero =>
          simp
      | succ extra =>
          have htail :=
            compareOfficialHierarchicalDigraphTrace_eq_of_frontiers_nil
              (m := m) fuel hleftNext hrightNext (extra + 1)
          rw [show (fuel + 1) + (extra + 1) = (fuel + (extra + 1)) + 1 by omega]
          rw [show fuel + 1 = Nat.succ fuel by omega]
          by_cases houtcome :
              cipTraceOutcome (m.compareOfficialLayerTrace left right) = Ordering.eq
          · conv_lhs => rw [compareOfficialHierarchicalDigraphTrace]
            conv_rhs => rw [compareOfficialHierarchicalDigraphTrace]
            simp [houtcome, htail]
          · conv_lhs => rw [compareOfficialHierarchicalDigraphTrace]
            conv_rhs => rw [compareOfficialHierarchicalDigraphTrace]
            simp [houtcome]

/-- Outcome-level version of official hierarchical-digraph stabilization. -/
theorem compareOfficialHierarchicalDigraphTrace_outcome_eq_of_frontiers_nil
    (m : MoleculeGraph V) {fuel : ℕ} {left right : List (OfficialCIPNode V)}
    (hleft : m.officialCIPFrontier fuel left = [])
    (hright : m.officialCIPFrontier fuel right = []) (extra : ℕ) :
    cipTraceOutcome (m.compareOfficialHierarchicalDigraphTrace (fuel + extra) left right) =
      cipTraceOutcome (m.compareOfficialHierarchicalDigraphTrace fuel left right) := by
  rw [m.compareOfficialHierarchicalDigraphTrace_eq_of_frontiers_nil fuel hleft hright extra]

/-- Terminal-frontier version of stabilization: once the current layer has no expandable children
on either side, all additional fuel leaves the trace equal to the current layer comparison. -/
theorem compareOfficialHierarchicalDigraphTrace_eq_layer_of_terminalFrontiers
    (m : MoleculeGraph V) {left right : List (OfficialCIPNode V)}
    (hleft : m.OfficialTerminalFrontier left) (hright : m.OfficialTerminalFrontier right)
    (extra : ℕ) :
    m.compareOfficialHierarchicalDigraphTrace (1 + extra) left right =
      m.compareOfficialLayerTrace left right := by
  have hleftEmpty : m.officialCIPFrontier 1 left = [] := by
    simpa using m.officialCIPFrontier_eq_nil_of_terminalFrontier hleft 0
  have hrightEmpty : m.officialCIPFrontier 1 right = [] := by
    simpa using m.officialCIPFrontier_eq_nil_of_terminalFrontier hright 0
  rw [m.compareOfficialHierarchicalDigraphTrace_eq_of_frontiers_nil 1 hleftEmpty hrightEmpty extra]
  simp

/-- Outcome-level terminal-frontier stabilization. -/
theorem compareOfficialHierarchicalDigraphTrace_outcome_eq_layer_of_terminalFrontiers
    (m : MoleculeGraph V) {left right : List (OfficialCIPNode V)}
    (hleft : m.OfficialTerminalFrontier left) (hright : m.OfficialTerminalFrontier right)
    (extra : ℕ) :
    cipTraceOutcome (m.compareOfficialHierarchicalDigraphTrace (1 + extra) left right) =
      cipTraceOutcome (m.compareOfficialLayerTrace left right) := by
  rw [m.compareOfficialHierarchicalDigraphTrace_eq_layer_of_terminalFrontiers hleft hright extra]

/-- For ordinary ligand-root branches, the default `Fintype.card V + 1` fuel is already stable:
all later fuel values produce the same official hierarchical-digraph trace. -/
theorem compareOfficialHierarchicalDigraphTrace_rootFromEdge_stable_default
    (m : MoleculeGraph V) {center left right : V}
    (hleft : left ≠ center) (hright : right ≠ center) (extra : ℕ) :
    m.compareOfficialHierarchicalDigraphTrace ((Fintype.card V + 1) + extra)
      [OfficialCIPNode.rootFromEdge center left] [OfficialCIPNode.rootFromEdge center right] =
        m.compareOfficialHierarchicalDigraphTrace (Fintype.card V + 1)
          [OfficialCIPNode.rootFromEdge center left]
          [OfficialCIPNode.rootFromEdge center right] := by
  have hleftEmpty :
      m.officialCIPFrontier (Fintype.card V + 1)
        [OfficialCIPNode.rootFromEdge center left] = [] :=
    m.officialCIPFrontier_rootFromEdge_eq_nil_card_add_one hleft
  have hrightEmpty :
      m.officialCIPFrontier (Fintype.card V + 1)
        [OfficialCIPNode.rootFromEdge center right] = [] :=
    m.officialCIPFrontier_rootFromEdge_eq_nil_card_add_one hright
  exact m.compareOfficialHierarchicalDigraphTrace_eq_of_frontiers_nil
    (Fintype.card V + 1) hleftEmpty hrightEmpty extra

/-- Outcome-level default-fuel stability for ordinary ligand-root official digraph branches. -/
theorem compareOfficialHierarchicalDigraphTrace_outcome_rootFromEdge_stable_default
    (m : MoleculeGraph V) {center left right : V}
    (hleft : left ≠ center) (hright : right ≠ center) (extra : ℕ) :
    cipTraceOutcome
      (m.compareOfficialHierarchicalDigraphTrace ((Fintype.card V + 1) + extra)
        [OfficialCIPNode.rootFromEdge center left] [OfficialCIPNode.rootFromEdge center right]) =
      cipTraceOutcome
        (m.compareOfficialHierarchicalDigraphTrace (Fintype.card V + 1)
          [OfficialCIPNode.rootFromEdge center left]
          [OfficialCIPNode.rootFromEdge center right]) := by
  rw [m.compareOfficialHierarchicalDigraphTrace_rootFromEdge_stable_default hleft hright extra]

@[simp] theorem compareOfficialHierarchicalDigraphCertificate_outcome
    (m : MoleculeGraph V) (fuel : ℕ)
    (left right : List (OfficialCIPNode V)) :
    (m.compareOfficialHierarchicalDigraphCertificate fuel left right).outcome =
      cipTraceOutcome (m.compareOfficialHierarchicalDigraphTrace fuel left right) :=
  rfl

@[simp] theorem compareOfficialHierarchicalDigraphThenContextFrom_outcome
    (m : MoleculeGraph V) (fuel : ℕ) (center left right : V)
    (leftContext rightContext : CIPRuleEngine.OfficialLigandRuleContext) :
    (m.compareOfficialHierarchicalDigraphThenContextFrom fuel center left right
      leftContext rightContext).outcome =
      cipTraceOutcome
        (CIPRuleEngine.compareDigraphThenOfficialTrace
          (m.compareOfficialHierarchicalDigraphTrace fuel
            [OfficialCIPNode.rootFromEdge center left] [OfficialCIPNode.rootFromEdge center right])
          leftContext rightContext) :=
  rfl

end MoleculeGraph

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Official hierarchical-digraph descriptor comparison for two ligands. -/
noncomputable def cipOfficialHierarchicalDigraphCompare (m : OneCenterMolecule V) (fuel : ℕ)
    (i j : Fin 4) : CIPTraceCertificate :=
  m.mol.compareOfficialHierarchicalDigraphFrom fuel m.center (m.ligandAtom i) (m.ligandAtom j)

/-- Default official hierarchical-digraph descriptor comparison. -/
noncomputable def cipOfficialHierarchicalDigraphCompareDefault (m : OneCenterMolecule V)
    (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialHierarchicalDigraphCompare (Fintype.card V + 1) i j

/-- Official hierarchical-digraph comparison followed by official Rule 3/4/5 context fallthrough. -/
noncomputable def cipOfficialHierarchicalDigraphCompareWithContext (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (fuel : ℕ)
    (i j : Fin 4) : CIPTraceCertificate :=
  m.mol.compareOfficialHierarchicalDigraphThenContextFrom fuel m.center
    (m.ligandAtom i) (m.ligandAtom j) (context i) (context j)

/-- Default official hierarchical-digraph-plus-context comparison. -/
noncomputable def cipOfficialHierarchicalDigraphCompareWithContextDefault (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialHierarchicalDigraphCompareWithContext context (Fintype.card V + 1) i j

end OneCenterMolecule

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Official hierarchical-digraph comparison at a distinguished center with context fallthrough. -/
noncomputable def cipOfficialHierarchicalDigraphCompareAtWithContext (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (fuel : ℕ)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  (m.toOneCenterMolecule center).cipOfficialHierarchicalDigraphCompareWithContext
    (context center) fuel i j

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
