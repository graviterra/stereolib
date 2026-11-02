import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456
import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Generic retained-occurrence recalculation with input-generated references and schedule

**Experimental constructor.** This module removes the prescribed cage marks, visits and two-layer
schedule of the accepted hidden-parity pipeline. Every quantity below is generated from the
molecular input by existing runtime calls:

* occurrences and their four-ligand frames: `occurrenceLigandFrame?` on the canonical expansion
  `canonicalChildren` of the actual `RawMolecule` graph;
* the ordinary Rules 1–5 order and its tied runs: the production fail-closed initial sort
  `sortRule6InitialPositions?` and the adjacent decisions `compareRule6InitialAdjacent?`;
* eligible references: the frame atoms lying in a tied run of length at least two
  (`tiedPositions`); the production Rule-6 selectors `rule6EquivalentReferencePositions`
  (two groups) and `sorted[1]` with the local-reference gate (three groups) are *not* reused, see
  the report for the exact differences;
* the evaluation schedule: the canonical children in tied positions, descended through
  non-framed nodes to the framed occurrences of their subtrees (`facts`), bounded by the finite
  history structure (`facts_stable`);
* the marked ranking: the existing `rankOccurrencePositionsThroughRule6Tracked?` at the reference
  position of the chosen atom;
* raw letters: geometry readback of the returned priority order
  (`descriptorOfPriorityOrderedPoints?`) from an atom-indexed coordinate function;
* case: recomputation from the same input state on reflected coordinates (`caseFromMirror?`), the
  reflection criterion of Blue Book P-91.2.1.1 / Hanson et al. 2018 p. 1761.

No atom identifier, graph, joint-sign formula, precomputed letter or caller-supplied winning
reference list occurs in the definitions. Nothing here changes production defaults or the
ordinary generated state; no chemical sanction of promotion-indexed recalculation is claimed.

## Scope of a promoted reference (explicit semantic choice)

A reference chosen at an occurrence is *carried* to a descendant occurrence exactly when that
atom is one of the descendant's frame atoms (`List.contains`); the descendant then uses it as its
single reference and no own context is opened. When the carried atom is not in the descendant's
frame, the descendant opens its own promotion context with its own tied references and requires
a consensus over all of them (`consensus`), mirroring the production topology-invariance
discipline of `rankOccurrenceEquivalentReferences?`. A single globally carried marker would
*not* reproduce the accepted candidate: the accepted near marks are selected at the near
occurrence's own tied class, and the root marks never occur in a near frame. The cage module
exhibits both behaviours on actual calls.

Internally generated facts of different promotion contexts never share a state: `facts` under reference `r`
is appended (`appendFacts?`, duplicate keys refused) to the input state only for the evaluation
under `r`. Generated facts flow upward only; arbitrary caller-supplied states are not validated.
The public `assign` endpoint starts from the empty state. For a nonempty supplied state, reflection
holds its labels fixed and therefore does not model full reflection of that molecular state.
-/

namespace TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

/-! ## Geometry -/

/-- Atom-indexed coordinates: the certified point of a runtime atom identifier, if any. -/
abbrev Geometry := Nat → Option CartesianPoint3

/-- Pointwise spatial reflection of a geometry. -/
def mirror (geom : Geometry) : Geometry := fun atom => (geom atom).map CartesianPoint3.reflectX

/-- Raw letter of atoms in descending priority order from their coordinates. -/
def readback? (geom : Geometry) (atoms : List Nat) : Option RS := do
  let points ← atoms.mapM geom
  descriptorOfPriorityOrderedPoints? points

theorem mapM_mirror (geom : Geometry) (atoms : List Nat) :
    atoms.mapM (mirror geom) = (atoms.mapM geom).map (List.map CartesianPoint3.reflectX) := by
  induction atoms with
  | nil => rfl
  | cons atom tail ih =>
      simp only [List.mapM_cons, mirror, ih]
      cases geom atom <;> cases tail.mapM geom <;> rfl

/-- A raw letter read on the reflected geometry is the complement. -/
theorem readback_mirror (geom : Geometry) (atoms : List Nat) :
    readback? (mirror geom) atoms = (readback? geom atoms).map RS.swap := by
  unfold readback?
  rw [mapM_mirror]
  cases atoms.mapM geom with
  | none => rfl
  | some points =>
      simpa using descriptorOfPriorityOrderedPoints?_reflectX points

/-! ## Frames, ordinary order and tied runs from actual runtime calls -/

/-- Frame atom identifiers in frame order. -/
def frameAtomsOf (roots : List CanonicalRerootCursor) : List Nat :=
  roots.map fun cursor => cursor.node.atom

/-- Frame atoms of an occurrence, if it has a four-ligand frame. -/
def frameAtoms? (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) :
    Option (List Nat) :=
  (occurrenceLigandFrame? mol node).map frameAtomsOf

/-- Production Rules 1–5 initial order (positions in descending priority) together with the
actual adjacent decisions, through the fail-closed sort used before Rule 6. -/
def ordinary? (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option (List Nat × List (Option Ordering)) := do
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← sortRule6InitialPositions? (mol := mol) state fuel roots (List.range roots.length)
  let adjacent ← compareRule6InitialAdjacent? (mol := mol) state fuel roots sorted
  some (sorted, adjacent)

/-- Every adjacent decision is a strict `gt`. -/
def strict (adjacent : List (Option Ordering)) : Bool :=
  adjacent.all fun decision => decision == some Ordering.gt

/-- Every adjacent decision is `gt` or `eq`; an inverted or missing decision is malformed. -/
def consistent (adjacent : List (Option Ordering)) : Bool :=
  adjacent.all fun decision => decision == some Ordering.gt || decision == some Ordering.eq

/-- Positions (in sorted order) that lie in a tied run of length at least two. The Boolean
records whether the previous adjacent decision was a tie. -/
def tiedPositions : Bool → List Nat → List (Option Ordering) → List Nat
  | _, [], _ => []
  | prev, [p], _ => if prev then [p] else []
  | prev, p :: q :: rest, [] =>
      (if prev then [p] else []) ++ tiedPositions false (q :: rest) []
  | prev, p :: q :: rest, d :: ds =>
      let tie := d == some Ordering.eq
      (if prev || tie then [p] else []) ++ tiedPositions tie (q :: rest) ds

/-- Frame atoms at positions. -/
def atomsAt (atoms : List Nat) (positions : List Nat) : List Nat :=
  positions.filterMap fun position => atoms[position]?

/-- Frame atoms at positions, refusing an out-of-range position. -/
def atomsAt? (atoms : List Nat) (positions : List Nat) : Option (List Nat) :=
  positions.mapM fun position => atoms[position]?

/-- Eligible references of an occurrence: its frame atoms in tied runs. -/
def eligibleOf (atoms sorted : List Nat) (adjacent : List (Option Ordering)) : List Nat :=
  atomsAt atoms (tiedPositions false sorted adjacent)

/-! ## The existing marked ranking and its geometry readback -/

/-- The existing tracked Rule-6 ranking with the reference at the position of `mark`. -/
def marked? (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (mark : Nat) : Option Rule6TrackedRanking := do
  let roots ← occurrenceLigandFrame? mol node
  let ligands := roots.map fun cursor => cursor.node.atom
  let referencePosition := ligands.idxOf mark
  if referencePosition >= ligands.length then none else
    rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots ligands [0, 1, 2, 3]
      referencePosition

/-- Frame atoms in returned priority order of a strict ranking. -/
def rankedAtoms? (atoms : List Nat) (ranking : Rule6TrackedRanking) : Option (List Nat) :=
  if ranking.unique then ranking.positions.mapM fun position => atoms[position]? else none

/-- Raw letter of the marked ranking under a state. -/
def markedReadback? (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    Option RS := do
  let atoms ← frameAtoms? mol node
  let ranking ← marked? mol fuel state node mark
  let ranked ← rankedAtoms? atoms ranking
  readback? geom ranked

/-! ## Consensus, duplicate-free state extension and the mirror case -/

/-- Common value of a non-empty list of results; refused if any is missing or they differ. -/
def consensus : List (Option RS) → Option RS
  | [] => none
  | [result] => result
  | result :: rest =>
      match result, consensus rest with
      | some a, some b => if a = b then some a else none
      | _, _ => none

/-- Append facts one by one, refusing a repeated occurrence key (`appendInputFact?`). -/
def appendFacts? : OccurrenceAuxState → List OccurrenceAuxFact → Option OccurrenceAuxState
  | state, [] => some state
  | state, fact :: facts => do
      let next ← appendInputFact? state fact
      appendFacts? next facts

/-- Case from the mirror test: both computations must succeed; an unchanged raw letter is
lowercase, a complemented raw letter is uppercase. -/
def caseFromMirror? (original reflected : Option RS) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let a ← original
  let b ← reflected
  some (if b = a then .pseudoasymmetric (pseudoRSOfRS a) else .chiral a)

/-- Temporary fact at the exact occurrence key of a real node. -/
def factOf (node : RawMolecule.CanonicalBranchNode) :
    LocalizedTetrahedralRSPseudoDescriptor → OccurrenceAuxFact
  | .chiral raw =>
      { key := canonicalOccurrenceKey node, atom := node.atom, descriptor := raw,
        uppercase := true }
  | .pseudoasymmetric .r =>
      { key := canonicalOccurrenceKey node, atom := node.atom, descriptor := RS.R,
        uppercase := false }
  | .pseudoasymmetric .s =>
      { key := canonicalOccurrenceKey node, atom := node.atom, descriptor := RS.S,
        uppercase := false }

/-! ## One occurrence evaluation -/

/-- Children of an occurrence standing in tied positions of its ordinary order. -/
def tiedChildren (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : List RawMolecule.CanonicalBranchNode :=
  match frameAtoms? mol node, ordinary? mol fuel state node with
  | some atoms, some (sorted, adjacent) =>
      let eligible := eligibleOf atoms sorted adjacent
      (mol.canonicalChildren node).filter fun child => eligible.contains child.atom
  | _, _ => []

/-- Evaluate one occurrence given, for each reference `r`, the temporary facts `under r` that its
tied children contribute under `r`.

* ordinary strict order with the input state: its readback (ordinary success is preserved);
* otherwise, in a carried context whose atom is in the frame: the marked readback under that
  reference with `state ++ under r`;
* otherwise: the consensus of the marked readbacks over all eligible references. -/
def rawStep? (mol : RawMolecule) (fuel : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (under : Nat → OccurrenceAuxState) : Option RS := do
  let atoms ← frameAtoms? mol node
  let (sorted, adjacent) ← ordinary? mol fuel state node
  if ¬ atoms.Nodup ∨ consistent adjacent = false then none
  else if strict adjacent then
    let ranked ← atomsAt? atoms sorted
    readback? geom ranked
  else
    let eligible := eligibleOf atoms sorted adjacent
    let evaluate := fun (r : Nat) => do
      let temp ← appendFacts? state (under r)
      markedReadback? mol fuel geom temp node r
    match ctx with
    | some r => if atoms.contains r then evaluate r else consensus (eligible.map evaluate)
    | none => consensus (eligible.map evaluate)

/-- Contribution of the tied children under one reference through a continuation `sub`. -/
def underWith (mol : RawMolecule) (fuel : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState) (r : Nat) : OccurrenceAuxState :=
  (tiedChildren mol fuel state node).flatMap (sub geom state (some r))

def rawWith? (mol : RawMolecule) (fuel : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState) : Option RS :=
  rawStep? mol fuel geom state ctx node (underWith mol fuel geom state node sub)

/-- Cased descriptor by recomputing generated descendants on reflected geometry, with the same
supplied state held fixed. Full molecular reflection of nonempty supplied states needs a separate
state-transport contract; the public endpoint uses the empty state. -/
def descriptorWith? (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  caseFromMirror? (rawWith? mol fuel geom state ctx node sub)
    (rawWith? mol fuel (mirror geom) state ctx node sub)

/-! ## The terminating subtree recursion -/

/-- Facts contributed by the subtree at `node` to its parent's temporary state, with structural
depth `depth`: at every framed occurrence the mirror-cased descriptor fact; descent continues
through non-framed nodes and below framed ones. Exhausted depth contributes nothing;
`facts_stable` shows sufficient depth loses no contributing real occurrence; a forced leaf may
reach depth zero harmlessly. -/
def facts (mol : RawMolecule) (fuel : Nat) :
    Nat → Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState
  | 0, _, _, _, _ => []
  | depth + 1, geom, state, ctx, node =>
      (descriptorWith? mol fuel geom state ctx node (facts mol fuel depth)).toList.map
          (factOf node) ++
        (mol.canonicalChildren node).flatMap (facts mol fuel depth geom state ctx)

/-- Raw letter of an occurrence whose descendants are evaluated with depth `depth`. -/
def raw? (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) : Option RS :=
  rawWith? mol fuel geom state ctx node (facts mol fuel depth)

/-- Cased descriptor of an occurrence whose descendants are evaluated with depth `depth`. -/
def descriptor? (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorWith? mol fuel geom state ctx node (facts mol fuel depth)

theorem facts_zero (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    facts mol fuel 0 geom state ctx node = [] := rfl

theorem facts_succ (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode) :
    facts mol fuel (depth + 1) geom state ctx node =
      (descriptor? mol fuel depth geom state ctx node).toList.map (factOf node) ++
        (mol.canonicalChildren node).flatMap (facts mol fuel depth geom state ctx) := rfl

/-- Structural depth: a real occurrence history is duplicate-free and in range, so no descendant
chain is longer than the atom count. -/
def structuralDepth (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) : Nat :=
  mol.atomCount + 1 - node.history.length

/-- Comparator fuel of the existing runtime calls, from the atom count. -/
def comparatorFuel (mol : RawMolecule) : Nat := mol.atomCount + 1

/-- Descriptor of a center from the molecular input, an atom-indexed geometry and the empty input
state: generated frames, references and schedule only. -/
def assignCenter? (mol : RawMolecule) (fuel : Nat) (geom : Geometry) (center : Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  let root := canonicalCenterRoot center
  descriptor? mol fuel (structuralDepth mol root) geom [] none root

/-- All centers of the input with a generated descriptor. -/
def assign (mol : RawMolecule) (geom : Geometry) :
    List (Nat × LocalizedTetrahedralRSPseudoDescriptor) :=
  (List.range mol.atomCount).filterMap fun center =>
    (assignCenter? mol (comparatorFuel mol) geom center).map fun d => (center, d)

/-! ## Structural facts about the canonical expansion -/

theorem canonicalChildren_forcedLeaf (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (leaf : node.forcedLeaf = true) : mol.canonicalChildren node = [] := by
  simp [RawMolecule.canonicalChildren, leaf]

theorem occurrenceLigandFrame?_forcedLeaf (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode) (leaf : node.forcedLeaf = true) :
    occurrenceLigandFrame? mol node = none := by
  simp [occurrenceLigandFrame?, occurrenceLigandCursors, CanonicalRerootCursor.children, leaf]

theorem frameAtoms?_forcedLeaf (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (leaf : node.forcedLeaf = true) : frameAtoms? mol node = none := by
  simp [frameAtoms?, occurrenceLigandFrame?_forcedLeaf mol node leaf]

theorem rawStep?_none_of_frame (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (under : Nat → OccurrenceAuxState) (noFrame : frameAtoms? mol node = none) :
    rawStep? mol fuel geom state ctx node under = none := by
  simp [rawStep?, noFrame]

theorem descriptorWith?_none_of_frame (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState) (noFrame : frameAtoms? mol node = none) :
    descriptorWith? mol fuel geom state ctx node sub = none := by
  simp [descriptorWith?, rawWith?, rawStep?_none_of_frame mol fuel _ state ctx node _ noFrame,
    caseFromMirror?]

/-- A node without a four-ligand frame contributes only its descendants' facts. -/
theorem facts_succ_noFrame (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (noFrame : frameAtoms? mol node = none) :
    facts mol fuel (depth + 1) geom state ctx node =
      (mol.canonicalChildren node).flatMap (facts mol fuel depth geom state ctx) := by
  rw [facts_succ]
  unfold descriptor?
  rw [descriptorWith?_none_of_frame mol fuel geom state ctx node _ noFrame]
  rfl

theorem flatMap_nil_fun {α β : Type} (l : List α) :
    l.flatMap (fun _ : α => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp_all

theorem facts_forcedLeaf (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (leaf : node.forcedLeaf = true) : facts mol fuel depth geom state ctx node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      rw [facts_succ_noFrame mol fuel depth geom state ctx node (frameAtoms?_forcedLeaf mol node leaf),
        canonicalChildren_forcedLeaf mol node leaf]
      rfl

theorem mem_eraseCanonicalParentCopy (parent : Nat) (copies : List (Nat × Nat)) (copy : Nat × Nat)
    (member : copy ∈ RawMolecule.eraseCanonicalParentCopy parent copies) : copy ∈ copies := by
  induction copies with
  | nil => simp [RawMolecule.eraseCanonicalParentCopy] at member
  | cons head tail ih =>
      simp only [RawMolecule.eraseCanonicalParentCopy] at member
      split at member
      · exact List.mem_cons_of_mem head member
      · rcases List.mem_cons.mp member with same | deeper
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons_of_mem head (ih deeper)

/-- Bond endpoints of a well-formed raw molecule are atom indices. -/
def WellFormedBonds (mol : RawMolecule) : Prop :=
  ∀ bond ∈ mol.bonds, bond.source < mol.atomCount ∧ bond.target < mol.atomCount

theorem mem_canonicalChildCopies (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (copy : Nat × Nat) (member : copy ∈ mol.canonicalChildCopies node)
    (wellFormed : WellFormedBonds mol) : copy.1 < mol.atomCount := by
  unfold RawMolecule.canonicalChildCopies at member
  have inner := mem_eraseCanonicalParentCopy _ _ _ member
  rw [List.mem_flatMap] at inner
  rcases inner with ⟨bond, bondMember, copyMember⟩
  rcases wellFormed bond bondMember with ⟨sourceLt, targetLt⟩
  by_cases sourceEq : bond.source == node.atom
  · simp only [sourceEq, ↓reduceIte, List.mem_map, List.mem_range] at copyMember
    rcases copyMember with ⟨_, _, rfl⟩
    exact targetLt
  · by_cases targetEq : bond.target == node.atom
    · simp only [sourceEq, targetEq, ↓reduceIte, Bool.false_eq_true, List.mem_map,
        List.mem_range] at copyMember
      rcases copyMember with ⟨_, _, rfl⟩
      exact sourceLt
    · simp [sourceEq, targetEq] at copyMember

/-- Every canonical child extends the history by its own atom; a real child adds a fresh atom. -/
theorem mem_canonicalChildren (mol : RawMolecule) (node child : RawMolecule.CanonicalBranchNode)
    (member : child ∈ mol.canonicalChildren node) :
    child.history = child.atom :: node.history ∧
      (child.forcedLeaf = false → child.atom ∉ node.history) ∧
      (WellFormedBonds mol → child.atom < mol.atomCount) := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : node.forcedLeaf = true
  · simp [leaf] at member
  · have leafFalse : node.forcedLeaf = false := by simpa using leaf
    simp only [leafFalse, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    rcases member with ⟨copy, copyMember, rfl⟩
    refine ⟨rfl, ?_, fun wellFormed => mem_canonicalChildCopies mol node copy copyMember wellFormed⟩
    intro real inHistory
    have contains : node.history.contains copy.1 = true := List.contains_iff_mem.mpr inHistory
    simp only [contains, ↓reduceIte] at real
    by_cases dup : (copy.2 != 0) = true
    · simp [RawMolecule.CanonicalBranchNode.forcedLeaf, dup] at real
    · simp [RawMolecule.CanonicalBranchNode.forcedLeaf, dup] at real

/-- A real occurrence: duplicate-free history of atom indices. -/
def GoodNode (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode) : Prop :=
  node.history.Nodup ∧ ∀ atom ∈ node.history, atom < mol.atomCount

theorem GoodNode.length_le {mol : RawMolecule} {node : RawMolecule.CanonicalBranchNode}
    (good : GoodNode mol node) : node.history.length ≤ mol.atomCount := by
  rcases good with ⟨nodup, inRange⟩
  have cardEq := List.toFinset_card_of_nodup nodup
  have subset : node.history.toFinset ⊆ Finset.range mol.atomCount := by
    intro atom memberFinset
    rw [List.mem_toFinset] at memberFinset
    exact Finset.mem_range.mpr (inRange atom memberFinset)
  have := Finset.card_le_card subset
  rw [cardEq, Finset.card_range] at this
  exact this

theorem GoodNode.child {mol : RawMolecule} {node child : RawMolecule.CanonicalBranchNode}
    (good : GoodNode mol node) (wellFormed : WellFormedBonds mol)
    (member : child ∈ mol.canonicalChildren node) (real : child.forcedLeaf = false) :
    GoodNode mol child := by
  rcases mem_canonicalChildren mol node child member with ⟨historyEq, fresh, inRange⟩
  rcases good with ⟨nodup, bounded⟩
  refine ⟨?_, ?_⟩
  · rw [historyEq]
    exact List.nodup_cons.mpr ⟨fresh real, nodup⟩
  · intro atom memberHistory
    rw [historyEq] at memberHistory
    rcases List.mem_cons.mp memberHistory with rfl | deeper
    · exact inRange wellFormed
    · exact bounded atom deeper

/-! ## The structural depth bound -/

theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons]
      rw [h head (List.mem_cons.mpr (Or.inl rfl)),
        ih fun a member => h a (List.mem_cons_of_mem head member)]

theorem mem_tiedChildren (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node child : RawMolecule.CanonicalBranchNode)
    (member : child ∈ tiedChildren mol fuel state node) : child ∈ mol.canonicalChildren node := by
  unfold tiedChildren at member
  split at member
  · exact (List.mem_filter.mp member).1
  · simp at member

theorem descriptorWith?_congr (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (sub₁ sub₂ : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState)
    (h : ∀ child ∈ mol.canonicalChildren node, ∀ g s x, sub₁ g s x child = sub₂ g s x child) :
    descriptorWith? mol fuel geom state ctx node sub₁ =
      descriptorWith? mol fuel geom state ctx node sub₂ := by
  have under : ∀ g, underWith mol fuel g state node sub₁ = underWith mol fuel g state node sub₂ := by
    intro g
    funext r
    unfold underWith
    exact flatMap_congr_mem _ _ _ fun child member =>
      h child (mem_tiedChildren mol fuel state node child member) g state (some r)
  unfold descriptorWith? rawWith?
  rw [under geom, under (mirror geom)]

/-- Depth is sufficient at a node when it is a forced leaf or a real occurrence whose history
leaves no room for a longer duplicate-free chain than the depth. -/
def Sufficient (mol : RawMolecule) (depth : Nat) (node : RawMolecule.CanonicalBranchNode) :
    Prop :=
  node.forcedLeaf = true ∨
    (GoodNode mol node ∧ mol.atomCount + 1 ≤ depth + node.history.length)

theorem Sufficient.child {mol : RawMolecule} {depth : Nat}
    {node child : RawMolecule.CanonicalBranchNode} (wellFormed : WellFormedBonds mol)
    (good : GoodNode mol node) (bound : mol.atomCount + 1 ≤ depth + 1 + node.history.length)
    (member : child ∈ mol.canonicalChildren node) : Sufficient mol depth child := by
  by_cases leaf : child.forcedLeaf = true
  · exact Or.inl leaf
  · have real : child.forcedLeaf = false := by simpa using leaf
    refine Or.inr ⟨good.child wellFormed member real, ?_⟩
    rw [(mem_canonicalChildren mol node child member).1, List.length_cons]
    omega

/-- **Structural bound.** Increasing sufficient depth never changes the contributed facts:
no duplicate-free in-range history exceeds the atom count. Sufficient depth never cuts off a real
occurrence that could contribute facts; a forced-leaf cutoff remains harmless. -/
theorem facts_stable (mol : RawMolecule) (fuel : Nat) (wellFormed : WellFormedBonds mol) :
    ∀ (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
      (node : RawMolecule.CanonicalBranchNode), Sufficient mol depth node →
      facts mol fuel depth geom state ctx node = facts mol fuel (depth + 1) geom state ctx node := by
  intro depth
  induction depth with
  | zero =>
      intro geom state ctx node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [facts_forcedLeaf mol fuel 0 geom state ctx node leaf,
          facts_forcedLeaf mol fuel 1 geom state ctx node leaf]
      · have := good.length_le
        omega
  | succ depth ih =>
      intro geom state ctx node sufficient
      rcases sufficient with leaf | ⟨good, bound⟩
      · rw [facts_forcedLeaf mol fuel _ geom state ctx node leaf,
          facts_forcedLeaf mol fuel _ geom state ctx node leaf]
      · have children : ∀ child ∈ mol.canonicalChildren node, ∀ g s x,
            facts mol fuel depth g s x child = facts mol fuel (depth + 1) g s x child :=
          fun child member g s x => ih g s x child (Sufficient.child wellFormed good bound member)
        rw [facts_succ, facts_succ]
        unfold descriptor?
        rw [descriptorWith?_congr mol fuel geom state ctx node _ _ children,
          flatMap_congr_mem _ _ _ fun child member => children child member geom state ctx]

theorem facts_stable_add (mol : RawMolecule) (fuel : Nat) (wellFormed : WellFormedBonds mol)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat)
    (node : RawMolecule.CanonicalBranchNode) (sufficient : Sufficient mol depth node) (k : Nat) :
    facts mol fuel (depth + k) geom state ctx node = facts mol fuel depth geom state ctx node := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have deeper : Sufficient mol (depth + k) node := by
        rcases sufficient with leaf | ⟨good, bound⟩
        · exact Or.inl leaf
        · exact Or.inr ⟨good, by omega⟩
      rw [← ih, Nat.add_succ, ← facts_stable mol fuel wellFormed (depth + k) geom state ctx node
        deeper]

/-- The structural depth is sufficient at every real in-range occurrence. -/
theorem sufficient_structuralDepth (mol : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (good : GoodNode mol node) : Sufficient mol (structuralDepth mol node) node := by
  refine Or.inr ⟨good, ?_⟩
  have := good.length_le
  unfold structuralDepth
  omega

/-- **The center descriptor is independent of any depth at or above the structural depth.** -/
theorem assignCenter?_stable (mol : RawMolecule) (fuel : Nat) (wellFormed : WellFormedBonds mol)
    (geom : Geometry) (center : Nat) (inRange : center < mol.atomCount) (k : Nat) :
    descriptor? mol fuel (structuralDepth mol (canonicalCenterRoot center) + k) geom [] none
        (canonicalCenterRoot center) =
      assignCenter? mol fuel geom center := by
  unfold assignCenter? descriptor?
  apply descriptorWith?_congr
  intro child member g s x
  have good : GoodNode mol (canonicalCenterRoot center) := by
    refine ⟨List.nodup_singleton center, ?_⟩
    intro atom memberHistory
    simp only [canonicalCenterRoot, List.mem_singleton] at memberHistory
    rw [memberHistory]
    exact inRange
  have bound : mol.atomCount + 1 ≤
      structuralDepth mol (canonicalCenterRoot center) + 1 +
        (canonicalCenterRoot center).history.length := by
    have := good.length_le
    unfold structuralDepth
    omega
  have sufficient := Sufficient.child wellFormed good bound member
  exact facts_stable_add mol fuel wellFormed _ g s x child sufficient k

/-! ## Evaluation equations used by instantiations -/

/-- A node without a frame whose canonical children are all forced leaves contributes nothing. -/
theorem facts_eq_nil_of_leafChildren (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (noFrame : frameAtoms? mol node = none)
    (leaves : ∀ child ∈ mol.canonicalChildren node, child.forcedLeaf = true) :
    facts mol fuel depth geom state ctx node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      rw [facts_succ_noFrame mol fuel depth geom state ctx node noFrame,
        flatMap_congr_mem _ _ (fun _ => []) fun child member =>
          facts_forcedLeaf mol fuel depth geom state ctx child (leaves child member)]
      exact flatMap_nil_fun _

theorem flatMap_facts_eq_nil (mol : RawMolecule) (fuel depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (nodes : List RawMolecule.CanonicalBranchNode)
    (leafy : ∀ n ∈ nodes, frameAtoms? mol n = none ∧
      ∀ c ∈ mol.canonicalChildren n, c.forcedLeaf = true) :
    nodes.flatMap (facts mol fuel depth geom state ctx) = [] := by
  rw [flatMap_congr_mem _ _ (fun _ => []) fun n member =>
    facts_eq_nil_of_leafChildren mol fuel depth geom state ctx n (leafy n member).1
      (leafy n member).2]
  exact flatMap_nil_fun _

/-- Carried reference present in the frame: evaluate under exactly that reference. -/
theorem rawStep?_carried (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (r : Nat) (node : RawMolecule.CanonicalBranchNode)
    (under : Nat → OccurrenceAuxState) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (order : ordinary? mol fuel state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (cons : consistent adjacent = true) (notStrict : strict adjacent = false)
    (inFrame : r ∈ atoms) :
    rawStep? mol fuel geom state (some r) node under =
      (appendFacts? state (under r)).bind fun temp =>
        markedReadback? mol fuel geom temp node r := by
  simp [rawStep?, frame, order, nodup, cons, notStrict, inFrame]

/-- Own context: consensus over the generated eligible references. -/
theorem rawStep?_consensus (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (under : Nat → OccurrenceAuxState) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (order : ordinary? mol fuel state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (cons : consistent adjacent = true) (notStrict : strict adjacent = false)
    (notInFrame : ∀ r, ctx = some r → r ∉ atoms) :
    rawStep? mol fuel geom state ctx node under =
      consensus ((eligibleOf atoms sorted adjacent).map fun r =>
        (appendFacts? state (under r)).bind fun temp =>
          markedReadback? mol fuel geom temp node r) := by
  cases ctx with
  | none => simp [rawStep?, frame, order, nodup, cons, notStrict]
  | some r => simp [rawStep?, frame, order, nodup, cons, notStrict, notInFrame r rfl]

theorem consensus_pair (x y : Option RS) :
    consensus [x, y] =
      match x, y with
      | some a, some b => if a = b then some a else none
      | _, _ => none := by
  cases x <;> cases y <;> rfl

theorem consensus_three_same (a : RS) : consensus [some a, some a, some a] = some a := by
  simp [consensus]

theorem caseFromMirror?_eq_swap (raw : RS) :
    caseFromMirror? (some raw) (some raw.swap) = some (.chiral raw) := by
  cases raw <;> rfl

theorem caseFromMirror?_eq_same (raw : RS) :
    caseFromMirror? (some raw) (some raw) = some (.pseudoasymmetric (pseudoRSOfRS raw)) := by
  cases raw <;> rfl

theorem caseFromMirror?_none_left (reflected : Option RS) :
    caseFromMirror? none reflected = none := rfl

theorem appendFacts?_nil (state : OccurrenceAuxState) : appendFacts? state [] = some state := rfl

theorem appendFacts?_two (f₁ f₂ : OccurrenceAuxFact) (distinct : f₁.key ≠ f₂.key) :
    appendFacts? [] [f₁, f₂] = some [f₁, f₂] := by
  simp [appendFacts?, appendInputFact?, distinct]

/-! ## Strict-order readback with the supplied state held fixed -/

theorem rawStep?_strict (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (under : Nat → OccurrenceAuxState) (atoms sorted : List Nat)
    (adjacent : List (Option Ordering)) (frame : frameAtoms? mol node = some atoms)
    (order : ordinary? mol fuel state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (isStrict : strict adjacent = true) :
    rawStep? mol fuel geom state ctx node under =
      (atomsAt? atoms sorted).bind (readback? geom) := by
  have cons : consistent adjacent = true := by
    unfold strict at isStrict
    unfold consistent
    rw [List.all_eq_true] at isStrict ⊢
    intro decision member
    simp [isStrict decision member]
  simp [rawStep?, frame, order, nodup, cons, isStrict]

/-- A strict ordinary order under the supplied state keeps its raw geometric readback. Holding
that state fixed during reflection makes this temporary descriptor uppercase, for every depth
and context. This does not claim preservation of ordinary pseudo labels under state reflection. -/
theorem descriptorWith?_strict (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawMolecule.CanonicalBranchNode)
    (sub : Geometry → OccurrenceAuxState → Option Nat → RawMolecule.CanonicalBranchNode →
      OccurrenceAuxState)
    (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (order : ordinary? mol fuel state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (isStrict : strict adjacent = true) :
    descriptorWith? mol fuel geom state ctx node sub =
      ((atomsAt? atoms sorted).bind (readback? geom)).map
        LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  unfold descriptorWith? rawWith?
  rw [rawStep?_strict mol fuel geom state ctx node _ atoms sorted adjacent frame order nodup
      isStrict,
    rawStep?_strict mol fuel (mirror geom) state ctx node _ atoms sorted adjacent frame order
      nodup isStrict]
  cases atomsAt? atoms sorted with
  | none => rfl
  | some ranked =>
      simp only [Option.bind_some]
      rw [readback_mirror]
      cases readback? geom ranked with
      | none => rfl
      | some raw =>
          cases raw <;> rfl

end TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation

assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation.readback_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation.facts_forcedLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation.mem_canonicalChildren
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation.facts_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation.assignCenter?_stable
assert_kernel_only TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation.descriptorWith?_strict
