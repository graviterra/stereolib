import TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingSingleBondChildren

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

/-! Generic single-bond occurrence children and natural-H ties, isolated from the prior
second-sphere family's physical construction. The proof terms follow the generic portions of
GeneralSecondSphereRuntimeBridge; no family domain or desired comparison is assumed. -/

/-- Independent element metadata from an actual raw AtomSpec record. Other spelling fields
are unrestricted: the real-node Rule-1a comparator observes only the element atomic number. -/
def ObservedElement (raw : RawMolecule) (atom : Nat) (element : Element) : Prop :=
  ∃ spec, raw.atomAt? atom = some spec ∧ spec.element = element

/-- Actual natural-H record metadata. Shared isotope metadata, rather than entire record
identity, is sufficient for the terminal sibling Rule-2 tie. Explicit-H metadata, aromaticity,
charge and annotation fields are unrestricted by this comparator theorem. -/
def ObservedNaturalHydrogen (raw : RawMolecule) (atom : Nat) : Prop :=
  ∃ spec, raw.atomAt? atom = some spec ∧ spec.element = Element.H ∧ spec.isotope? = none

theorem observed_naturalHydrogen_element (raw : RawMolecule) (atom : Nat)
    (observed : ObservedNaturalHydrogen raw atom) : ObservedElement raw atom Element.H := by
  obtain ⟨spec, lookup, element, _⟩ := observed
  exact ⟨spec, lookup, element⟩

theorem observed_element_z (raw : RawMolecule) (atom : Nat) (element : Element)
    (observed : ObservedElement raw atom element) : raw.atomZAt atom = element.atomicNumber := by
  obtain ⟨spec, lookup, matching⟩ := observed
  rw [atomZAt_eq_of_atomAt? raw atom spec lookup, matching]

theorem observed_naturalHydrogen_z (raw : RawMolecule) (atom : Nat)
    (observed : ObservedNaturalHydrogen raw atom) : raw.atomZAt atom = 1 := by
  exact observed_element_z raw atom Element.H (observed_naturalHydrogen_element raw atom observed)

theorem observed_naturalHydrogen_mass (raw : RawMolecule) (atom : Nat)
    (observed : ObservedNaturalHydrogen raw atom) :
    raw.atomMassAt atom = rule2MassPico Element.H none := by
  obtain ⟨spec, lookup, element, isotope⟩ := observed
  simp [atomMassAt, atomMassAt?, lookup, element, isotope, rule2MassPico]

/-- A real occurrence with its original chronological ancestry. -/
def pathNode (atom : Nat) (ancestors : List Nat) : CanonicalBranchNode :=
  { atom := atom, parent := ancestors.headD atom, history := atom :: ancestors,
    provenance := .realAtom }

def awayCursor (atom parent : Nat) (ancestors : List Nat) : CanonicalRerootCursor :=
  { node := pathNode atom (parent :: ancestors), previous? := some (pathNode parent ancestors) }

theorem originalParent_pathNode (atom parent : Nat) (ancestors : List Nat) :
    canonicalOriginalParent? (pathNode atom (parent :: ancestors)) =
      some (pathNode parent ancestors) := by
  cases ancestors <;> rfl

theorem pathNode_ne (left right : Nat) (leftAncestors rightAncestors : List Nat)
    (different : left ≠ right) : pathNode left leftAncestors ≠ pathNode right rightAncestors := by
  intro equal
  exact different (congrArg CanonicalBranchNode.atom equal)

private theorem canonical_bond_one (raw : RawMolecule) (node : CanonicalBranchNode) (atom : Nat)
    (one : raw.bondOrder node.atom atom = 1) : raw.canonicalBondOrder node atom = 1 := by
  cases history : node.history with
  | nil => simpa only [canonicalBondOrder, history] using one
  | cons first tail =>
      cases tail with
      | nil => simpa only [canonicalBondOrder, history] using one
      | cons second tail =>
          cases tail with
          | nil => simp [canonicalBondOrder, history, one]
          | cons third rest => simpa only [canonicalBondOrder, history] using one

private theorem unit_copies (raw : RawMolecule) (node : CanonicalBranchNode) (bonds : List RawBond)
    (single : ∀ bond ∈ bonds, ∀ atom, recordNeighbor? node.atom bond = some atom →
      raw.canonicalBondOrder node atom = 1) :
    (bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some atom => (List.range (raw.canonicalBondOrder node atom)).map (fun copy => (atom, copy))) =
    (bonds.filterMap (recordNeighbor? node.atom)).map (fun atom => (atom, 0)) := by
  induction bonds with
  | nil => rfl
  | cons bond bonds ih =>
      have tailSingle : ∀ selected ∈ bonds, ∀ atom, recordNeighbor? node.atom selected = some atom →
          raw.canonicalBondOrder node atom = 1 := by
        intro selected member atom observed
        exact single selected (List.mem_cons_of_mem bond member) atom observed
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases observed : recordNeighbor? node.atom bond with
      | none => simpa only [List.nil_append] using ih tailSingle
      | some atom =>
          have one := single bond List.mem_cons_self atom observed
          simp only [one, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
            List.map_nil, List.cons_append]
          rw [ih tailSingle]

private theorem erase_parent_map (parent : Nat) (atoms : List Nat) :
    eraseCanonicalParentCopy parent (atoms.map (fun atom => (atom, 0))) =
      (atoms.erase parent).map (fun atom => (atom, 0)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      by_cases equal : atom = parent
      · subst atom; simp [eraseCanonicalParentCopy]
      · simp [eraseCanonicalParentCopy, equal, ih]

/-- Actual raw single records generate one copy, with only the original parent copy erased. -/
theorem actual_child_copies (raw : RawMolecule) (node : CanonicalBranchNode)
    (single : ∀ other ∈ recordNeighbors raw node.atom, raw.bondOrder node.atom other = 1) :
    raw.canonicalChildCopies node =
      ((recordNeighbors raw node.atom).erase node.parent).map (fun other => (other, 0)) := by
  have seeds := unit_copies raw node raw.bonds (by
    intro bond retained other observed
    exact canonical_bond_one raw node other
      (single other (List.mem_filterMap.mpr ⟨bond, retained, observed⟩)))
  change eraseCanonicalParentCopy node.parent
    (raw.bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
      | none => []
      | some other => (List.range (raw.canonicalBondOrder node other)).map (fun copy => (other, copy))) = _
  rw [seeds, erase_parent_map]
  rfl

/-- Freshness is consumed only to derive real provenance from the actual child-copy generator. -/
theorem actual_path_children (raw : RawMolecule) (atom parent : Nat) (ancestors children : List Nat)
    (row : (recordNeighbors raw atom).erase parent = children)
    (single : ∀ other ∈ recordNeighbors raw atom, raw.bondOrder atom other = 1)
    (fresh : ∀ other ∈ children, other ∉ atom :: parent :: ancestors) :
    raw.canonicalChildren (pathNode atom (parent :: ancestors)) =
      children.map (fun other => pathNode other (atom :: parent :: ancestors)) := by
  have copies := actual_child_copies raw (pathNode atom (parent :: ancestors)) single
  change raw.canonicalChildCopies (pathNode atom (parent :: ancestors)) =
    ((recordNeighbors raw atom).erase parent).map (fun other => (other, 0)) at copies
  rw [row] at copies
  have forced : (pathNode atom (parent :: ancestors)).forcedLeaf = false := rfl
  unfold canonicalChildren
  rw [forced]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [copies, List.map_map]
  apply List.map_congr_left
  intro other member
  have absent := fresh other member
  simp [pathNode]
  simpa only [List.mem_cons, not_or] using absent

/-- A physical terminal's actual reroot cursor has no descendants, at arbitrary ancestry. -/
theorem actual_terminal_children (raw : RawMolecule) (leaf parent : Nat) (ancestors : List Nat)
    (row : recordNeighbors raw leaf = [parent]) (single : raw.bondOrder leaf parent = 1) :
    (awayCursor leaf parent ancestors).children raw = [] := by
  have children := actual_path_children raw leaf parent ancestors []
    (by
      rw [row]
      simp)
    (by
      intro other member
      rw [row] at member
      have equal := List.mem_singleton.mp member
      simpa only [equal] using single)
    (by simp)
  have forced : (pathNode leaf (parent :: ancestors)).forcedLeaf = false := rfl
  simp [awayCursor, CanonicalRerootCursor.children, CanonicalRerootCursor.neighbors,
    forced, originalParent_pathNode, children]

theorem physical_hydrogen_tie (raw : RawMolecule) (left right parent : Nat) (ancestors : List Nat)
    (leftAtom : ObservedNaturalHydrogen raw left)
    (rightAtom : ObservedNaturalHydrogen raw right)
    (leftRow : recordNeighbors raw left = [parent])
    (rightRow : recordNeighbors raw right = [parent])
    (leftSingle : raw.bondOrder left parent = 1) (rightSingle : raw.bondOrder right parent = 1)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt raw fuel stage (awayCursor left parent ancestors)
      (awayCursor right parent ancestors) = some Ordering.eq := by
  have lc := actual_terminal_children raw left parent ancestors leftRow leftSingle
  have rc := actual_terminal_children raw right parent ancestors rightRow rightSingle
  have leftZ := observed_naturalHydrogen_z raw left leftAtom
  have rightZ := observed_naturalHydrogen_z raw right rightAtom
  have leftMass := observed_naturalHydrogen_mass raw left leftAtom
  have rightMass := observed_naturalHydrogen_mass raw right rightAtom
  have rule1a : raw.compareCanonicalNodeRule? .rule1a
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) = some Ordering.eq := by
    have computed := compareCanonicalNodeRule?_rule1a_realAtom raw
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) rfl rfl
    simpa only [pathNode, leftZ, rightZ, Std.compare_self] using computed
  have rule1b : raw.compareCanonicalNodeRule? .rule1b
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) = some Ordering.eq := by
    simp [compareCanonicalNodeRule?, compareCanonicalNodeRule, pathNode,
      CanonicalBranchNode.rule1bRootDistance, CanonicalBranchNode.depth]
  have rule2 : raw.compareCanonicalNodeRule? .rule2
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) = some Ordering.eq := by
    simp [compareCanonicalNodeRule?, compareCanonicalNodeRule, pathNode, leftMass, rightMass]
  have terminalL : cursorTerminal raw (awayCursor left parent ancestors) = true := by
    simp [cursorTerminal, lc]
  have terminalR : cursorTerminal raw (awayCursor right parent ancestors) = true := by
    simp [cursorTerminal, rc]
  have pairedLabels (current : CanonicalRuleStage) : compareCursorPairLabels raw current
      [(awayCursor left parent ancestors, awayCursor right parent ancestors)] = some Ordering.eq := by
    cases current with
    | rule1a => simp only [compareCursorPairLabels, awayCursor, rule1a]
    | rule1b => simp only [compareCursorPairLabels, awayCursor, rule1b]
    | rule2 => simp only [compareCursorPairLabels, awayCursor, rule2]
  have next (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
      nextCursorPairs? raw before [(awayCursor left parent ancestors, awayCursor right parent ancestors)] = some [] := by
    simp [nextCursorPairs?, terminalL, terminalR]
  have rules (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
      (depth : Nat) (current : CanonicalRuleStage) :
      compareCursorRule raw before current depth
        [(awayCursor left parent ancestors, awayCursor right parent ancestors)] = some Ordering.eq := by
    cases depth <;> simp [compareCursorRule, pairedLabels, next, defaultBranchWidthCap]
  cases fuel with
  | zero =>
      cases stage with
      | rule1a => simp [compareCursorBranchAt, compareCanonicalNodeThrough?, awayCursor, rule1a]
      | rule1b => simp [compareCursorBranchAt, compareCanonicalNodeThrough?, awayCursor, rule1a, rule1b]
      | rule2 => simp [compareCursorBranchAt, compareCanonicalNodeThrough?, awayCursor, rule1a, rule1b, rule2]
  | succ fuel =>
      cases stage <;> simp only [compareCursorBranchAt, rules]


theorem physical_hydrogen_tie_authoritative (raw : RawMolecule) (left right parent : Nat) (ancestors : List Nat)
    (leftAtom : ObservedNaturalHydrogen raw left)
    (rightAtom : ObservedNaturalHydrogen raw right)
    (leftRow : recordNeighbors raw left = [parent])
    (rightRow : recordNeighbors raw right = [parent])
    (leftSingle : raw.bondOrder left parent = 1) (rightSingle : raw.bondOrder right parent = 1)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? raw fuel stage (awayCursor left parent ancestors)
      (awayCursor right parent ancestors) = some Ordering.eq := by
  have lc := actual_terminal_children raw left parent ancestors leftRow leftSingle
  have rc := actual_terminal_children raw right parent ancestors rightRow rightSingle
  have leftZ := observed_naturalHydrogen_z raw left leftAtom
  have rightZ := observed_naturalHydrogen_z raw right rightAtom
  have leftMass := observed_naturalHydrogen_mass raw left leftAtom
  have rightMass := observed_naturalHydrogen_mass raw right rightAtom
  have rule1a : raw.compareCanonicalNodeRuleAuthoritative? .rule1a
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) = some Ordering.eq := by
    have computed := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom raw
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) rfl rfl
    simpa only [pathNode, leftZ, rightZ, Std.compare_self] using computed
  have rule1b : raw.compareCanonicalNodeRuleAuthoritative? .rule1b
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) = some Ordering.eq := by
    simp [compareCanonicalNodeRuleAuthoritative?, compareCanonicalNodeRule, pathNode,
      CanonicalBranchNode.rule1bRootDistance, CanonicalBranchNode.depth]
  have rule2 : raw.compareCanonicalNodeRuleAuthoritative? .rule2
      (pathNode left (parent :: ancestors)) (pathNode right (parent :: ancestors)) = some Ordering.eq := by
    simp [compareCanonicalNodeRuleAuthoritative?, compareCanonicalNodeRule, pathNode, leftMass, rightMass]
  have terminalL : cursorTerminal raw (awayCursor left parent ancestors) = true := by
    simp [cursorTerminal, lc]
  have terminalR : cursorTerminal raw (awayCursor right parent ancestors) = true := by
    simp [cursorTerminal, rc]
  have pairedLabels (current : CanonicalRuleStage) : compareCursorPairLabelsAuthoritative? raw current
      [(awayCursor left parent ancestors, awayCursor right parent ancestors)] = some Ordering.eq := by
    cases current with
    | rule1a => simp only [compareCursorPairLabelsAuthoritative?, awayCursor, rule1a]
    | rule1b => simp only [compareCursorPairLabelsAuthoritative?, awayCursor, rule1b]
    | rule2 => simp only [compareCursorPairLabelsAuthoritative?, awayCursor, rule2]
  have next (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) :
      nextCursorPairsAuthoritative? raw before [(awayCursor left parent ancestors, awayCursor right parent ancestors)] = some [] := by
    simp [nextCursorPairsAuthoritative?, terminalL, terminalR]
  have rules (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
      (depth : Nat) (current : CanonicalRuleStage) :
      compareCursorRuleAuthoritative? raw before current depth
        [(awayCursor left parent ancestors, awayCursor right parent ancestors)] = some Ordering.eq := by
    cases depth <;> simp [compareCursorRuleAuthoritative?, pairedLabels, next]
  cases fuel with
  | zero =>
      cases stage with
      | rule1a => simp [compareCursorBranchAtAuthoritative?, compareCanonicalNodeThroughAuthoritative?, awayCursor, rule1a]
      | rule1b => simp [compareCursorBranchAtAuthoritative?, compareCanonicalNodeThroughAuthoritative?, awayCursor, rule1a, rule1b]
      | rule2 => simp [compareCursorBranchAtAuthoritative?, compareCanonicalNodeThroughAuthoritative?, awayCursor, rule1a, rule1b, rule2]
  | succ fuel =>
      cases stage <;> simp only [compareCursorBranchAtAuthoritative?, rules]

end TetraStereo.UniversalProof.NativeRingSingleBondChildren
