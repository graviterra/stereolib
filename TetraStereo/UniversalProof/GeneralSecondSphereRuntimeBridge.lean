import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery
import TetraStereo.UniversalProof.TerminalStarCycleGuard

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery
open TetraStereo.UniversalProof.TerminalStarCycleGuard










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

/-- The incoming bridge occurrence retains its backbone ancestry when rerooted at the tag. -/
def incomingBridge (backbone bridge tag : Nat) (tail : List Nat) : CanonicalRerootCursor :=
  { node := pathNode bridge (backbone :: tail),
    previous? := some (pathNode tag (bridge :: backbone :: tail)) }

def outgoingMethyl (backbone bridge tag methyl : Nat) (tail : List Nat) :
    CanonicalRerootCursor := awayCursor methyl tag (bridge :: backbone :: tail)

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

structure Roles (raw : RawMolecule) where
  backbone : Fin raw.atomCount
  bridge : Fin raw.atomCount
  tag : Fin raw.atomCount
  methyl : Fin raw.atomCount
  bh1 : Fin raw.atomCount
  bh2 : Fin raw.atomCount
  mh1 : Fin raw.atomCount
  mh2 : Fin raw.atomCount
  mh3 : Fin raw.atomCount

def hydrogenRoles {raw : RawMolecule} (roles : Roles raw) : List Nat :=
  [roles.bh1.val, roles.bh2.val, roles.mh1.val, roles.mh2.val, roles.mh3.val]

/-- Independent physical records and the actual input occurrence ancestry. The tag row is
deliberately unrestricted: its remaining ligands can be H and F, as in the frozen 543 family. -/
structure InteriorDomain (raw : RawMolecule) (roles : Roles raw)
    (root : Fin raw.atomCount) (tail : List Nat) : Prop where
  well : raw.WellFormed
  rootAtom : ObservedElement raw root.val Element.C
  backboneAtom : ObservedElement raw roles.backbone.val Element.C
  bridgeAtom : ObservedElement raw roles.bridge.val Element.C
  methylAtom : ObservedElement raw roles.methyl.val Element.C
  hydrogenAtoms : ∀ h ∈ hydrogenRoles roles,
    ObservedNaturalHydrogen raw h
  bridgeRow : recordNeighbors raw roles.bridge.val =
    [roles.backbone.val, roles.bh1.val, roles.bh2.val, roles.tag.val]
  methylRow : recordNeighbors raw roles.methyl.val =
    [roles.tag.val, roles.mh1.val, roles.mh2.val, roles.mh3.val]
  bridgeDistinct : [roles.backbone.val, roles.bh1.val, roles.bh2.val, roles.tag.val].Nodup
  methylDistinct : [roles.tag.val, roles.mh1.val, roles.mh2.val, roles.mh3.val].Nodup
  bridgeSingle : ∀ other ∈ recordNeighbors raw roles.bridge.val,
    raw.bondOrder roles.bridge.val other = 1
  methylSingle : ∀ other ∈ recordNeighbors raw roles.methyl.val,
    raw.bondOrder roles.methyl.val other = 1
  bh1Row : recordNeighbors raw roles.bh1.val = [roles.bridge.val]
  bh2Row : recordNeighbors raw roles.bh2.val = [roles.bridge.val]
  mh1Row : recordNeighbors raw roles.mh1.val = [roles.methyl.val]
  mh2Row : recordNeighbors raw roles.mh2.val = [roles.methyl.val]
  mh3Row : recordNeighbors raw roles.mh3.val = [roles.methyl.val]
  generated : CanonicalCenterTreeNode raw root.val
    (pathNode roles.methyl.val (roles.tag.val :: roles.bridge.val :: roles.backbone.val :: tail))

section Interior
variable {raw : RawMolecule} {roles : Roles raw} {root : Fin raw.atomCount} {tail : List Nat}
variable (domain : InteriorDomain raw roles root tail)

def bridgeCursor : CanonicalRerootCursor :=
  incomingBridge roles.backbone.val roles.bridge.val roles.tag.val tail

def methylCursor : CanonicalRerootCursor :=
  outgoingMethyl roles.backbone.val roles.bridge.val roles.tag.val roles.methyl.val tail

def backboneCursor : CanonicalRerootCursor :=
  { node := pathNode roles.backbone.val tail,
    previous? := some (pathNode roles.bridge.val (roles.backbone.val :: tail)) }

def bridgeHydrogen (h : Nat) : CanonicalRerootCursor :=
  awayCursor h roles.bridge.val (roles.backbone.val :: tail)

def methylHydrogen (h : Nat) : CanonicalRerootCursor :=
  awayCursor h roles.methyl.val (roles.tag.val :: roles.bridge.val :: roles.backbone.val :: tail)

theorem carbon_z (atom : Nat) (observed : ObservedElement raw atom Element.C) :
    raw.atomZAt atom = 6 := by
  exact observed_element_z raw atom Element.C observed

/- Include the physical input domain even when it occurs only in the proof body. -/
include domain

theorem hydrogen_z (h : Nat) (member : h ∈ hydrogenRoles roles) : raw.atomZAt h = 1 := by
  exact observed_naturalHydrogen_z raw h (domain.hydrogenAtoms h member)

theorem generated_history_nodup :
    (roles.methyl.val :: roles.tag.val :: roles.bridge.val :: roles.backbone.val :: tail).Nodup :=
  (domain.generated.real_history root.isLt domain.well rfl).1

/-- Terminal raw records exclude H from all of the actual generated ancestral history. -/
theorem actual_hydrogen_fresh (h attached : Nat) (member : h ∈ hydrogenRoles roles)
    (row : recordNeighbors raw h = [attached]) :
    h ∉ roles.methyl.val :: roles.tag.val :: roles.bridge.val :: roles.backbone.val :: tail := by
  apply generated_terminal_absent raw domain.well root.val h attached root.isLt domain.generated rfl row
  · intro equal
    change roles.methyl.val = h at equal
    have carbon := carbon_z roles.methyl.val domain.methylAtom
    have hydrogen := hydrogen_z domain h member
    rw [equal, hydrogen] at carbon
    contradiction
  · intro equal
    have carbon := carbon_z root.val domain.rootAtom
    have hydrogen := hydrogen_z domain h member
    rw [equal, hydrogen] at carbon
    contradiction

theorem actual_bridge_children : (bridgeCursor (roles := roles) (tail := tail)).children raw =
    [backboneCursor (roles := roles) (tail := tail),
      bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val,
      bridgeHydrogen (roles := roles) (tail := tail) roles.bh2.val] := by
  have history := generated_history_nodup domain
  have tagFresh : roles.tag.val ∉ roles.bridge.val :: roles.backbone.val :: tail :=
    (List.nodup_cons.mp (List.nodup_cons.mp history).2).1
  have bh1Fresh := actual_hydrogen_fresh domain roles.bh1.val roles.bridge.val (by simp [hydrogenRoles]) domain.bh1Row
  have bh2Fresh := actual_hydrogen_fresh domain roles.bh2.val roles.bridge.val (by simp [hydrogenRoles]) domain.bh2Row
  have bh1Tail : roles.bh1.val ∉ roles.bridge.val :: roles.backbone.val :: tail := by
    intro member
    exact bh1Fresh (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have bh2Tail : roles.bh2.val ∉ roles.bridge.val :: roles.backbone.val :: tail := by
    intro member
    exact bh2Fresh (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have children := actual_path_children raw roles.bridge.val roles.backbone.val tail
    [roles.bh1.val, roles.bh2.val, roles.tag.val]
    (by rw [domain.bridgeRow]; simp) domain.bridgeSingle (by
      intro other member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact bh1Tail
      · exact bh2Tail
      · exact tagFresh)
  have backboneNeTag : roles.backbone.val ≠ roles.tag.val := by
    intro equal
    exact tagFresh (by simp [equal])
  have bh1NeTag : roles.bh1.val ≠ roles.tag.val := by
    intro equal; exact bh1Fresh (by simp [equal])
  have bh2NeTag : roles.bh2.val ≠ roles.tag.val := by
    intro equal; exact bh2Fresh (by simp [equal])
  have forced : (pathNode roles.bridge.val (roles.backbone.val :: tail)).forcedLeaf = false := rfl
  simp only [bridgeCursor, incomingBridge, CanonicalRerootCursor.children,
    CanonicalRerootCursor.neighbors, forced, originalParent_pathNode, children]
  simp [backboneCursor, bridgeHydrogen, awayCursor, List.filterMap_nil,
    pathNode_ne _ _ _ _ backboneNeTag, pathNode_ne _ _ _ _ bh1NeTag,
    pathNode_ne _ _ _ _ bh2NeTag]

theorem actual_methyl_children : (methylCursor (roles := roles) (tail := tail)).children raw =
    [methylHydrogen (roles := roles) (tail := tail) roles.mh1.val,
      methylHydrogen (roles := roles) (tail := tail) roles.mh2.val,
      methylHydrogen (roles := roles) (tail := tail) roles.mh3.val] := by
  have mh1Fresh := actual_hydrogen_fresh domain roles.mh1.val roles.methyl.val (by simp [hydrogenRoles]) domain.mh1Row
  have mh2Fresh := actual_hydrogen_fresh domain roles.mh2.val roles.methyl.val (by simp [hydrogenRoles]) domain.mh2Row
  have mh3Fresh := actual_hydrogen_fresh domain roles.mh3.val roles.methyl.val (by simp [hydrogenRoles]) domain.mh3Row
  have children := actual_path_children raw roles.methyl.val roles.tag.val
    (roles.bridge.val :: roles.backbone.val :: tail) [roles.mh1.val, roles.mh2.val, roles.mh3.val]
    (by rw [domain.methylRow]; simp) domain.methylSingle (by
      intro other member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact mh1Fresh
      · exact mh2Fresh
      · exact mh3Fresh)
  have mh1NeTag : roles.mh1.val ≠ roles.tag.val := by
    intro equal; exact mh1Fresh (by simp [equal])
  have mh2NeTag : roles.mh2.val ≠ roles.tag.val := by
    intro equal; exact mh2Fresh (by simp [equal])
  have mh3NeTag : roles.mh3.val ≠ roles.tag.val := by
    intro equal; exact mh3Fresh (by simp [equal])
  have forced : (pathNode roles.methyl.val
      (roles.tag.val :: roles.bridge.val :: roles.backbone.val :: tail)).forcedLeaf = false := rfl
  simp only [methylCursor, outgoingMethyl, awayCursor, CanonicalRerootCursor.children,
    CanonicalRerootCursor.neighbors, forced, originalParent_pathNode, children]
  simp [methylHydrogen, awayCursor, List.filterMap_nil,
    pathNode_ne _ _ _ _ mh1NeTag, pathNode_ne _ _ _ _ mh2NeTag,
    pathNode_ne _ _ _ _ mh3NeTag]

/-- Both actual physical branches are nonterminal, shared by the two comparator paths. -/
private theorem actual_nonterminal_both :
    cursorTerminal raw (bridgeCursor (roles := roles) (tail := tail)) = false ∧
    cursorTerminal raw (methylCursor (roles := roles) (tail := tail)) = false := by
  constructor
  · rw [cursorTerminal, actual_bridge_children domain]
    rfl
  · rw [cursorTerminal, actual_methyl_children domain]
    rfl

theorem methyl_terminal_star : TerminalStar raw roles.methyl.val roles.tag.val
    roles.mh1.val roles.mh2.val roles.mh3.val :=
  ⟨domain.well, domain.methylRow, domain.methylDistinct,
    domain.mh1Row, domain.mh2Row, domain.mh3Row⟩

theorem actual_guards (fuel : Nat) (decision : Ordering) :
    occurrenceRootsProvedAutomorphic raw fuel (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) decision = false ∧
    occurrenceRootsProvedAutomorphic raw fuel (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) decision = false := by
  have excluded := terminalStar_atomLiesInCycle_false raw roles.methyl.val roles.tag.val
    roles.mh1.val roles.mh2.val roles.mh3.val fuel (methyl_terminal_star domain)
  simp [occurrenceRootsProvedAutomorphic, bridgeCursor, methylCursor, incomingBridge,
    outgoingMethyl, awayCursor, pathNode, excluded]

end Interior

/-! Terminal sibling comparison is proved for actual physical H records. Recursive refinement
cannot manufacture a distinction once both reroot branches have no children. -/

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

section Comparison
variable {raw : RawMolecule} {roles : Roles raw} {root : Fin raw.atomCount} {tail : List Nat}
variable (domain : InteriorDomain raw roles root tail)
include domain

private theorem bridge_hydrogen_single (h : Nat) (member : h ∈ [roles.bh1.val, roles.bh2.val]) :
    raw.bondOrder h roles.bridge.val = 1 := by
  rw [raw.bondOrder_symm]
  exact domain.bridgeSingle h (by
    rw [domain.bridgeRow]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with first | second
    · exact Or.inr (Or.inl first)
    · exact Or.inr (Or.inr (Or.inl second)))

private theorem methyl_hydrogen_single (h : Nat)
    (member : h ∈ [roles.mh1.val, roles.mh2.val, roles.mh3.val]) :
    raw.bondOrder h roles.methyl.val = 1 := by
  rw [raw.bondOrder_symm]
  exact domain.methylSingle h (by rw [domain.methylRow]; simp_all)

theorem bridge_sibling_tie (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt raw fuel stage (bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val)
      (bridgeHydrogen (roles := roles) (tail := tail) roles.bh2.val) = some Ordering.eq := by
  exact physical_hydrogen_tie raw roles.bh1.val roles.bh2.val roles.bridge.val
    (roles.backbone.val :: tail)
    (domain.hydrogenAtoms _ (by simp [hydrogenRoles]))
    (domain.hydrogenAtoms _ (by simp [hydrogenRoles])) domain.bh1Row domain.bh2Row
    (bridge_hydrogen_single domain _ (by simp)) (bridge_hydrogen_single domain _ (by simp)) fuel stage

theorem methyl_sibling_tie (left right : Nat)
    (leftMember : left ∈ [roles.mh1.val, roles.mh2.val, roles.mh3.val])
    (rightMember : right ∈ [roles.mh1.val, roles.mh2.val, roles.mh3.val])
    (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt raw fuel stage (methylHydrogen (roles := roles) (tail := tail) left)
      (methylHydrogen (roles := roles) (tail := tail) right) = some Ordering.eq := by
  have row : ∀ h ∈ [roles.mh1.val, roles.mh2.val, roles.mh3.val],
      recordNeighbors raw h = [roles.methyl.val] := by
    intro h member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact domain.mh1Row
    · exact domain.mh2Row
    · exact domain.mh3Row
  exact physical_hydrogen_tie raw left right roles.methyl.val
    (roles.tag.val :: roles.bridge.val :: roles.backbone.val :: tail)
    (domain.hydrogenAtoms _ (by simp_all [hydrogenRoles]))
    (domain.hydrogenAtoms _ (by simp_all [hydrogenRoles]))
    (row left leftMember) (row right rightMember)
    (methyl_hydrogen_single domain _ leftMember) (methyl_hydrogen_single domain _ rightMember) fuel stage

theorem backbone_over_hydrogen (h : Nat) (member : h ∈ hydrogenRoles roles)
    (ancestors : List Nat) (previous : CanonicalBranchNode) (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt raw fuel stage (backboneCursor (roles := roles) (tail := tail))
      { node := pathNode h ancestors, previous? := some previous } = some Ordering.gt := by
  have carbon := carbon_z roles.backbone.val domain.backboneAtom
  have hydrogen := hydrogen_z domain h member
  have different : raw.atomZAt roles.backbone.val ≠ raw.atomZAt h := by rw [carbon, hydrogen]; decide
  have result := compareCursorBranchAt_eq_of_rule1a raw
    (backboneCursor (roles := roles) (tail := tail))
    { node := pathNode h ancestors, previous? := some previous } rfl rfl different fuel stage
  simpa [backboneCursor, pathNode, carbon, hydrogen] using result

theorem bridge_sibling_tie_authoritative (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? raw fuel stage (bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val)
      (bridgeHydrogen (roles := roles) (tail := tail) roles.bh2.val) = some Ordering.eq := by
  exact physical_hydrogen_tie_authoritative raw roles.bh1.val roles.bh2.val roles.bridge.val
    (roles.backbone.val :: tail)
    (domain.hydrogenAtoms _ (by simp [hydrogenRoles]))
    (domain.hydrogenAtoms _ (by simp [hydrogenRoles])) domain.bh1Row domain.bh2Row
    (bridge_hydrogen_single domain _ (by simp)) (bridge_hydrogen_single domain _ (by simp)) fuel stage

theorem methyl_sibling_tie_authoritative (left right : Nat)
    (leftMember : left ∈ [roles.mh1.val, roles.mh2.val, roles.mh3.val])
    (rightMember : right ∈ [roles.mh1.val, roles.mh2.val, roles.mh3.val])
    (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? raw fuel stage (methylHydrogen (roles := roles) (tail := tail) left)
      (methylHydrogen (roles := roles) (tail := tail) right) = some Ordering.eq := by
  have row : ∀ h ∈ [roles.mh1.val, roles.mh2.val, roles.mh3.val],
      recordNeighbors raw h = [roles.methyl.val] := by
    intro h member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact domain.mh1Row
    · exact domain.mh2Row
    · exact domain.mh3Row
  exact physical_hydrogen_tie_authoritative raw left right roles.methyl.val
    (roles.tag.val :: roles.bridge.val :: roles.backbone.val :: tail)
    (domain.hydrogenAtoms _ (by simp_all [hydrogenRoles]))
    (domain.hydrogenAtoms _ (by simp_all [hydrogenRoles]))
    (row left leftMember) (row right rightMember)
    (methyl_hydrogen_single domain _ leftMember) (methyl_hydrogen_single domain _ rightMember) fuel stage

theorem backbone_over_hydrogen_authoritative (h : Nat) (member : h ∈ hydrogenRoles roles)
    (ancestors : List Nat) (previous : CanonicalBranchNode) (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? raw fuel stage (backboneCursor (roles := roles) (tail := tail))
      { node := pathNode h ancestors, previous? := some previous } = some Ordering.gt := by
  have carbon := carbon_z roles.backbone.val domain.backboneAtom
  have hydrogen := hydrogen_z domain h member
  have different : raw.atomZAt roles.backbone.val ≠ raw.atomZAt h := by rw [carbon, hydrogen]; decide
  have result := compareCursorBranchAtAuthoritative?_eq_of_rule1a raw
    (backboneCursor (roles := roles) (tail := tail))
    { node := pathNode h ancestors, previous? := some previous } rfl rfl different fuel stage
  simpa [backboneCursor, pathNode, carbon, hydrogen] using result

theorem actual_ranked_bridge (fuel : Nat) (stage : CanonicalRuleStage) :
    rankedCursorChildren? raw (compareCursorBranchAt raw fuel stage)
      (bridgeCursor (roles := roles) (tail := tail)) =
    some [backboneCursor (roles := roles) (tail := tail),
      bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val,
      bridgeHydrogen (roles := roles) (tail := tail) roles.bh2.val] := by
  have tied := bridge_sibling_tie domain fuel stage
  have above := backbone_over_hydrogen domain roles.bh1.val (by simp [hydrogenRoles])
    (roles.bridge.val :: roles.backbone.val :: tail)
    (pathNode roles.bridge.val (roles.backbone.val :: tail)) fuel stage
  change compareCursorBranchAt raw fuel stage (backboneCursor (roles := roles) (tail := tail))
    (bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val) = some Ordering.gt at above
  simp [rankedCursorChildren?, actual_bridge_children domain, sortCursorsBy?, insertCursorBy?, tied, above]

theorem actual_ranked_methyl (fuel : Nat) (stage : CanonicalRuleStage) :
    rankedCursorChildren? raw (compareCursorBranchAt raw fuel stage)
      (methylCursor (roles := roles) (tail := tail)) =
    some [methylHydrogen (roles := roles) (tail := tail) roles.mh1.val,
      methylHydrogen (roles := roles) (tail := tail) roles.mh2.val,
      methylHydrogen (roles := roles) (tail := tail) roles.mh3.val] := by
  have tied12 := methyl_sibling_tie domain roles.mh1.val roles.mh2.val (by simp) (by simp) fuel stage
  have tied23 := methyl_sibling_tie domain roles.mh2.val roles.mh3.val (by simp) (by simp) fuel stage
  simp [rankedCursorChildren?, actual_methyl_children domain, sortCursorsBy?, insertCursorBy?, tied12, tied23]

/-- Both orientations of the actual fast constitutional comparison, for every positive fuel.
The leading child pair decides; deeper ancestry and auxiliary facts are never inspected. -/
theorem actual_fast_raw_both (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt raw (fuel + 1) stage (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some Ordering.gt ∧
    compareCursorBranchAt raw (fuel + 1) stage (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some Ordering.lt := by
  have bridgeZ := carbon_z roles.bridge.val domain.bridgeAtom
  have methylZ := carbon_z roles.methyl.val domain.methylAtom
  have backboneZ := carbon_z roles.backbone.val domain.backboneAtom
  have hydrogenZ := hydrogen_z domain roles.mh1.val (by simp [hydrogenRoles])
  have rootTie := compareCanonicalNodeRule?_rule1a_realAtom raw
    (bridgeCursor (roles := roles) (tail := tail)).node
    (methylCursor (roles := roles) (tail := tail)).node rfl rfl
  have rootTieReverse := compareCanonicalNodeRule?_rule1a_realAtom raw
    (methylCursor (roles := roles) (tail := tail)).node
    (bridgeCursor (roles := roles) (tail := tail)).node rfl rfl
  have lead := compareCanonicalNodeRule?_rule1a_realAtom raw
    (backboneCursor (roles := roles) (tail := tail)).node
    (methylHydrogen (roles := roles) (tail := tail) roles.mh1.val).node rfl rfl
  have leadReverse := compareCanonicalNodeRule?_rule1a_realAtom raw
    (methylHydrogen (roles := roles) (tail := tail) roles.mh1.val).node
    (backboneCursor (roles := roles) (tail := tail)).node rfl rfl
  change _ = some (compare (raw.atomZAt roles.bridge.val) (raw.atomZAt roles.methyl.val)) at rootTie
  rw [bridgeZ, methylZ] at rootTie
  change _ = some Ordering.eq at rootTie
  change _ = some (compare (raw.atomZAt roles.methyl.val) (raw.atomZAt roles.bridge.val)) at rootTieReverse
  rw [methylZ, bridgeZ] at rootTieReverse
  change _ = some Ordering.eq at rootTieReverse
  change _ = some (compare (raw.atomZAt roles.backbone.val) (raw.atomZAt roles.mh1.val)) at lead
  rw [backboneZ, hydrogenZ] at lead
  change _ = some Ordering.gt at lead
  change _ = some (compare (raw.atomZAt roles.mh1.val) (raw.atomZAt roles.backbone.val)) at leadReverse
  rw [hydrogenZ, backboneZ] at leadReverse
  change _ = some Ordering.lt at leadReverse
  have nonterminal := actual_nonterminal_both domain
  have nonterminalBridge := nonterminal.1
  have nonterminalMethyl := nonterminal.2
  have rankedB := actual_ranked_bridge domain fuel stage
  have rankedM := actual_ranked_methyl domain fuel stage
  have rootForward : compareCursorPairLabels raw .rule1a
      [(bridgeCursor (roles := roles) (tail := tail), methylCursor (roles := roles) (tail := tail))] =
      some Ordering.eq := by
    simp only [compareCursorPairLabels, rootTie]
  have rootReverse : compareCursorPairLabels raw .rule1a
      [(methylCursor (roles := roles) (tail := tail), bridgeCursor (roles := roles) (tail := tail))] =
      some Ordering.eq := by
    simp only [compareCursorPairLabels, rootTieReverse]
  let b := bridgeCursor (roles := roles) (tail := tail)
  let m := methylCursor (roles := roles) (tail := tail)
  let bc := backboneCursor (roles := roles) (tail := tail)
  let bh1 := bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val
  let bh2 := bridgeHydrogen (roles := roles) (tail := tail) roles.bh2.val
  let mh1 := methylHydrogen (roles := roles) (tail := tail) roles.mh1.val
  let mh2 := methylHydrogen (roles := roles) (tail := tail) roles.mh2.val
  let mh3 := methylHydrogen (roles := roles) (tail := tail) roles.mh3.val
  let forwardPairs := [(bc, mh1), (bh1, mh2), (bh2, mh3)]
  let reversePairs := [(mh1, bc), (mh2, bh1), (mh3, bh2)]
  change compareCursorPairLabels raw .rule1a [(b, m)] = some Ordering.eq at rootForward
  change compareCursorPairLabels raw .rule1a [(m, b)] = some Ordering.eq at rootReverse
  change raw.compareCanonicalNodeRule? .rule1a bc.node mh1.node = some Ordering.gt at lead
  change raw.compareCanonicalNodeRule? .rule1a mh1.node bc.node = some Ordering.lt at leadReverse
  have expandedForward : nextCursorPairs? raw (compareCursorBranchAt raw fuel stage) [(b, m)] = some forwardPairs := by
    simp [nextCursorPairs?, b, m, forwardPairs, bc, bh1, bh2, mh1, mh2, mh3,
      nonterminalBridge, nonterminalMethyl, rankedB, rankedM, List.zip_cons_cons]
  have expandedReverse : nextCursorPairs? raw (compareCursorBranchAt raw fuel stage) [(m, b)] = some reversePairs := by
    simp [nextCursorPairs?, b, m, reversePairs, bc, bh1, bh2, mh1, mh2, mh3,
      nonterminalBridge, nonterminalMethyl, rankedB, rankedM, List.zip_cons_cons]
  have labelForward : compareCursorPairLabels raw .rule1a forwardPairs = some Ordering.gt := by
    simp only [forwardPairs, compareCursorPairLabels, lead]
  have labelReverse : compareCursorPairLabels raw .rule1a reversePairs = some Ordering.lt := by
    simp only [reversePairs, compareCursorPairLabels, leadReverse]
  have widthForward : ¬ defaultBranchWidthCap < forwardPairs.length := by
    simp [defaultBranchWidthCap, forwardPairs]
  have widthReverse : ¬ defaultBranchWidthCap < reversePairs.length := by
    simp [defaultBranchWidthCap, reversePairs]
  have secondForward (depth : Nat) : compareCursorRule raw (compareCursorBranchAt raw fuel stage) .rule1a depth forwardPairs =
      some Ordering.gt := by
    cases depth <;> simp only [compareCursorRule, widthForward, labelForward, ↓reduceIte]
  have secondReverse (depth : Nat) : compareCursorRule raw (compareCursorBranchAt raw fuel stage) .rule1a depth reversePairs =
      some Ordering.lt := by
    cases depth <;> simp only [compareCursorRule, widthReverse, labelReverse, ↓reduceIte]
  have firstForward : compareCursorRule raw (compareCursorBranchAt raw fuel stage) .rule1a (fuel + 1) [(b, m)] =
      some Ordering.gt := by
    simp only [compareCursorRule]
    simp [rootForward, expandedForward, secondForward, defaultBranchWidthCap]
  have firstReverse : compareCursorRule raw (compareCursorBranchAt raw fuel stage) .rule1a (fuel + 1) [(m, b)] =
      some Ordering.lt := by
    simp only [compareCursorRule]
    simp [rootReverse, expandedReverse, secondReverse, defaultBranchWidthCap]
  change compareCursorBranchAt raw (fuel + 1) stage b m = some Ordering.gt ∧
    compareCursorBranchAt raw (fuel + 1) stage m b = some Ordering.lt
  constructor
  · simp only [compareCursorBranchAt, firstForward]
  · simp only [compareCursorBranchAt, firstReverse]

def paddingCursor (raw : RawMolecule) (cursor : CanonicalRerootCursor) : CanonicalRerootCursor :=
  { node := raw.canonicalPhantom cursor.node.atom (cursor.node.rule1bRootDistance + 1) }

/-- The authoritative path has two actual phantom slots beyond the three physical children. -/
theorem actual_ranked_bridge_authoritative (fuel : Nat) (stage : CanonicalRuleStage) :
    rankedCursorChildrenAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage)
      (bridgeCursor (roles := roles) (tail := tail)) =
    some ([backboneCursor (roles := roles) (tail := tail),
      bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val,
      bridgeHydrogen (roles := roles) (tail := tail) roles.bh2.val] ++
      List.replicate 2 (paddingCursor raw (bridgeCursor (roles := roles) (tail := tail)))) := by
  have tied := bridge_sibling_tie_authoritative domain fuel stage
  have above := backbone_over_hydrogen_authoritative domain roles.bh1.val (by simp [hydrogenRoles])
    (roles.bridge.val :: roles.backbone.val :: tail)
    (pathNode roles.bridge.val (roles.backbone.val :: tail)) fuel stage
  change compareCursorBranchAtAuthoritative? raw fuel stage
    (backboneCursor (roles := roles) (tail := tail))
    (bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val) = some Ordering.gt at above
  simp [rankedCursorChildrenAuthoritative?, actual_bridge_children domain, sortCursorsBy?,
    insertCursorBy?, tied, above, authoritativeChildSlots, paddingCursor]

theorem actual_ranked_methyl_authoritative (fuel : Nat) (stage : CanonicalRuleStage) :
    rankedCursorChildrenAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage)
      (methylCursor (roles := roles) (tail := tail)) =
    some ([methylHydrogen (roles := roles) (tail := tail) roles.mh1.val,
      methylHydrogen (roles := roles) (tail := tail) roles.mh2.val,
      methylHydrogen (roles := roles) (tail := tail) roles.mh3.val] ++
      List.replicate 2 (paddingCursor raw (methylCursor (roles := roles) (tail := tail)))) := by
  have tied12 := methyl_sibling_tie_authoritative domain roles.mh1.val roles.mh2.val (by simp) (by simp) fuel stage
  have tied23 := methyl_sibling_tie_authoritative domain roles.mh2.val roles.mh3.val (by simp) (by simp) fuel stage
  simp [rankedCursorChildrenAuthoritative?, actual_methyl_children domain, sortCursorsBy?,
    insertCursorBy?, tied12, tied23, authoritativeChildSlots, paddingCursor]

theorem actual_authoritative_raw_both (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? raw (fuel + 1) stage (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some Ordering.gt ∧
    compareCursorBranchAtAuthoritative? raw (fuel + 1) stage (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some Ordering.lt := by
  have bridgeZ := carbon_z roles.bridge.val domain.bridgeAtom
  have methylZ := carbon_z roles.methyl.val domain.methylAtom
  have backboneZ := carbon_z roles.backbone.val domain.backboneAtom
  have hydrogenZ := hydrogen_z domain roles.mh1.val (by simp [hydrogenRoles])
  have rootTie := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom raw
    (bridgeCursor (roles := roles) (tail := tail)).node
    (methylCursor (roles := roles) (tail := tail)).node rfl rfl
  have rootTieReverse := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom raw
    (methylCursor (roles := roles) (tail := tail)).node
    (bridgeCursor (roles := roles) (tail := tail)).node rfl rfl
  have lead := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom raw
    (backboneCursor (roles := roles) (tail := tail)).node
    (methylHydrogen (roles := roles) (tail := tail) roles.mh1.val).node rfl rfl
  have leadReverse := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom raw
    (methylHydrogen (roles := roles) (tail := tail) roles.mh1.val).node
    (backboneCursor (roles := roles) (tail := tail)).node rfl rfl
  change _ = some (compare (raw.atomZAt roles.bridge.val) (raw.atomZAt roles.methyl.val)) at rootTie
  rw [bridgeZ, methylZ] at rootTie
  change _ = some Ordering.eq at rootTie
  change _ = some (compare (raw.atomZAt roles.methyl.val) (raw.atomZAt roles.bridge.val)) at rootTieReverse
  rw [methylZ, bridgeZ] at rootTieReverse
  change _ = some Ordering.eq at rootTieReverse
  change _ = some (compare (raw.atomZAt roles.backbone.val) (raw.atomZAt roles.mh1.val)) at lead
  rw [backboneZ, hydrogenZ] at lead
  change _ = some Ordering.gt at lead
  change _ = some (compare (raw.atomZAt roles.mh1.val) (raw.atomZAt roles.backbone.val)) at leadReverse
  rw [hydrogenZ, backboneZ] at leadReverse
  change _ = some Ordering.lt at leadReverse
  have nonterminal := actual_nonterminal_both domain
  have nonterminalBridge := nonterminal.1
  have nonterminalMethyl := nonterminal.2
  have rankedB := actual_ranked_bridge_authoritative domain fuel stage
  have rankedM := actual_ranked_methyl_authoritative domain fuel stage
  have rootForward : compareCursorPairLabelsAuthoritative? raw .rule1a
      [(bridgeCursor (roles := roles) (tail := tail), methylCursor (roles := roles) (tail := tail))] =
      some Ordering.eq := by
    simp only [compareCursorPairLabelsAuthoritative?, rootTie]
  have rootReverse : compareCursorPairLabelsAuthoritative? raw .rule1a
      [(methylCursor (roles := roles) (tail := tail), bridgeCursor (roles := roles) (tail := tail))] =
      some Ordering.eq := by
    simp only [compareCursorPairLabelsAuthoritative?, rootTieReverse]
  let b := bridgeCursor (roles := roles) (tail := tail)
  let m := methylCursor (roles := roles) (tail := tail)
  let bc := backboneCursor (roles := roles) (tail := tail)
  let bh1 := bridgeHydrogen (roles := roles) (tail := tail) roles.bh1.val
  let bh2 := bridgeHydrogen (roles := roles) (tail := tail) roles.bh2.val
  let mh1 := methylHydrogen (roles := roles) (tail := tail) roles.mh1.val
  let mh2 := methylHydrogen (roles := roles) (tail := tail) roles.mh2.val
  let mh3 := methylHydrogen (roles := roles) (tail := tail) roles.mh3.val
  let forwardPairs := [(bc, mh1), (bh1, mh2), (bh2, mh3)] ++ List.replicate 2 (paddingCursor raw b, paddingCursor raw m)
  let reversePairs := [(mh1, bc), (mh2, bh1), (mh3, bh2)] ++ List.replicate 2 (paddingCursor raw m, paddingCursor raw b)
  change compareCursorPairLabelsAuthoritative? raw .rule1a [(b, m)] = some Ordering.eq at rootForward
  change compareCursorPairLabelsAuthoritative? raw .rule1a [(m, b)] = some Ordering.eq at rootReverse
  change raw.compareCanonicalNodeRuleAuthoritative? .rule1a bc.node mh1.node = some Ordering.gt at lead
  change raw.compareCanonicalNodeRuleAuthoritative? .rule1a mh1.node bc.node = some Ordering.lt at leadReverse
  have expandedForward : nextCursorPairsAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage) [(b, m)] = some forwardPairs := by
    simp [nextCursorPairsAuthoritative?, b, m, forwardPairs, bc, bh1, bh2, mh1, mh2, mh3,
      nonterminalBridge, nonterminalMethyl, rankedB, rankedM, List.replicate_succ, List.replicate_zero]
  have expandedReverse : nextCursorPairsAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage) [(m, b)] = some reversePairs := by
    simp [nextCursorPairsAuthoritative?, b, m, reversePairs, bc, bh1, bh2, mh1, mh2, mh3,
      nonterminalBridge, nonterminalMethyl, rankedB, rankedM, List.replicate_succ, List.replicate_zero]
  have labelForward : compareCursorPairLabelsAuthoritative? raw .rule1a forwardPairs = some Ordering.gt := by
    simp only [forwardPairs, List.cons_append, List.nil_append, compareCursorPairLabelsAuthoritative?, lead]
  have labelReverse : compareCursorPairLabelsAuthoritative? raw .rule1a reversePairs = some Ordering.lt := by
    simp only [reversePairs, List.cons_append, List.nil_append, compareCursorPairLabelsAuthoritative?, leadReverse]
  have secondForward (depth : Nat) : compareCursorRuleAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage) .rule1a depth forwardPairs =
      some Ordering.gt := by
    cases depth <;> simp only [compareCursorRuleAuthoritative?, labelForward]
  have secondReverse (depth : Nat) : compareCursorRuleAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage) .rule1a depth reversePairs =
      some Ordering.lt := by
    cases depth <;> simp only [compareCursorRuleAuthoritative?, labelReverse]
  have firstForward : compareCursorRuleAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage) .rule1a (fuel + 1) [(b, m)] =
      some Ordering.gt := by
    simp only [compareCursorRuleAuthoritative?, rootForward, expandedForward]
    exact secondForward fuel
  have firstReverse : compareCursorRuleAuthoritative? raw (compareCursorBranchAtAuthoritative? raw fuel stage) .rule1a (fuel + 1) [(m, b)] =
      some Ordering.lt := by
    simp only [compareCursorRuleAuthoritative?, rootReverse, expandedReverse]
    exact secondReverse fuel
  change compareCursorBranchAtAuthoritative? raw (fuel + 1) stage b m = some Ordering.gt ∧
    compareCursorBranchAtAuthoritative? raw (fuel + 1) stage m b = some Ordering.lt
  constructor
  · simp only [compareCursorBranchAtAuthoritative?, firstForward]
  · simp only [compareCursorBranchAtAuthoritative?, firstReverse]

theorem actual_certified_both (fuel : Nat) :
    certifiedConstitutionalStage? raw (fuel + 1) (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some Ordering.gt ∧
    certifiedConstitutionalStage? raw (fuel + 1) (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some Ordering.lt := by
  have strict := actual_fast_raw_both domain fuel .rule2
  have forwardGuard := (actual_guards domain (fuel + 1) .gt).1
  have reverseGuard := (actual_guards domain (fuel + 1) .lt).2
  simp [certifiedConstitutionalStage?, strict.1, strict.2, forwardGuard, reverseGuard]

theorem actual_fast_protocol_both (state : OccurrenceAuxState) (fuel : Nat) :
    compareOccurrenceBranches? raw state (fuel + 1) (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) =
      some { ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } ∧
    compareOccurrenceBranches? raw state (fuel + 1) (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) =
      some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  have certified := actual_certified_both domain fuel
  simp [compareOccurrenceBranches?, certified.1, certified.2]

theorem actual_certified_authoritative_both (fuel : Nat) :
    certifiedConstitutionalStageAuthoritative? raw (fuel + 1) (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some Ordering.gt ∧
    certifiedConstitutionalStageAuthoritative? raw (fuel + 1) (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some Ordering.lt := by
  have strict := actual_authoritative_raw_both domain fuel .rule2
  have forwardGuard := (actual_guards domain (fuel + 1) .gt).1
  have reverseGuard := (actual_guards domain (fuel + 1) .lt).2
  simp [certifiedConstitutionalStageAuthoritative?, strict.1, strict.2, forwardGuard, reverseGuard]

theorem actual_authoritative_protocol_both (state : OccurrenceAuxState) (fuel : Nat) :
    compareOccurrenceBranchesAuthoritative? raw state (fuel + 1) (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) =
      some { ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } ∧
    compareOccurrenceBranchesAuthoritative? raw state (fuel + 1) (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) =
      some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  have certified := actual_certified_authoritative_both domain fuel
  simp [compareOccurrenceBranchesAuthoritative?, certified.1, certified.2]

theorem actual_complete_protocol_both (state : OccurrenceAuxState) (fuel : Nat) :
    compareOccurrenceBranchesComplete? raw state (fuel + 1)
      (bridgeCursor (roles := roles) (tail := tail)) (methylCursor (roles := roles) (tail := tail)) =
      some { ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } ∧
    compareOccurrenceBranchesComplete? raw state (fuel + 1)
      (methylCursor (roles := roles) (tail := tail)) (bridgeCursor (roles := roles) (tail := tail)) =
      some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  have fast := actual_fast_protocol_both domain state fuel
  simp [compareOccurrenceBranchesComplete?, fast.1, fast.2]

/-- The public positive-threshold form: no assertion is made at zero comparison fuel. -/
theorem actual_complete_protocol_positive (state : OccurrenceAuxState) (fuel : Nat)
    (positive : 1 ≤ fuel) :
    compareOccurrenceBranchesComplete? raw state fuel (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some { ordering := Ordering.gt } ∧
    compareOccurrenceBranchesComplete? raw state fuel (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some { ordering := Ordering.lt } := by
  cases fuel with
  | zero => omega
  | succ fuel => exact actual_complete_protocol_both domain state fuel

end Comparison
end TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge
