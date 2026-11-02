import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap
import TetraStereo.OneCenter.LocalizedMarkedTerminalMarkedRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The actual frame at an outward terminal-twin center and its comparator symmetry

Every cursor of the actual four-ligand frame of an occurrence with two outward terminal twins is
one of: the two twin cursors, the ascending incoming-parent cursor, or a twin-free cursor (an
outward non-twin child, a ring duplicate, or the lone-pair phantom). From the key lemmas this
yields the comparator symmetry under exchanging the twin cursors and the two twin marks.

The incoming-parent cursor is handled through its stored Rule-1b distance, which differs from
every other slot; its Rule-6 key may genuinely depend on the mark through ring re-entry, and no
claim about that key is made.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeFrame

open LocalizedMarkedTerminalGaugeKeys LocalizedMarkedTerminalGaugeSwap
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedTerminalCursor
open LocalizedMarkedTerminalComparison LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedReachableConfigurations LocalizedMarkedUncappedOperations
open LocalizedMarkedUncappedRankingLaws
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPRule6PromotedComparatorLaws
open AuthoritativeCIPOccurrenceDescriptorComparatorLaws
open AuthoritativeCIPRerootComparatorLaws
open RawMolecule

abbrev Cursor := CanonicalRerootCursor
abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## Canonical child facts under single bonds -/

theorem child_parent (mol : RawMolecule) (node child : Node)
    (member : child ∈ mol.canonicalChildren node) : child.parent = node.atom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : node.forcedLeaf = true
  · simp [leaf] at member
  · have leafFalse : node.forcedLeaf = false := by simpa using leaf
    simp only [leafFalse, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, _, rfl⟩ := member
    rfl

theorem child_bond (mol : RawMolecule) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (node child : Node) (member : child ∈ mol.canonicalChildren node) :
    0 < mol.bondOrder node.atom child.atom := by
  have real : node.forcedLeaf = false := by
    cases leaf : node.forcedLeaf with
    | false => rfl
    | true => simp [LocalizedGenericMarkedRecalculation.canonicalChildren_forcedLeaf mol node leaf]
        at member
  have atoms := children_atoms mol wellFormed single node real
  have atomMem : child.atom ∈ (mol.canonicalChildren node).map (·.atom) :=
    List.mem_map.mpr ⟨child, member, rfl⟩
  rw [atoms] at atomMem
  exact (mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed child.atom).mp
    (List.mem_of_mem_erase atomMem)

theorem child_atom_ne_parent (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (node child : Node)
    (member : child ∈ mol.canonicalChildren node) : child.atom ≠ node.parent := by
  have real : node.forcedLeaf = false := by
    cases leaf : node.forcedLeaf with
    | false => rfl
    | true => simp [LocalizedGenericMarkedRecalculation.canonicalChildren_forcedLeaf mol node leaf]
        at member
  have atoms := children_atoms mol wellFormed single node real
  have atomMem : child.atom ∈ (mol.canonicalChildren node).map (·.atom) :=
    List.mem_map.mpr ⟨child, member, rfl⟩
  rw [atoms] at atomMem
  exact ((mol.canonicalIncidentNeighbors_nodup node.atom unique).mem_erase_iff.mp atomMem).1

/-- Under single bonds a canonical child is a real atom or a ring duplicate. -/
theorem child_provenance (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (node child : Node) (member : child ∈ mol.canonicalChildren node) :
    child.provenance = .realAtom ∨
      ∃ distance, child.provenance = .ringDuplicate distance := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : node.forcedLeaf = true
  · simp [leaf] at member
  · have leafFalse : node.forcedLeaf = false := by simpa using leaf
    simp only [leafFalse, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, copyMem, rfl⟩ := member
    rw [mol.canonicalChildCopies_eq_erase_seed, seeds_eq_neighbors mol wellFormed single] at copyMem
    have seed := LocalizedGenericMarkedRecalculation.mem_eraseCanonicalParentCopy _ _ _ copyMem
    obtain ⟨atom, _, copyEq⟩ := List.mem_map.mp seed
    subst copyEq
    by_cases ring : atom ∈ node.history
    · right
      exact ⟨RawMolecule.canonicalHistoryDistance node atom, by simp [ring]⟩
    · left
      simp [ring]

theorem realAtom_rule1b (node : Node) (real : node.provenance = .realAtom) :
    node.rule1bRootDistance = node.history.length - 1 := by
  simp [RawMolecule.CanonicalBranchNode.rule1bRootDistance, real,
    RawMolecule.CanonicalBranchNode.depth]

theorem terminal_children_nil (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (node twin : Node)
    (member : twin ∈ mol.canonicalChildren node)
    (terminal : TerminalNeighbor mol node.atom twin.atom) : mol.canonicalChildren twin = [] := by
  cases leaf : twin.forcedLeaf with
  | true => exact LocalizedGenericMarkedRecalculation.canonicalChildren_forcedLeaf mol twin leaf
  | false =>
      have atoms := children_atoms mol wellFormed single twin leaf
      have parent := child_parent mol node twin member
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child childMem
      have atomMem : child.atom ∈ (mol.canonicalChildren twin).map (·.atom) :=
        List.mem_map.mpr ⟨child, childMem, rfl⟩
      rw [atoms, parent] at atomMem
      have erased := (mol.canonicalIncidentNeighbors_nodup twin.atom unique).mem_erase_iff.mp atomMem
      have bond := (mol.mem_canonicalIncidentNeighbors_iff twin.atom wellFormed child.atom).mp
        erased.2
      exact erased.1 (terminal.2 child.atom bond)

/-! ## Frame structure -/

theorem frame_members (mol : RawMolecule) (target : Node) (roots : List Cursor)
    (frame : occurrenceLigandFrame? mol target = some roots) :
    ∀ c ∈ roots, c ∈ occurrenceLigandCursors mol target ∨
      c = { node := mol.canonicalPhantom target.atom (target.depth + 1), previous? := some target } := by
  unfold occurrenceLigandFrame? at frame
  dsimp only at frame
  split at frame
  · simp at frame
  · split at frame
    · simp only [Option.some.injEq] at frame
      subst frame
      intro c member
      exact Or.inl member
    · split at frame
      · simp only [Option.some.injEq] at frame
        subst frame
        intro c member
        rcases List.mem_append.mp member with physical | phantom
        · exact Or.inl physical
        · simp only [List.mem_singleton] at phantom
          exact Or.inr phantom
      · simp at frame

theorem frame_nodup (mol : RawMolecule) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (unique : mol.BondRecordsUnique) (target : Node) (reached : Reached mol target)
    (roots : List Cursor) (frame : occurrenceLigandFrame? mol target = some roots) :
    (LocalizedGenericMarkedRecalculation.frameAtomsOf roots).Nodup ∧ roots.Nodup := by
  have atomsNodup : (LocalizedGenericMarkedRecalculation.frameAtomsOf roots).Nodup := by
    have frameAtoms : LocalizedGenericMarkedRecalculation.frameAtoms? mol target =
        some (LocalizedGenericMarkedRecalculation.frameAtomsOf roots) := by
      simp [LocalizedGenericMarkedRecalculation.frameAtoms?, frame]
    rcases frame_atoms_perm_neighbors mol wellFormed single target reached _ frameAtoms with
      ⟨_, perm⟩ | ⟨_, perm⟩
    · exact perm.nodup_iff.mpr (mol.canonicalIncidentNeighbors_nodup target.atom unique)
    · refine perm.nodup_iff.mpr ?_
      rw [List.nodup_append]
      refine ⟨mol.canonicalIncidentNeighbors_nodup target.atom unique, List.nodup_singleton _, ?_⟩
      intro x xMem y yMem
      simp only [List.mem_singleton] at yMem
      subst yMem
      have bond := (mol.mem_canonicalIncidentNeighbors_iff target.atom wellFormed x).mp xMem
      exact Nat.ne_of_lt (mol.bondOrder_pos_endpoint_lt wellFormed bond).2
  exact ⟨atomsNodup, List.Nodup.of_map _ atomsNodup⟩

/-! ## Twin-freeness of outward non-twin slots -/

/-- Invariant along reroot descent below an outward slot of `target`. -/
def OutwardInvariant (mol : RawMolecule) (root : Nat) (T : List Nat) (target : Node)
    (d : Cursor) : Prop :=
  d.node.atom ∉ T ∧ ∃ parentNode : Node, d.previous? = some parentNode ∧
    d.node ∈ mol.canonicalChildren parentNode ∧ CanonicalCenterTreeNode mol root parentNode ∧
    target.atom ∈ d.node.history.tail

theorem outwardInvariant_step (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (root : Nat) (T : List Nat) (target : Node)
    (terminalT : ∀ t ∈ T, TerminalNeighbor mol target.atom t) (d e : Cursor)
    (inv : OutwardInvariant mol root T target d) (edge : e ∈ d.children mol) :
    OutwardInvariant mol root T target e := by
  obtain ⟨avoid, p, previous, child, generated, center⟩ := inv
  have shape : d = { node := d.node, previous? := some p } := by
    cases d
    simp only [CanonicalRerootCursor.mk.injEq, true_and]
    exact previous
  rw [shape] at edge
  obtain ⟨nb, nbMem, different, rfl⟩ := mem_cursor_children_of_previous edge
  have nodeGenerated := CanonicalCenterTreeNode.child generated child
  have nbChild : nb ∈ mol.canonicalChildren d.node := by
    rcases nodeGenerated.neighbor_cases nbMem with ⟨nbGenerated, fromNb⟩ | childCase
    · have fromP := canonicalOriginalParent?_eq_some_of_child generated child
      have fromNb' := canonicalOriginalParent?_eq_some_of_child nbGenerated fromNb
      rw [fromP] at fromNb'
      exact absurd (Option.some.inj fromNb').symm different
    · exact childCase
  have history := mol.canonicalChildren_history p d.node child
  have centerMem : target.atom ∈ p.history := by
    rw [history] at center
    exact center
  refine ⟨?_, d.node, rfl, nbChild, nodeGenerated, ?_⟩
  · intro atomIn
    have bond := child_bond mol wellFormed single d.node nb nbChild
    have sameCenter := (terminalT nb.atom atomIn).2 d.node.atom
      (by rwa [RawMolecule.bondOrder_symm])
    have inHistory : d.node.atom ∈ p.history := by
      rw [sameCenter]
      exact centerMem
    have leaf : d.node.forcedLeaf = true := by
      by_contra notLeaf
      have real : d.node.forcedLeaf = false := by simpa using notLeaf
      exact (LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol p d.node child).2.1 real
        inHistory
    rw [LocalizedGenericMarkedRecalculation.canonicalChildren_forcedLeaf mol d.node leaf] at nbChild
    simp at nbChild
  · rw [mol.canonicalChildren_history d.node nb nbChild]
    simp only [List.tail_cons]
    rw [history]
    exact List.mem_cons_of_mem _ centerMem

theorem outward_avoids (mol : RawMolecule) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (root : Nat) (T : List Nat) (target : Node)
    (targetGenerated : CanonicalCenterTreeNode mol root target)
    (terminalT : ∀ t ∈ T, TerminalNeighbor mol target.atom t) (n : Node)
    (child : n ∈ mol.canonicalChildren target) (notTwin : n.atom ∉ T) :
    Avoids mol T { node := n, previous? := some target } := by
  have base : OutwardInvariant mol root T target { node := n, previous? := some target } := by
    refine ⟨notTwin, target, rfl, child, targetGenerated, ?_⟩
    rw [mol.canonicalChildren_history target n child]
    simp only [List.tail_cons]
    exact List.mem_of_head?_eq_some targetGenerated.history_head
  intro d below
  have inv : OutwardInvariant mol root T target d := by
    induction below with
    | refl => exact base
    | tail _ edge ih => exact outwardInvariant_step mol wellFormed single root T target terminalT _ _ ih edge
  exact inv.1

/-! ## The outward terminal-twin center -/

structure TwinCenter (mol : RawMolecule) (target : Node) (left right : Cursor) : Prop where
  leftSlot : left ∈ occurrenceLigandCursors mol target
  rightSlot : right ∈ occurrenceLigandCursors mol target
  leftChild : left.node ∈ mol.canonicalChildren target
  rightChild : right.node ∈ mol.canonicalChildren target
  leftTerminal : TerminalNeighbor mol target.atom left.node.atom
  rightTerminal : TerminalNeighbor mol target.atom right.node.atom
  leftReal : left.node.provenance = .realAtom
  rightReal : right.node.provenance = .realAtom
  sameZ : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom
  sameMass : mol.atomMassAt left.node.atom = mol.atomMassAt right.node.atom
  distinct : left.node.atom ≠ right.node.atom

namespace TwinCenter

variable {mol : RawMolecule} {target : Node} {left right : Cursor}

/-- The two twin atoms. -/
def marks (_ : TwinCenter mol target left right) : List Nat := [left.node.atom, right.node.atom]

theorem leftPrevious (tc : TwinCenter mol target left right) :
    left = { node := left.node, previous? := some target } := by
  obtain ⟨_, _, rfl⟩ := mem_occurrenceLigandCursors tc.leftSlot
  rfl

theorem rightPrevious (tc : TwinCenter mol target left right) :
    right = { node := right.node, previous? := some target } := by
  obtain ⟨_, _, rfl⟩ := mem_occurrenceLigandCursors tc.rightSlot
  rfl

theorem cursor_ne (tc : TwinCenter mol target left right) : left ≠ right := by
  intro same
  exact tc.distinct (congrArg (fun c : Cursor => c.node.atom) same)

theorem marks_inRange (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed) :
    ∀ t ∈ tc.marks, t < mol.atomCount := by
  intro t member
  simp [marks] at member
  rcases member with rfl | rfl
  · exact (mol.bondOrder_pos_endpoint_lt wellFormed tc.leftTerminal.1).2
  · exact (mol.bondOrder_pos_endpoint_lt wellFormed tc.rightTerminal.1).2

theorem marks_terminal (tc : TwinCenter mol target left right) :
    ∀ t ∈ tc.marks, TerminalNeighbor mol target.atom t := by
  intro t member
  simp [marks] at member
  rcases member with rfl | rfl
  · exact tc.leftTerminal
  · exact tc.rightTerminal

theorem leftTerminalCursor (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target) :
    cursorTerminal mol left = true :=
  (ligand_terminal mol wellFormed single unique target reached left tc.leftSlot target.atom
    tc.leftTerminal).2

theorem rightTerminalCursor (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target) :
    cursorTerminal mol right = true :=
  (ligand_terminal mol wellFormed single unique target reached right tc.rightSlot target.atom
    tc.rightTerminal).2

theorem sameDepth (tc : TwinCenter mol target left right) :
    left.node.depth = right.node.depth :=
  outward_depth_eq mol target left right tc.leftChild tc.rightChild

/-- A child cursor of `target` carrying a twin atom is that twin cursor. -/
theorem child_cursor_eq (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (n : Node)
    (child : n ∈ mol.canonicalChildren target) :
    (n.atom = left.node.atom → ({ node := n, previous? := some target } : Cursor) = left) ∧
    (n.atom = right.node.atom → ({ node := n, previous? := some target } : Cursor) = right) := by
  have nodup := LocalizedMarkedGeneratedFactUniqueness.child_atoms_nodup mol wellFormed single
    unique target
  have injective := List.inj_on_of_nodup_map nodup
  constructor
  · intro same
    have nodeEq : n = left.node := injective child tc.leftChild same
    rw [nodeEq, ← tc.leftPrevious]
  · intro same
    have nodeEq : n = right.node := injective child tc.rightChild same
    rw [nodeEq, ← tc.rightPrevious]

/-- The ascending incoming-parent cursor, when `target` is not the expansion root. -/
def ascending? (target : Node) : Option Cursor :=
  (canonicalOriginalParent? target).map fun p => { node := p, previous? := some target }

/-- **Frame classification.** Every actual frame cursor is a twin, the incoming-parent cursor, or
twin-free. -/
theorem classify (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target)
    (roots : List Cursor) (frame : occurrenceLigandFrame? mol target = some roots) :
    ∀ c ∈ roots, c = left ∨ c = right ∨ ascending? target = some c ∨ Avoids mol tc.marks c := by
  obtain ⟨root, valid, path⟩ := reached
  have generated := generated_of_reachedFrom mol root target path
  intro c member
  rcases frame_members mol target roots frame c member with slot | phantom
  · obtain ⟨nb, nbMem, rfl⟩ := mem_occurrenceLigandCursors slot
    rcases generated.neighbor_cases nbMem with ⟨nbGenerated, fromNb⟩ | child
    · right; right; left
      simp [ascending?, canonicalOriginalParent?_eq_some_of_child nbGenerated fromNb]
    · by_cases isLeft : nb.atom = left.node.atom
      · left
        exact (tc.child_cursor_eq wellFormed single unique nb child).1 isLeft
      · by_cases isRight : nb.atom = right.node.atom
        · right; left
          exact (tc.child_cursor_eq wellFormed single unique nb child).2 isRight
        · right; right; right
          apply outward_avoids mol wellFormed single root tc.marks target generated
            tc.marks_terminal nb child
          simp [marks, isLeft, isRight]
  · right; right; right
    rw [phantom]
    exact avoids_phantom mol tc.marks (tc.marks_inRange wellFormed) _ _ _

/-! ### Stored Rule-1b distances of the frame slots -/

theorem ascending_distance (target : Node) (p : Node) (parent : canonicalOriginalParent? target = some p) :
    p.rule1bRootDistance = target.history.length - 2 ∧ 2 ≤ target.history.length := by
  rcases h : target.history with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp [canonicalOriginalParent?, h] at parent
  · simp [canonicalOriginalParent?, h] at parent
  · simp only [canonicalOriginalParent?, h, Option.some.injEq] at parent
    subst parent
    refine ⟨?_, by simp⟩
    simp [RawMolecule.CanonicalBranchNode.rule1bRootDistance, RawMolecule.CanonicalBranchNode.depth]
  · simp only [canonicalOriginalParent?, h, Option.some.injEq] at parent
    subst parent
    refine ⟨?_, by simp⟩
    simp [RawMolecule.CanonicalBranchNode.rule1bRootDistance, RawMolecule.CanonicalBranchNode.depth]

theorem ascending_node (target : Node) (p : Node) (parent : canonicalOriginalParent? target = some p)
    (root : Nat) (generated : CanonicalCenterTreeNode mol root target) :
    target ∈ mol.canonicalChildren p ∧ CanonicalCenterTreeNode mol root p := by
  cases generated with
  | root => simp [canonicalCenterRoot, canonicalOriginalParent?] at parent
  | child parentGenerated member =>
      have := canonicalOriginalParent?_eq_some_of_child parentGenerated member
      rw [this] at parent
      have eq := Option.some.inj parent
      subst eq
      exact ⟨member, parentGenerated⟩

theorem real_child_distance (mol : RawMolecule) (target n : Node)
    (child : n ∈ mol.canonicalChildren target) (real : n.provenance = .realAtom) :
    n.rule1bRootDistance = target.history.length := by
  rw [realAtom_rule1b n real, mol.canonicalChildren_history target n child]
  simp

theorem ring_child_distance (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (root : Nat) (target : Node)
    (generated : CanonicalCenterTreeNode mol root target) (p : Node)
    (parent : canonicalOriginalParent? target = some p) (n : Node)
    (child : n ∈ mol.canonicalChildren target) (distance : Nat)
    (ring : n.provenance = .ringDuplicate distance) :
    distance + 3 ≤ target.history.length := by
  obtain ⟨targetChild, pGenerated⟩ := ascending_node target p parent root generated
  obtain ⟨inHistory, distanceEq, neTarget⟩ := RawMolecule.canonicalChildren_ringDuplicate_data mol
    target n generated.history_head child distance ring
  have neParent : n.atom ≠ p.atom := by
    have := child_atom_ne_parent mol wellFormed single unique target n child
    rwa [child_parent mol p target targetChild] at this
  obtain ⟨index, firstIndex, distanceIndex⟩ :=
    RawMolecule.canonicalHistoryDistance_eq_index_of_mem target n.atom inHistory
  rw [distanceEq, distanceIndex]
  have lookup := RawMolecule.firstNatIndex?_eq_some_imp_getElem? n.atom _ index firstIndex
  have bound := RawMolecule.firstNatIndex?_eq_some_imp_lt_length n.atom _ index firstIndex
  rw [List.length_reverse] at bound
  rw [List.getElem?_reverse (by simpa using bound)] at lookup
  have historyEq := mol.canonicalChildren_history p target targetChild
  have pHead := pGenerated.history_head
  obtain ⟨rest, pHistory⟩ : ∃ rest, p.history = p.atom :: rest := by
    cases h : p.history with
    | nil => simp [h] at pHead
    | cons a rest =>
        simp only [h, List.head?_cons, Option.some.injEq] at pHead
        exact ⟨rest, by rw [pHead]⟩
  rw [historyEq, pHistory] at lookup bound ⊢
  simp only [List.length_cons] at lookup bound ⊢
  by_contra tooSmall
  have cases : rest.length + 1 + 1 - 1 - index = 0 ∨ rest.length + 1 + 1 - 1 - index = 1 := by omega
  rcases cases with zero | one
  · rw [zero] at lookup
    simp at lookup
    exact neTarget lookup.symm
  · rw [one] at lookup
    simp at lookup
    exact neParent lookup.symm

theorem phantom_distance (mol : RawMolecule) (target : Node) :
    (mol.canonicalPhantom target.atom (target.depth + 1)).rule1bRootDistance = target.depth + 1 := rfl

/-- The incoming-parent slot has a stored distance different from every other frame slot. -/
theorem ascending_distance_ne (_tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target)
    (roots : List Cursor) (frame : occurrenceLigandFrame? mol target = some roots)
    (P : Cursor) (asc : ascending? target = some P) :
    ∀ c ∈ roots, c ≠ P → P.node.rule1bRootDistance ≠ c.node.rule1bRootDistance := by
  obtain ⟨root, valid, path⟩ := reached
  have generated := generated_of_reachedFrom mol root target path
  simp only [ascending?, Option.map_eq_some_iff] at asc
  obtain ⟨p, parent, rfl⟩ := asc
  obtain ⟨pDistance, two⟩ := ascending_distance target p parent
  intro c member cNe
  simp only
  rw [pDistance]
  rcases frame_members mol target roots frame c member with slot | phantom
  · obtain ⟨nb, nbMem, rfl⟩ := mem_occurrenceLigandCursors slot
    rcases generated.neighbor_cases nbMem with ⟨nbGenerated, fromNb⟩ | child
    · exfalso
      apply cNe
      have := canonicalOriginalParent?_eq_some_of_child nbGenerated fromNb
      rw [parent] at this
      rw [Option.some.inj this]
    · rcases child_provenance mol wellFormed single target nb child with real | ⟨distance, ring⟩
      · simp only
        rw [real_child_distance mol target nb child real]
        omega
      · have bound := ring_child_distance mol wellFormed single unique root target generated p parent
          nb child distance ring
        show target.history.length - 2 ≠ nb.rule1bRootDistance
        unfold RawMolecule.CanonicalBranchNode.rule1bRootDistance
        simp only [ring]
        omega
  · rw [phantom]
    show target.history.length - 2 ≠
      (mol.canonicalPhantom target.atom (target.depth + 1)).rule1bRootDistance
    rw [phantom_distance]
    unfold RawMolecule.CanonicalBranchNode.depth
    omega

/-! ## Comparator symmetry under the twin exchange -/

theorem key_tie_twin (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target)
    (fuel : Nat) :
    comparePromotedOccurrenceBranchKeys
        (buildPromotedOccurrenceBranchKeyUnrestricted mol [] right.node.atom fuel left)
        (buildPromotedOccurrenceBranchKeyUnrestricted mol [] left.node.atom fuel right) = .eq ∧
    comparePromotedOccurrenceBranchKeys
        (buildPromotedOccurrenceBranchKeyUnrestricted mol [] right.node.atom fuel right)
        (buildPromotedOccurrenceBranchKeyUnrestricted mol [] left.node.atom fuel left) = .eq := by
  have lt := tc.leftTerminalCursor wellFormed single unique reached
  have rt := tc.rightTerminalCursor wellFormed single unique reached
  have ordinaryLR := ordinary_tie mol [] fuel left right lt rt tc.leftReal tc.rightReal tc.sameZ
    tc.sameDepth tc.sameMass rfl rfl
  have ordinaryRL := ordinary_tie mol [] fuel right left rt lt tc.rightReal tc.leftReal tc.sameZ.symm
    tc.sameDepth.symm tc.sameMass.symm rfl rfl
  have ordLR := compareOccurrenceBranchesUnrestricted_ordering_success_factors mol [] fuel left right
    _ ordinaryLR
  have ordRL := compareOccurrenceBranchesUnrestricted_ordering_success_factors mol [] fuel right left
    _ ordinaryRL
  have boundL := (mol.bondOrder_pos_endpoint_lt wellFormed tc.leftTerminal.1).2
  have boundR := (mol.bondOrder_pos_endpoint_lt wellFormed tc.rightTerminal.1).2
  have denseUnmarked := denseRule6Key_terminal_eq mol
    (promotedRule6BeforeUnrestricted mol [] right.node.atom fuel)
    (promotedRule6BeforeUnrestricted mol [] left.node.atom fuel) right.node.atom left.node.atom fuel
    left right lt rt boundR boundL (by
      simp [occurrenceRule6NodePriority, tc.distinct, tc.distinct.symm])
  have denseMarked := denseRule6Key_terminal_eq mol
    (promotedRule6BeforeUnrestricted mol [] right.node.atom fuel)
    (promotedRule6BeforeUnrestricted mol [] left.node.atom fuel) right.node.atom left.node.atom fuel
    right left rt lt boundR boundL (by simp [occurrenceRule6NodePriority])
  letI := compareDenseOccurrenceRule6Keys_transCmp
  constructor
  · unfold comparePromotedOccurrenceBranchKeys
    simp only [compareLex, Ordering.byKey, promotedKey_ordinary]
    rw [ordLR]
    simp only
    unfold buildPromotedOccurrenceBranchKeyUnrestricted
    simp only
    rw [denseUnmarked, orientedCmp_refl compareDenseOccurrenceRule6Keys]
    rfl
  · unfold comparePromotedOccurrenceBranchKeys
    simp only [compareLex, Ordering.byKey, promotedKey_ordinary]
    rw [ordRL]
    simp only
    unfold buildPromotedOccurrenceBranchKeyUnrestricted
    simp only
    rw [denseMarked, orientedCmp_refl compareDenseOccurrenceRule6Keys]
    rfl

theorem constitutional_tie_twin (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target)
    (fuel : Nat) :
    compareDenseRerootKeys (buildDenseRerootKey mol fuel left) (buildDenseRerootKey mol fuel right)
      = .eq := by
  have lt := tc.leftTerminalCursor wellFormed single unique reached
  have rt := tc.rightTerminalCursor wellFormed single unique reached
  exact compareCursorBranchAtAuthoritative?_success_dense_factors mol fuel left right .eq
    (constitutional_tie mol fuel left right lt rt tc.leftReal tc.rightReal tc.sameZ tc.sameDepth
      tc.sameMass)

/-- Key tie between a frame cursor under the right mark and its exchange under the left mark,
for every non-ascending slot. -/
theorem key_tie_nonAscending (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target)
    (fuel : Nat) (c : Cursor) (kind : c = left ∨ c = right ∨ Avoids mol tc.marks c) :
    comparePromotedOccurrenceBranchKeys
      (buildPromotedOccurrenceBranchKeyUnrestricted mol [] right.node.atom fuel c)
      (buildPromotedOccurrenceBranchKeyUnrestricted mol [] left.node.atom fuel (swapCursor left right c))
      = .eq := by
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  rcases kind with rfl | rfl | avoids
  · rw [swapCursor_left]
    exact (tc.key_tie_twin wellFormed single unique reached fuel).1
  · rw [swapCursor_right _ _ tc.cursor_ne]
    exact (tc.key_tie_twin wellFormed single unique reached fuel).2
  · have notLeft : c ≠ left := by
      intro same
      subst same
      exact avoids.self (by simp [marks])
    have notRight : c ≠ right := by
      intro same
      subst same
      exact avoids.self (by simp [marks])
    rw [swapCursor_other _ _ _ notLeft notRight,
      promotedKey_congr mol tc.marks (tc.marks_inRange wellFormed) [] right.node.atom left.node.atom
        (by simp [marks]) (by simp [marks]) fuel c avoids]
    exact orientedCmp_refl comparePromotedOccurrenceBranchKeys _

/-- **Comparator symmetry.** Exchanging the twin marks and the twin cursors leaves every actual
frame comparison unchanged. -/
theorem symmetry (tc : TwinCenter mol target left right) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique) (reached : Reached mol target)
    (roots : List Cursor) (frame : occurrenceLigandFrame? mol target = some roots) (fuel : Nat) :
    ∀ a ∈ roots, ∀ b ∈ roots,
      cursorCompare mol [] right.node.atom fuel a b =
        cursorCompare mol [] left.node.atom fuel (swapCursor left right a) (swapCursor left right b) := by
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  letI := compareDenseRerootKeys_transCmp
  have classify := tc.classify wellFormed single unique reached roots frame
  have constitutional := tc.constitutional_tie_twin wellFormed single unique reached fuel
  have constitutional' : compareDenseRerootKeys (buildDenseRerootKey mol fuel right)
      (buildDenseRerootKey mol fuel left) = .eq := by
    rw [Std.OrientedCmp.eq_swap (cmp := compareDenseRerootKeys), constitutional]
    rfl
  have swapMem : ∀ c ∈ roots, swapCursor left right c ∈ roots := by
    intro c member
    have leftMem : left ∈ roots :=
      LocalizedMarkedTerminalMarkedRefusal.physical_slots_mem_frame mol target roots frame left
        tc.leftSlot
    have rightMem : right ∈ roots :=
      LocalizedMarkedTerminalMarkedRefusal.physical_slots_mem_frame mol target roots frame right
        tc.rightSlot
    by_cases hl : c = left
    · rw [hl, swapCursor_left]; exact rightMem
    · by_cases hr : c = right
      · rw [hr, swapCursor_right _ _ tc.cursor_ne]; exact leftMem
      · rw [swapCursor_other _ _ _ hl hr]; exact member
  -- constitutional tie between a slot and its exchange
  have constitutionalSwap : ∀ c ∈ roots, c = left ∨ c = right ∨ Avoids mol tc.marks c →
      compareDenseRerootKeys (buildDenseRerootKey mol fuel c)
        (buildDenseRerootKey mol fuel (swapCursor left right c)) = .eq := by
    intro c _ kind
    rcases kind with rfl | rfl | avoids
    · rw [swapCursor_left]; exact constitutional
    · rw [swapCursor_right _ _ tc.cursor_ne]; exact constitutional'
    · have notLeft : c ≠ left := by
        intro same; subst same; exact avoids.self (by simp [marks])
      have notRight : c ≠ right := by
        intro same; subst same; exact avoids.self (by simp [marks])
      rw [swapCursor_other _ _ _ notLeft notRight]
      exact orientedCmp_refl compareDenseRerootKeys _
  -- non-ascending slots: compared through tied keys
  have keyRoute : ∀ a ∈ roots, ∀ b ∈ roots,
      (a = left ∨ a = right ∨ Avoids mol tc.marks a) →
      (b = left ∨ b = right ∨ Avoids mol tc.marks b) →
      cursorCompare mol [] right.node.atom fuel a b =
        cursorCompare mol [] left.node.atom fuel (swapCursor left right a) (swapCursor left right b) := by
    intro a _ b _ ca cb
    have ta := tc.key_tie_nonAscending wellFormed single unique reached fuel a ca
    have tb := tc.key_tie_nonAscending wellFormed single unique reached fuel b cb
    unfold cursorCompare
    rw [transCmp_congr_left comparePromotedOccurrenceBranchKeys ta,
      transCmp_congr_right comparePromotedOccurrenceBranchKeys tb]
  -- the ascending slot is fixed by the exchange and compared through constitutional keys
  have ascFixed : ∀ P, ascending? target = some P → ¬ (P = left ∨ P = right ∨ Avoids mol tc.marks P) →
      swapCursor left right P = P := by
    intro P _ notNon
    have notLeft : P ≠ left := fun h => notNon (Or.inl h)
    have notRight : P ≠ right := fun h => notNon (Or.inr (Or.inl h))
    exact swapCursor_other _ _ _ notLeft notRight
  -- `a` is the ascending slot (and not twin-free), `b` is not ascending
  have ascCaseA : ∀ a ∈ roots, ∀ b ∈ roots, a ≠ b → ascending? target = some a →
      ¬ (a = left ∨ a = right ∨ Avoids mol tc.marks a) →
      (b = left ∨ b = right ∨ Avoids mol tc.marks b) →
      cursorCompare mol [] right.node.atom fuel a b =
        cursorCompare mol [] left.node.atom fuel (swapCursor left right a) (swapCursor left right b) := by
    intro a _ b bMem same ascA nonA nonB
    have fixedA := ascFixed a ascA nonA
    have distA := tc.ascending_distance_ne wellFormed single unique reached roots frame a ascA b bMem
      (Ne.symm same)
    have swapB := swapMem b bMem
    have swapBNe : swapCursor left right b ≠ a := by
      intro h
      have := congrArg (swapCursor left right) h
      rw [swapCursor_involutive, fixedA] at this
      exact same this.symm
    have distA' := tc.ascending_distance_ne wellFormed single unique reached roots frame a ascA _
      swapB swapBNe
    rw [fixedA, cursorCompare_of_distance mol [] right.node.atom fuel a b distA,
      cursorCompare_of_distance mol [] left.node.atom fuel a _ distA',
      transCmp_congr_right compareDenseRerootKeys (constitutionalSwap b bMem nonB)]
  -- `b` is the ascending slot (and not twin-free), `a` is not ascending
  have ascCaseB : ∀ a ∈ roots, ∀ b ∈ roots, a ≠ b → ascending? target = some b →
      ¬ (b = left ∨ b = right ∨ Avoids mol tc.marks b) →
      (a = left ∨ a = right ∨ Avoids mol tc.marks a) →
      cursorCompare mol [] right.node.atom fuel a b =
        cursorCompare mol [] left.node.atom fuel (swapCursor left right a) (swapCursor left right b) := by
    intro a aMem b _ same ascB nonB nonA
    have fixedB := ascFixed b ascB nonB
    have distB := tc.ascending_distance_ne wellFormed single unique reached roots frame b ascB a aMem
      same
    have swapA := swapMem a aMem
    have swapANe : swapCursor left right a ≠ b := by
      intro h
      have := congrArg (swapCursor left right) h
      rw [swapCursor_involutive, fixedB] at this
      exact same this
    have distB' := tc.ascending_distance_ne wellFormed single unique reached roots frame b ascB _
      swapA swapANe
    rw [fixedB, cursorCompare_of_distance mol [] right.node.atom fuel a b (Ne.symm distB),
      cursorCompare_of_distance mol [] left.node.atom fuel _ b (Ne.symm distB'),
      transCmp_congr_left compareDenseRerootKeys (constitutionalSwap a aMem nonA)]
  intro a aMem b bMem
  by_cases same : a = b
  · subst same
    unfold cursorCompare
    rw [orientedCmp_refl comparePromotedOccurrenceBranchKeys,
      orientedCmp_refl comparePromotedOccurrenceBranchKeys]
  have ca : (a = left ∨ a = right ∨ Avoids mol tc.marks a) ∨ ascending? target = some a := by
    rcases classify a aMem with h | h | h | h <;> tauto
  have cb : (b = left ∨ b = right ∨ Avoids mol tc.marks b) ∨ ascending? target = some b := by
    rcases classify b bMem with h | h | h | h <;> tauto
  by_cases nonA : a = left ∨ a = right ∨ Avoids mol tc.marks a
  · by_cases nonB : b = left ∨ b = right ∨ Avoids mol tc.marks b
    · exact keyRoute a aMem b bMem nonA nonB
    · rcases cb with nonB' | ascB
      · exact absurd nonB' nonB
      · exact ascCaseB a aMem b bMem same ascB nonB nonA
  · rcases ca with nonA' | ascA
    · exact absurd nonA' nonA
    · by_cases nonB : b = left ∨ b = right ∨ Avoids mol tc.marks b
      · exact ascCaseA a aMem b bMem same ascA nonA nonB
      · rcases cb with nonB' | ascB
        · exact absurd nonB' nonB
        · exfalso
          rw [ascA] at ascB
          exact same (Option.some.inj ascB)

end TwinCenter

end TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeFrame
