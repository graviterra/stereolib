import TetraStereo.OneCenter.CIPCycleCut
import TetraStereo.OneCenter.Euclidean

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

section

open TetrahedralGeometry

/-!
This module is the next frontier layer above the current descriptor engine.  It does not claim
to finish the full IUPAC CIP formalization; instead it gives the verified scaffolding we need to
replace the present simplified key with a rule-traced, cycle-aware, conformation-aware engine.
-/

/-- Rule families that a full CIP implementation must be able to record in a comparison trace. -/
inductive CIPRuleFamily where
  | atomicNumber
  | isotopeMass
  | duplicateAtom
  | multipleBondExpansion
  | cycleDuplicateLeaf
  | frontierExhaustion
  | descriptorSubrule
  | doubleBondGeometry
  | stereogenicUnitKind
  | likeUnlikeDescriptorPair
  | pseudoasymmetricDescriptor
  | pseudoasymmetricTiebreak
  deriving DecidableEq, Repr

/-- One comparison step in a rule-by-rule CIP trace. -/
structure CIPRuleDecision where
  rule : CIPRuleFamily
  outcome : Ordering
  deriving DecidableEq, Repr

namespace CIPRuleDecision

/-- A rule decision is decisive exactly when it is not a tie. -/
def Decisive (d : CIPRuleDecision) : Prop :=
  d.outcome ≠ Ordering.eq

end CIPRuleDecision

/-- Lexicographic evaluation of a rule trace: the first non-`eq` decision wins. -/
def cipTraceOutcome : List CIPRuleDecision → Ordering
  | [] => Ordering.eq
  | d :: ds => if d.outcome = Ordering.eq then cipTraceOutcome ds else d.outcome

@[simp] theorem cipTraceOutcome_nil :
    cipTraceOutcome [] = Ordering.eq :=
  rfl

@[simp] theorem cipTraceOutcome_cons_eq (d : CIPRuleDecision) (ds : List CIPRuleDecision)
    (h : d.outcome = Ordering.eq) :
    cipTraceOutcome (d :: ds) = cipTraceOutcome ds := by
  simp [cipTraceOutcome, h]

theorem cipTraceOutcome_cons_decisive (d : CIPRuleDecision) (ds : List CIPRuleDecision)
    (h : d.Decisive) :
    cipTraceOutcome (d :: ds) = d.outcome := by
  have hne : d.outcome ≠ Ordering.eq := h
  simp [cipTraceOutcome, hne]

@[simp] theorem cipTraceOutcome_cons_lt (rule : CIPRuleFamily) (ds : List CIPRuleDecision) :
    cipTraceOutcome ({ rule := rule, outcome := Ordering.lt } :: ds) = Ordering.lt := by
  simp [cipTraceOutcome]

@[simp] theorem cipTraceOutcome_cons_gt (rule : CIPRuleFamily) (ds : List CIPRuleDecision) :
    cipTraceOutcome ({ rule := rule, outcome := Ordering.gt } :: ds) = Ordering.gt := by
  simp [cipTraceOutcome]

theorem cipTraceOutcome_append_of_left_eq :
    ∀ {left right : List CIPRuleDecision}, cipTraceOutcome left = Ordering.eq →
      cipTraceOutcome (left ++ right) = cipTraceOutcome right
  | [], _, _ => rfl
  | d :: ds, right, h => by
      by_cases hd : d.outcome = Ordering.eq
      · have hds : cipTraceOutcome ds = Ordering.eq := by
          simpa [cipTraceOutcome, hd] using h
        simp [hd, cipTraceOutcome_append_of_left_eq hds]
      · have hfalse : False := by
          simp [cipTraceOutcome, hd] at h
        exact False.elim hfalse

theorem cipTraceOutcome_eq_of_forall_eq :
    ∀ {trace : List CIPRuleDecision},
      (∀ d, d ∈ trace → d.outcome = Ordering.eq) →
        cipTraceOutcome trace = Ordering.eq
  | [], _ => rfl
  | d :: ds, h => by
      have hd : d.outcome = Ordering.eq := h d (by simp)
      have hds : ∀ e, e ∈ ds → e.outcome = Ordering.eq := by
        intro e he
        exact h e (by simp [he])
      simp [cipTraceOutcome, hd, cipTraceOutcome_eq_of_forall_eq hds]

/-- A proof-carrying CIP comparison result. -/
structure CIPTraceCertificate where
  trace : List CIPRuleDecision
  outcome : Ordering
  sound : cipTraceOutcome trace = outcome

namespace CIPTraceCertificate

/-- The canonical certificate obtained by evaluating a trace. -/
def ofTrace (trace : List CIPRuleDecision) : CIPTraceCertificate where
  trace := trace
  outcome := cipTraceOutcome trace
  sound := rfl

@[simp] theorem ofTrace_outcome (trace : List CIPRuleDecision) :
    (ofTrace trace).outcome = cipTraceOutcome trace :=
  rfl

end CIPTraceCertificate

/-! ### Cycle-expansion states for arbitrary cyclic graphs -/

/-- A branch node in an arbitrary CIP expansion.  The `history` is stored with the current atom at
the head, followed by older atoms on the branch. -/
structure CIPExpansionNode (V : Type*) where
  current : V
  history : List V
  current_head : history.head? = some current

namespace CIPExpansionNode

variable {V : Type*}

/-- The root expansion node at an atom. -/
def root (v : V) : CIPExpansionNode V where
  current := v
  history := [v]
  current_head := rfl

/-- The previous atoms on the branch, excluding the current atom. -/
def previous (n : CIPExpansionNode V) : List V :=
  n.history.drop 1

/-- Branch depth measured by the number of previous atoms. -/
def depth (n : CIPExpansionNode V) : ℕ :=
  n.previous.length

/-- The immediate predecessor on the branch, if the node is not a root. -/
def parent? (n : CIPExpansionNode V) : Option V :=
  n.previous.head?

/-- The finite set of previous atoms on the branch. -/
def seenFinset [DecidableEq V] (n : CIPExpansionNode V) : Finset V :=
  n.previous.toFinset

/-- The current atom is a duplicate when it has already appeared earlier on this branch. -/
def IsDuplicate [DecidableEq V] (n : CIPExpansionNode V) : Prop :=
  n.current ∈ n.previous

/-- Convert a non-root branch node to the existing cycle-cut `CIPState` representation. -/
def toCIPState? [DecidableEq V] (n : CIPExpansionNode V) :
    Option (MoleculeGraph.CIPState V) :=
  n.parent?.map fun parent => ⟨parent, n.current, n.seenFinset⟩

/-- Extend a branch by one atom, allowing arbitrary cycle revisits. -/
def extend (n : CIPExpansionNode V) (next : V) : CIPExpansionNode V where
  current := next
  history := next :: n.history
  current_head := rfl

@[simp] theorem root_current (v : V) :
    (root v).current = v :=
  rfl

@[simp] theorem root_history (v : V) :
    (root v).history = [v] :=
  rfl

@[simp] theorem previous_root (v : V) :
    (root v).previous = [] := by
  simp [previous, root]

@[simp] theorem depth_root (v : V) :
    (root v).depth = 0 := by
  simp [depth]

@[simp] theorem parent?_root (v : V) :
    (root v).parent? = none := by
  simp [parent?, previous]

@[simp] theorem seenFinset_root [DecidableEq V] (v : V) :
    (root v).seenFinset = ∅ := by
  simp [seenFinset]

@[simp] theorem not_isDuplicate_root [DecidableEq V] (v : V) :
    ¬ (root v).IsDuplicate := by
  simp [IsDuplicate]

@[simp] theorem toCIPState?_root [DecidableEq V] (v : V) :
    (root v).toCIPState? = none := by
  simp [toCIPState?]

@[simp] theorem extend_current (n : CIPExpansionNode V) (next : V) :
    (n.extend next).current = next :=
  rfl

@[simp] theorem extend_history (n : CIPExpansionNode V) (next : V) :
    (n.extend next).history = next :: n.history :=
  rfl

@[simp] theorem previous_extend (n : CIPExpansionNode V) (next : V) :
    (n.extend next).previous = n.history := by
  simp [previous, extend]

@[simp] theorem depth_extend (n : CIPExpansionNode V) (next : V) :
    (n.extend next).depth = n.history.length := by
  simp [depth]

@[simp] theorem parent?_extend (n : CIPExpansionNode V) (next : V) :
    (n.extend next).parent? = some n.current := by
  simp [parent?, n.current_head]

@[simp] theorem seenFinset_extend [DecidableEq V] (n : CIPExpansionNode V) (next : V) :
    (n.extend next).seenFinset = n.history.toFinset := by
  simp [seenFinset]

theorem isDuplicate_extend_iff [DecidableEq V] (n : CIPExpansionNode V) (next : V) :
    (n.extend next).IsDuplicate ↔ next ∈ n.history := by
  simp [IsDuplicate]

theorem isDuplicate_iff_mem_seenFinset [DecidableEq V] (n : CIPExpansionNode V) :
    n.IsDuplicate ↔ n.current ∈ n.seenFinset := by
  simp [IsDuplicate, seenFinset]

@[simp] theorem toCIPState?_extend [DecidableEq V] (n : CIPExpansionNode V) (next : V) :
    (n.extend next).toCIPState? =
      some
        ({ parent := n.current, current := next, seen := n.history.toFinset } :
          MoleculeGraph.CIPState V) := by
  simp [toCIPState?]

end CIPExpansionNode

namespace MoleculeGraph

open CIPExpansionNode

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership in the public raw CIP neighbor-multiset is exactly molecular adjacency. -/
theorem mem_rawCIPNeighborListWithMultiplicity_iff (m : MoleculeGraph V) {v u : V} :
    u ∈ m.rawCIPNeighborListWithMultiplicity v ↔ m.Adj v u := by
  constructor
  · intro h
    simp [rawCIPNeighborListWithMultiplicity, MoleculeGraph.Adj] at h
    exact h.1
  · intro h
    simp [rawCIPNeighborListWithMultiplicity, MoleculeGraph.Adj]
    exact ⟨h, Nat.ne_of_gt h⟩

/-- Consecutive atoms in a branch history are joined by molecular bonds. -/
def BranchHistoryBonded (m : MoleculeGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => m.Adj a b ∧ m.BranchHistoryBonded (b :: rest)

/-- A branch node is a genuine molecular walk when its stored history is bond-connected. -/
def BranchBonded (m : MoleculeGraph V) (n : CIPExpansionNode V) : Prop :=
  m.BranchHistoryBonded n.history

/-- Every node in a frontier is a genuine molecular walk. -/
def FrontierBranchBonded (m : MoleculeGraph V) (frontier : List (CIPExpansionNode V)) : Prop :=
  ∀ n, n ∈ frontier → m.BranchBonded n

@[simp] theorem branchHistoryBonded_nil (m : MoleculeGraph V) :
    m.BranchHistoryBonded [] :=
  trivial

@[simp] theorem branchHistoryBonded_singleton (m : MoleculeGraph V) (v : V) :
    m.BranchHistoryBonded [v] :=
  trivial

@[simp] theorem branchBonded_root (m : MoleculeGraph V) (v : V) :
    m.BranchBonded (CIPExpansionNode.root v) := by
  simp [BranchBonded]

theorem branchBonded_extend (m : MoleculeGraph V) {n : CIPExpansionNode V} {next : V}
    (hn : m.BranchBonded n) (hadj : m.Adj next n.current) :
    m.BranchBonded (n.extend next) := by
  unfold BranchBonded at hn ⊢
  cases hhistory : n.history with
  | nil =>
      have hbad := n.current_head
      simp [hhistory] at hbad
  | cons head tail =>
      have hhead : head = n.current := by
        simpa [hhistory] using n.current_head
      subst head
      simpa [CIPExpansionNode.extend, BranchHistoryBonded, hhistory, hadj] using hn

/-- All one-step graph expansions from a branch node.  This intentionally does not forbid
revisiting atoms; duplicates are detected by `CIPExpansionNode.IsDuplicate`. -/
noncomputable def cipExpansionChildren (m : MoleculeGraph V) (n : CIPExpansionNode V) :
    List (CIPExpansionNode V) :=
  (m.neighborFinset n.current).toList.map fun next => n.extend next

/-- The cycle-cut version of `cipExpansionChildren`: duplicate nodes are leaves. -/
noncomputable def cipCycleCutExpansionChildren (m : MoleculeGraph V) (n : CIPExpansionNode V) :
    List (CIPExpansionNode V) :=
  by
    classical
    exact if n.IsDuplicate then [] else m.cipExpansionChildren n

/-- A bond-order-aware branch expansion: neighbors are repeated with bond multiplicity and the
immediate parent occurrence is removed once, matching the raw CIP expansion convention. -/
noncomputable def cipMultiplicityExpansionChildren (m : MoleculeGraph V) (n : CIPExpansionNode V) :
    List (CIPExpansionNode V) :=
  match n.parent? with
  | none =>
      (m.rawCIPNeighborListWithMultiplicity n.current).map fun next => n.extend next
  | some parent =>
      (m.rawCIPChildren parent n.current).map fun next => n.extend next

/-- Cycle-cut, bond-order-aware branch expansion: duplicate atoms are leaves. -/
noncomputable def cipCycleCutMultiplicityExpansionChildren (m : MoleculeGraph V) (n : CIPExpansionNode V) :
    List (CIPExpansionNode V) :=
  by
    classical
    exact if n.IsDuplicate then [] else m.cipMultiplicityExpansionChildren n

/-- One breadth-first layer of the bond-order-aware branch expansion. -/
noncomputable def cipMultiplicityNextFrontier (m : MoleculeGraph V) (frontier : List (CIPExpansionNode V)) :
    List (CIPExpansionNode V) :=
  frontier.flatMap fun n => m.cipMultiplicityExpansionChildren n

/-- One breadth-first layer of the cycle-cut, bond-order-aware branch expansion. -/
noncomputable def cipCycleCutMultiplicityNextFrontier (m : MoleculeGraph V)
    (frontier : List (CIPExpansionNode V)) :
    List (CIPExpansionNode V) :=
  frontier.flatMap fun n => m.cipCycleCutMultiplicityExpansionChildren n

/-- Iterate the bond-order-aware expansion for a bounded number of layers. -/
noncomputable def cipMultiplicityFrontier (m : MoleculeGraph V) :
    ℕ → List (CIPExpansionNode V) → List (CIPExpansionNode V)
  | 0, frontier => frontier
  | k + 1, frontier => m.cipMultiplicityFrontier k (m.cipMultiplicityNextFrontier frontier)

/-- Iterate the cycle-cut, bond-order-aware expansion for a bounded number of layers. -/
noncomputable def cipCycleCutMultiplicityFrontier (m : MoleculeGraph V) :
    ℕ → List (CIPExpansionNode V) → List (CIPExpansionNode V)
  | 0, frontier => frontier
  | k + 1, frontier =>
      m.cipCycleCutMultiplicityFrontier k (m.cipCycleCutMultiplicityNextFrontier frontier)

theorem mem_cipExpansionChildren_iff (m : MoleculeGraph V) (n : CIPExpansionNode V)
    (child : CIPExpansionNode V) :
    child ∈ m.cipExpansionChildren n ↔
      ∃ next, next ∈ m.neighborFinset n.current ∧ child = n.extend next := by
  simp [cipExpansionChildren, eq_comm]

theorem cipExpansionChild_bonded (m : MoleculeGraph V) {n child : CIPExpansionNode V}
    (hchild : child ∈ m.cipExpansionChildren n) :
    m.Adj n.current child.current := by
  rcases (m.mem_cipExpansionChildren_iff n child).1 hchild with ⟨next, hnext, rfl⟩
  simpa using hnext

theorem cipExpansionChild_duplicate_iff_history (m : MoleculeGraph V)
    {n child : CIPExpansionNode V}
    (hchild : child ∈ m.cipExpansionChildren n) :
    child.IsDuplicate ↔ child.current ∈ n.history := by
  rcases (m.mem_cipExpansionChildren_iff n child).1 hchild with ⟨next, _hnext, rfl⟩
  exact CIPExpansionNode.isDuplicate_extend_iff n next

theorem exists_extend_of_mem_cipMultiplicityExpansionChildren (m : MoleculeGraph V)
    {n child : CIPExpansionNode V}
    (hchild : child ∈ m.cipMultiplicityExpansionChildren n) :
    ∃ next, child = n.extend next := by
  unfold cipMultiplicityExpansionChildren at hchild
  split at hchild
  · rcases List.mem_map.1 hchild with ⟨next, _hnext, rfl⟩
    exact ⟨next, rfl⟩
  · rcases List.mem_map.1 hchild with ⟨next, _hnext, rfl⟩
    exact ⟨next, rfl⟩

theorem cipMultiplicityExpansionChild_bonded (m : MoleculeGraph V)
    {n child : CIPExpansionNode V}
    (hchild : child ∈ m.cipMultiplicityExpansionChildren n) :
    m.Adj n.current child.current := by
  unfold cipMultiplicityExpansionChildren at hchild
  split at hchild
  · rcases List.mem_map.1 hchild with ⟨next, hnext, rfl⟩
    exact (m.mem_rawCIPNeighborListWithMultiplicity_iff).1 hnext
  · rcases List.mem_map.1 hchild with ⟨next, hnext, rfl⟩
    exact (m.mem_rawCIPNeighborListWithMultiplicity_iff).1
      (List.mem_of_mem_erase (by simpa [rawCIPChildren] using hnext))

theorem cipMultiplicityExpansionChild_duplicate_iff_history (m : MoleculeGraph V)
    {n child : CIPExpansionNode V}
    (hchild : child ∈ m.cipMultiplicityExpansionChildren n) :
    child.IsDuplicate ↔ child.current ∈ n.history := by
  rcases m.exists_extend_of_mem_cipMultiplicityExpansionChildren hchild with ⟨next, rfl⟩
  exact CIPExpansionNode.isDuplicate_extend_iff n next

theorem branchBonded_of_mem_cipMultiplicityExpansionChildren (m : MoleculeGraph V)
    {n child : CIPExpansionNode V}
    (hn : m.BranchBonded n) (hchild : child ∈ m.cipMultiplicityExpansionChildren n) :
    m.BranchBonded child := by
  rcases m.exists_extend_of_mem_cipMultiplicityExpansionChildren hchild with ⟨next, rfl⟩
  have hadjCurrentNext : m.Adj n.current next := by
    have hbond := m.cipMultiplicityExpansionChild_bonded
      (child := n.extend next) hchild
    simpa using hbond
  have hadjNextCurrent : m.Adj next n.current := (m.adj_symm).1 hadjCurrentNext
  exact m.branchBonded_extend hn hadjNextCurrent

theorem branchBonded_of_mem_cipCycleCutMultiplicityExpansionChildren
    (m : MoleculeGraph V) {n child : CIPExpansionNode V}
    (hn : m.BranchBonded n)
    (hchild : child ∈ m.cipCycleCutMultiplicityExpansionChildren n) :
    m.BranchBonded child := by
  classical
  by_cases hdup : n.IsDuplicate
  · simp [cipCycleCutMultiplicityExpansionChildren, hdup] at hchild
  · have hchild' : child ∈ m.cipMultiplicityExpansionChildren n := by
      simpa [cipCycleCutMultiplicityExpansionChildren, hdup] using hchild
    exact m.branchBonded_of_mem_cipMultiplicityExpansionChildren hn hchild'

theorem frontierBranchBonded_cipMultiplicityNextFrontier (m : MoleculeGraph V)
    {frontier : List (CIPExpansionNode V)}
    (hfront : m.FrontierBranchBonded frontier) :
    m.FrontierBranchBonded (m.cipMultiplicityNextFrontier frontier) := by
  intro child hchild
  rcases (List.mem_flatMap).1 (by simpa [cipMultiplicityNextFrontier] using hchild) with
    ⟨n, hnFrontier, hchildN⟩
  exact m.branchBonded_of_mem_cipMultiplicityExpansionChildren (hfront n hnFrontier) hchildN

theorem frontierBranchBonded_cipCycleCutMultiplicityNextFrontier (m : MoleculeGraph V)
    {frontier : List (CIPExpansionNode V)}
    (hfront : m.FrontierBranchBonded frontier) :
    m.FrontierBranchBonded (m.cipCycleCutMultiplicityNextFrontier frontier) := by
  intro child hchild
  rcases (List.mem_flatMap).1 (by simpa [cipCycleCutMultiplicityNextFrontier] using hchild) with
    ⟨n, hnFrontier, hchildN⟩
  exact m.branchBonded_of_mem_cipCycleCutMultiplicityExpansionChildren
    (hfront n hnFrontier) hchildN

theorem frontierBranchBonded_cipMultiplicityFrontier (m : MoleculeGraph V) :
    ∀ k {frontier : List (CIPExpansionNode V)}, m.FrontierBranchBonded frontier →
      m.FrontierBranchBonded (m.cipMultiplicityFrontier k frontier)
  | 0, _frontier, hfront => by
      simpa [cipMultiplicityFrontier] using hfront
  | k + 1, frontier, hfront => by
      simpa [cipMultiplicityFrontier] using
        m.frontierBranchBonded_cipMultiplicityFrontier k
          (m.frontierBranchBonded_cipMultiplicityNextFrontier hfront)

theorem frontierBranchBonded_cipCycleCutMultiplicityFrontier (m : MoleculeGraph V) :
    ∀ k {frontier : List (CIPExpansionNode V)}, m.FrontierBranchBonded frontier →
      m.FrontierBranchBonded (m.cipCycleCutMultiplicityFrontier k frontier)
  | 0, _frontier, hfront => by
      simpa [cipCycleCutMultiplicityFrontier] using hfront
  | k + 1, frontier, hfront => by
      simpa [cipCycleCutMultiplicityFrontier] using
        m.frontierBranchBonded_cipCycleCutMultiplicityFrontier k
          (m.frontierBranchBonded_cipCycleCutMultiplicityNextFrontier hfront)

@[simp] theorem cipCycleCutExpansionChildren_of_duplicate (m : MoleculeGraph V)
    {n : CIPExpansionNode V} (hdup : n.IsDuplicate) :
    m.cipCycleCutExpansionChildren n = [] := by
  classical
  simp [cipCycleCutExpansionChildren, hdup]

@[simp] theorem cipCycleCutExpansionChildren_of_not_duplicate (m : MoleculeGraph V)
    {n : CIPExpansionNode V} (hdup : ¬ n.IsDuplicate) :
    m.cipCycleCutExpansionChildren n = m.cipExpansionChildren n := by
  classical
  simp [cipCycleCutExpansionChildren, hdup]

@[simp] theorem cipCycleCutMultiplicityExpansionChildren_of_duplicate (m : MoleculeGraph V)
    {n : CIPExpansionNode V} (hdup : n.IsDuplicate) :
    m.cipCycleCutMultiplicityExpansionChildren n = [] := by
  classical
  simp [cipCycleCutMultiplicityExpansionChildren, hdup]

@[simp] theorem cipCycleCutMultiplicityExpansionChildren_of_not_duplicate (m : MoleculeGraph V)
    {n : CIPExpansionNode V} (hdup : ¬ n.IsDuplicate) :
    m.cipCycleCutMultiplicityExpansionChildren n = m.cipMultiplicityExpansionChildren n := by
  classical
  simp [cipCycleCutMultiplicityExpansionChildren, hdup]

end MoleculeGraph

/-! ### Conformation-level geometry -/

/-- A molecular conformation assigns a point in Euclidean 3-space to each atom. -/
abbrev MolecularConformation (V : Type*) :=
  V → EuclideanSpace ℝ (Fin 3)

namespace MolecularConformation

variable {V : Type*}

/-- Apply a rigid Euclidean motion to every atom of a conformation. -/
noncomputable def mapEuclidean (μ : EuclideanMotion) (c : MolecularConformation V) :
    MolecularConformation V :=
  fun v => μ.applyPoint (c v)

/-- Proper rigid equivalence of molecular conformations. -/
def ProperEquivalent (c d : MolecularConformation V) : Prop :=
  ∃ μ : OrientationPreservingEuclideanMotion, ∀ v, μ.1.applyPoint (c v) = d v

/-- Full rigid equivalence of molecular conformations, allowing orientation reversal. -/
def EuclideanEquivalent (c d : MolecularConformation V) : Prop :=
  ∃ μ : EuclideanMotion, ∀ v, μ.applyPoint (c v) = d v

/-- `d` is an orientation-reversing rigid image of `c`. -/
def ImproperImage (c d : MolecularConformation V) : Prop :=
  ∃ μ : OrientationReversingEuclideanMotion, ∀ v, μ.1.applyPoint (c v) = d v

/-- Conformation-level achirality: an improper image is also properly congruent to the original. -/
def Achiral (c : MolecularConformation V) : Prop :=
  ∃ d, ImproperImage c d ∧ ProperEquivalent c d

/-- Conformation-level chirality is the negation of conformation-level achirality. -/
def Chiral (c : MolecularConformation V) : Prop :=
  ¬ Achiral c

theorem properEquivalent_refl (c : MolecularConformation V) :
    ProperEquivalent c c := by
  refine ⟨1, ?_⟩
  intro v
  change (1 : EuclideanMotion).applyPoint (c v) = c v
  simp

theorem euclideanEquivalent_refl (c : MolecularConformation V) :
    EuclideanEquivalent c c := by
  refine ⟨1, ?_⟩
  intro v
  simp

theorem properEquivalent_symm {c d : MolecularConformation V}
    (h : ProperEquivalent c d) :
    ProperEquivalent d c := by
  rcases h with ⟨μ, hμ⟩
  refine ⟨μ⁻¹, ?_⟩
  intro v
  change (μ.1⁻¹).applyPoint (d v) = c v
  calc
    (μ.1⁻¹).applyPoint (d v)
        = (μ.1⁻¹).applyPoint (μ.1.applyPoint (c v)) := by rw [hμ v]
    _ = ((μ.1⁻¹) * μ.1).applyPoint (c v) := by
          rw [EuclideanMotion.applyPoint_mul]
    _ = c v := by simp

theorem properEquivalent_trans {c d e : MolecularConformation V}
    (hcd : ProperEquivalent c d) (hde : ProperEquivalent d e) :
    ProperEquivalent c e := by
  rcases hcd with ⟨μ, hμ⟩
  rcases hde with ⟨ν, hν⟩
  refine ⟨ν * μ, ?_⟩
  intro v
  change (ν.1 * μ.1).applyPoint (c v) = e v
  rw [EuclideanMotion.applyPoint_mul, hμ v, hν v]

/-- A conformational ensemble is a selected set of allowed molecular conformations. -/
structure Ensemble (V : Type*) where
  allowed : Set (MolecularConformation V)

namespace Ensemble

variable {V : Type*}

/-- The ensemble is closed under proper rigid motions. -/
def ClosedUnderProperMotions (E : Ensemble V) : Prop :=
  ∀ c, c ∈ E.allowed → ∀ μ : OrientationPreservingEuclideanMotion,
    MolecularConformation.mapEuclidean μ.1 c ∈ E.allowed

/-- Achirality inside an ensemble: the improper witness and proper congruence target both stay
inside the allowed conformational space. -/
def AchiralWithin (E : Ensemble V) (c : MolecularConformation V) : Prop :=
  c ∈ E.allowed ∧ ∃ d, d ∈ E.allowed ∧ ImproperImage c d ∧ ProperEquivalent c d

/-- Chirality inside an ensemble. -/
def ChiralWithin (E : Ensemble V) (c : MolecularConformation V) : Prop :=
  c ∈ E.allowed ∧ ¬ E.AchiralWithin c

end Ensemble

end MolecularConformation

end

end OneCenter
end TetraStereo
