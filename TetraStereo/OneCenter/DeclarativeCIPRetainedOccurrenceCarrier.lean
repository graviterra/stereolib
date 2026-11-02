








import TetraStereo.OneCenter.DeclarativeCIP
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.KernelOnly
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Retained outer-root occurrence carrier

`FaithfulExactExpansion` rebuilds a ligand arm from a fresh `rootFromEdge` history. On a cyclic
single-bond graph that is the right object only for the outer-root arm. A later retained cursor
keeps the original outer digraph: duplicate provenance and root distances stay those of the
outer walk, and the parent direction is the carrier edge already present, not a new chemical
child computed from the cursor.

This module defines that carrier directly from `MoleculeGraph` adjacency.

* A real node is a simple adjacency path that starts at a fixed outer root.
* A ring node is one terminal closure: the prefix is simple, the final atom is adjacent,
  already occurs on the prefix, and is not the immediate predecessor.
* The child relation is prefix extension. The resulting digraph is a finite tree for every
  finite molecule, whether or not the molecule has a cycle.
* `retainedArm` reroots that whole tree at an occurrence. Edges point away from the occurrence,
  so the original parent is no longer a parent: on a real occurrence it is reattached as a
  child, and its subtree remains. This is the uncut full reroot. It is not the ligand arm
  entered from that predecessor. `FullRerootFaithful` means isomorphism to this uncut graph.
  `fullReroot_root_has_no_parent` does not remove `focus.dropLast`.
* The predecessor cut, which deletes that incoming child and retains the focus component, is
  `cutRetainedArm` in `DeclarativeCIPRetainedCutArm`. A ring focus of `retainedArm` is already
  the one-node terminal arm; that agrees with an incoming-parent cut and is not a real-focus cut.
* Readback is the `OccurrenceUnit` path used by `molecularFrameUnit`: root-first history with
  the outer root removed. One step of that path is `rerootStep`.

The carrier does not emit multiple-bond duplicates. On a `SimpleBonded` graph its children are
exactly the positive neighbors other than the immediate predecessor. It is not a
`FaithfulExactExpansion`, and it does not discharge auxiliary-label correctness on rings.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
namespace RetainedOccurrenceCarrier

noncomputable section

open scoped Classical

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-! ## Adjacency paths -/

/-- Consecutive atoms of a root-first list are bonded. -/
def AdjacentSteps (molecule : MoleculeGraph Atom) : List Atom → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => molecule.Adj a b ∧ AdjacentSteps molecule (b :: rest)

/-- A nonempty adjacency walk starting at `root`, stored root-first. -/
def ChainFrom (molecule : MoleculeGraph Atom) (root : Atom) (path : List Atom) : Prop :=
  path.head? = some root ∧ AdjacentSteps molecule path

namespace ChainFrom

variable {molecule : MoleculeGraph Atom} {root : Atom}

theorem ne_nil {path : List Atom} (h : ChainFrom molecule root path) : path ≠ [] := by
  intro hempty
  simp [ChainFrom, hempty] at h

theorem head?_eq {path : List Atom} (h : ChainFrom molecule root path) :
    path.head? = some root :=
  h.1

theorem getLast?_some {path : List Atom} (h : ChainFrom molecule root path) :
    ∃ atom, path.getLast? = some atom :=
  ⟨path.getLast (ne_nil h), List.getLast?_eq_some_getLast (ne_nil h)⟩

theorem single : ChainFrom molecule root [root] :=
  ⟨rfl, trivial⟩

theorem singleton {atom : Atom} (h : ChainFrom molecule root [atom]) : atom = root := by
  simpa [ChainFrom] using h.1

theorem adjacent_append {path : List Atom} {current next : Atom}
    (h : AdjacentSteps molecule path) (hlast : path.getLast? = some current)
    (hadj : molecule.Adj current next) (hne : path ≠ []) :
    AdjacentSteps molecule (path ++ [next]) := by
  induction path with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
      cases as with
      | nil =>
          have hcur : a = current := by simpa using hlast
          subst hcur
          simp [AdjacentSteps, hadj]
      | cons b bs =>
          exact ⟨h.1, ih h.2 hlast (by simp)⟩

theorem adjacent_of_append {path : List Atom} {next : Atom}
    (h : AdjacentSteps molecule (path ++ [next])) (hne : path ≠ []) :
    AdjacentSteps molecule path ∧ molecule.Adj (path.getLast hne) next := by
  induction path with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
      cases as with
      | nil =>
          simp [AdjacentSteps] at h
          exact ⟨trivial, h⟩
      | cons b bs =>
          simp [AdjacentSteps] at h
          have hrec := ih h.2 (by simp)
          exact ⟨⟨h.1, hrec.1⟩, hrec.2⟩

theorem adjacent_take {path : List Atom} (h : AdjacentSteps molecule path)
    {n : Nat} (hle : n ≤ path.length) : AdjacentSteps molecule (path.take n) := by
  induction path generalizing n with
  | nil =>
      simpa [List.take_nil, AdjacentSteps] using (trivial : True)
  | cons a as ih =>
      cases n with
      | zero => exact trivial
      | succ n =>
          cases as with
          | nil =>
              cases n with
              | zero => simp [AdjacentSteps]
              | succ n => simp at hle
          | cons b bs =>
              cases n with
              | zero => simp [AdjacentSteps, List.take_succ_cons]
              | succ n =>
                  have hrec := ih (n := n + 1) h.2 (by
                    have : (a :: b :: bs).length = (b :: bs).length + 1 := by simp
                    omega)
                  simp [AdjacentSteps, List.take_succ_cons]
                  exact ⟨h.1, hrec⟩

theorem snoc {path : List Atom} {current next : Atom}
    (h : ChainFrom molecule root path) (hlast : path.getLast? = some current)
    (hadj : molecule.Adj current next) :
    ChainFrom molecule root (path ++ [next]) := by
  have hne := ne_nil h
  refine ⟨?_, adjacent_append h.2 hlast hadj hne⟩
  cases path with
  | nil => exact (hne rfl).elim
  | cons _ _ => simpa [List.head?_append] using h.1

theorem snoc_inv {path : List Atom} {next : Atom}
    (h : ChainFrom molecule root (path ++ [next])) (hne : path ≠ []) :
    ∃ current, ChainFrom molecule root path ∧ path.getLast? = some current ∧
      molecule.Adj current next := by
  have hhead : path.head? = some root := by
    cases path with
    | nil => exact (hne rfl).elim
    | cons _ _ => simpa [List.head?_append] using h.1
  obtain ⟨hsteps, hadj⟩ := adjacent_of_append h.2 hne
  exact ⟨path.getLast hne, ⟨hhead, hsteps⟩, List.getLast?_eq_some_getLast hne, hadj⟩

theorem take_chain {path : List Atom} (h : ChainFrom molecule root path)
    {n : Nat} (hpos : 0 < n) (hle : n ≤ path.length) :
    ChainFrom molecule root (path.take n) := by
  refine ⟨?_, adjacent_take h.2 hle⟩
  cases path with
  | nil => simp at hle; omega
  | cons a as =>
      cases n with
      | zero => omega
      | succ n =>
          have hhead : a = root := by simpa [ChainFrom] using h.1
          subst a
          rfl

end ChainFrom

/-- The root-first walk is simple: adjacent, starting at the outer root, with no repeated atom. -/
def SimpleFrom (molecule : MoleculeGraph Atom) (root : Atom) (path : List Atom) : Prop :=
  ChainFrom molecule root path ∧ path.Nodup

namespace SimpleFrom

variable {molecule : MoleculeGraph Atom} {root : Atom}

theorem root_path : SimpleFrom molecule root [root] :=
  ⟨ChainFrom.single, by simp⟩

theorem ne_nil {path : List Atom} (h : SimpleFrom molecule root path) : path ≠ [] :=
  ChainFrom.ne_nil h.1

theorem head?_eq {path : List Atom} (h : SimpleFrom molecule root path) :
    path.head? = some root :=
  ChainFrom.head?_eq h.1

theorem length_le_card {path : List Atom} (h : SimpleFrom molecule root path) :
    path.length ≤ Fintype.card Atom :=
  h.2.length_le_card

theorem dropLast {path : List Atom} (h : SimpleFrom molecule root path) (hlen : 1 < path.length) :
    SimpleFrom molecule root path.dropLast := by
  have hne : path ≠ [] := by
    intro hempty
    simp [hempty] at hlen
  have hdrop : path.dropLast ≠ [] := by
    intro hempty
    have hlen' := congrArg List.length (List.dropLast_concat_getLast hne)
    simp [hempty] at hlen'
    omega
  rw [← List.dropLast_concat_getLast hne] at h
  obtain ⟨_, hchain, _, _⟩ := ChainFrom.snoc_inv h.1 hdrop
  exact ⟨hchain, (List.nodup_append.mp h.2).1⟩

theorem append_iff {path : List Atom} {next : Atom} (h : SimpleFrom molecule root path) :
    SimpleFrom molecule root (path ++ [next]) ↔
      (∃ current, path.getLast? = some current ∧ molecule.Adj current next) ∧ next ∉ path := by
  constructor
  · intro happ
    have hne := ne_nil h
    obtain ⟨current, _, hlast, hadj⟩ := ChainFrom.snoc_inv happ.1 hne
    refine ⟨⟨current, hlast, hadj⟩, ?_⟩
    intro hmem
    exact (List.nodup_append.mp happ.2).2.2 next hmem next (by simp) rfl
  · rintro ⟨⟨current, hlast, hadj⟩, hnot⟩
    refine ⟨ChainFrom.snoc h.1 hlast hadj, ?_⟩
    rw [List.nodup_append]
    refine ⟨h.2, by simp, ?_⟩
    intro x hx y hy heq
    have hy' : y = next := by simpa using hy
    exact hnot (hy' ▸ heq ▸ hx)

theorem of_take {path : List Atom} (h : SimpleFrom molecule root path)
    {n : Nat} (hpos : 0 < n) (hle : n ≤ path.length) :
    SimpleFrom molecule root (path.take n) :=
  ⟨ChainFrom.take_chain h.1 hpos hle, h.2.sublist (List.take_sublist n path)⟩

end SimpleFrom

/-- A terminal ring closure after a simple prefix. The final atom is adjacent, already on the
prefix, and is not the immediate predecessor. -/
def RingClosure (molecule : MoleculeGraph Atom) (path : List Atom) (atom : Atom) : Prop :=
  (∃ current, path.getLast? = some current ∧ molecule.Adj current atom) ∧
    atom ∈ path ∧ path.dropLast.getLast? ≠ some atom

/-- Nodes of the outer-root carrier. Paths are root-first and include the outer root. -/
inductive CarrierNode (Atom : Type u) where
  | real (path : List Atom)
  | ring (path : List Atom) (atom : Atom)
  deriving DecidableEq

namespace CarrierNode

variable {molecule : MoleculeGraph Atom} {root : Atom}

/-- Real nodes are simple outer paths. Ring nodes are one terminal closure after such a path. -/
def Valid (molecule : MoleculeGraph Atom) (root : Atom) : CarrierNode Atom → Prop
  | .real path => SimpleFrom molecule root path
  | .ring path atom => SimpleFrom molecule root path ∧ RingClosure molecule path atom

/-- Root-first atoms represented by a node, including a final closure when there is one. -/
def fullAtoms : CarrierNode Atom → List Atom
  | .real path => path
  | .ring path atom => path ++ [atom]

/-- Atom represented by the node. -/
def atomOf : CarrierNode Atom → Option Atom
  | .real path => path.getLast?
  | .ring _ atom => some atom

/-- Declarative label. Ring distance is the outer-root index of the duplicated atom. -/
def label : CarrierNode Atom → NodeLabel Atom
  | .real path => ⟨path.getLast?, .realAtom⟩
  | .ring path atom => ⟨some atom, .ringDuplicate (path.idxOf atom)⟩

/-- Depth in the outer-root prefix tree. -/
def depth : CarrierNode Atom → Nat
  | .real path => path.length - 1
  | .ring path _ => path.length

/-- Prefix extension. Ring nodes are terminal. -/
def Child : CarrierNode Atom → CarrierNode Atom → Prop
  | .real path, .real child => ∃ atom, child = path ++ [atom]
  | .real path, .ring childPath _ => childPath = path
  | .ring _ _, _ => False

end CarrierNode

variable {molecule : MoleculeGraph Atom} {root : Atom}

theorem real_valid_iff {path : List Atom} :
    CarrierNode.Valid molecule root (.real path) ↔ SimpleFrom molecule root path :=
  Iff.rfl

theorem ring_valid_iff {path : List Atom} {atom : Atom} :
    CarrierNode.Valid molecule root (.ring path atom) ↔
      SimpleFrom molecule root path ∧
        (∃ current, path.getLast? = some current ∧ molecule.Adj current atom) ∧
        atom ∈ path ∧ path.dropLast.getLast? ≠ some atom := by
  simp [CarrierNode.Valid, RingClosure]

theorem ring_atom_ne_current {path : List Atom} {current atom : Atom}
    (h : RingClosure molecule path atom) (hlast : path.getLast? = some current) :
    atom ≠ current := by
  intro heq
  obtain ⟨⟨current', hlast', hadj⟩, _, _⟩ := h
  cases hlast.symm.trans hlast'
  subst heq
  simp [MoleculeGraph.Adj, molecule.bond_self] at hadj

/-- A node is real exactly when its root-first atom list does not repeat an atom. A ring node
repeats only its final closure atom. -/
theorem provenance_real_iff_nodup {node : CarrierNode Atom}
    (h : CarrierNode.Valid molecule root node) :
    (CarrierNode.label node).provenance = NodeProvenance.realAtom ↔
      (CarrierNode.fullAtoms node).Nodup := by
  cases node with
  | real path =>
      simp [CarrierNode.label, CarrierNode.fullAtoms, h.2]
  | ring path atom =>
      simp [CarrierNode.label, CarrierNode.fullAtoms]
      intro hnd
      rw [List.nodup_append] at hnd
      exact hnd.2.2 atom h.2.2.1 atom (by simp) rfl

theorem label_ring_distance {path : List Atom} {atom : Atom} :
    (CarrierNode.label (.ring path atom)).provenance =
      NodeProvenance.ringDuplicate (path.idxOf atom) :=
  rfl

theorem provenance_ne_multipleBond {node : CarrierNode Atom} {distance : Nat} :
    (CarrierNode.label node).provenance ≠ NodeProvenance.multipleBondDuplicate distance := by
  cases node <;> simp [CarrierNode.label]

theorem carrierChild_depth {parent node : CarrierNode Atom}
    (hparent : CarrierNode.Valid molecule root parent)
    (hnode : CarrierNode.Valid molecule root node)
    (hchild : CarrierNode.Child parent node) :
    CarrierNode.depth node = CarrierNode.depth parent + 1 := by
  cases parent with
  | ring _ _ => cases node <;> simp [CarrierNode.Child] at hchild
  | real path =>
      have hpos : 0 < path.length := List.length_pos_iff.mpr (SimpleFrom.ne_nil hparent)
      cases node with
      | real child =>
          obtain ⟨atom, rfl⟩ := hchild
          simp [CarrierNode.depth, List.length_append]
          omega
      | ring childPath atom =>
          cases hchild
          simp [CarrierNode.depth]
          omega

theorem carrier_unique_parent_raw {first second node : CarrierNode Atom}
    (hfirst : CarrierNode.Child first node) (hsecond : CarrierNode.Child second node) :
    first = second := by
  cases first <;> cases second <;> cases node <;> simp [CarrierNode.Child] at hfirst hsecond
  · obtain ⟨atom, rfl⟩ := hfirst
    obtain ⟨atom', heq⟩ := hsecond
    exact congrArg CarrierNode.real (List.append_inj_left' heq (by simp))
  · cases hfirst
    cases hsecond
    rfl

/-! ## Finiteness -/

theorem finite_lists_length_le (n : Nat) :
    {path : List Atom | path.length ≤ n}.Finite := by
  have hcover : {path : List Atom | path.length ≤ n} ⊆
      ⋃ k ∈ Set.Iic n, Set.range (fun vector : List.Vector Atom k => vector.toList) := by
    intro path hpath
    simp only [Set.mem_iUnion, Set.mem_Iic]
    exact ⟨path.length, hpath, ⟨path, rfl⟩, rfl⟩
  exact Set.Finite.subset ((Set.finite_Iic n).biUnion fun _ _ => Set.finite_range _) hcover

theorem valid_finite (molecule : MoleculeGraph Atom) (root : Atom) :
    Set.Finite {node : CarrierNode Atom | CarrierNode.Valid molecule root node} := by
  let N := Fintype.card Atom
  have hpaths := finite_lists_length_le (Atom := Atom) N
  have hcover :
      {node : CarrierNode Atom | CarrierNode.Valid molecule root node} ⊆
        (CarrierNode.real '' {path : List Atom | path.length ≤ N}) ∪
          ((fun pair : List Atom × Atom => CarrierNode.ring pair.1 pair.2) ''
            ({path : List Atom | path.length ≤ N} ×ˢ Set.univ)) := by
    intro node hnode
    cases node with
    | real path =>
        exact Or.inl ⟨path, SimpleFrom.length_le_card hnode, rfl⟩
    | ring path atom =>
        exact Or.inr ⟨(path, atom), ⟨SimpleFrom.length_le_card hnode.1, trivial⟩, rfl⟩
  refine Set.Finite.subset (Set.Finite.union (hpaths.image _) ?_) hcover
  exact ((hpaths.prod Set.finite_univ).image _)

abbrev Nodes (molecule : MoleculeGraph Atom) (root : Atom) :=
  {node : CarrierNode Atom // CarrierNode.Valid molecule root node}

theorem carrier_root_valid (molecule : MoleculeGraph Atom) (root : Atom) :
    CarrierNode.Valid molecule root (.real [root]) :=
  SimpleFrom.root_path

theorem reachable_real (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} (h : SimpleFrom molecule root path) :
    Relation.ReflTransGen (fun parent child : Nodes molecule root =>
      CarrierNode.Child parent.1 child.1)
      ⟨.real [root], carrier_root_valid molecule root⟩ ⟨.real path, h⟩ := by
  suffices ∀ n (path : List Atom) (h : SimpleFrom molecule root path), path.length = n →
      Relation.ReflTransGen (fun parent child : Nodes molecule root =>
        CarrierNode.Child parent.1 child.1)
        ⟨.real [root], carrier_root_valid molecule root⟩ ⟨.real path, h⟩ by
    exact this path.length path h rfl
  intro n
  induction n with
  | zero =>
      intro path h hlen
      exact (SimpleFrom.ne_nil h (List.length_eq_zero_iff.mp hlen)).elim
  | succ n ih =>
      intro path h hlen
      cases n with
      | zero =>
          have hpath : path = [root] := by
            cases path with
            | nil => simp at hlen
            | cons a as =>
                cases as with
                | nil =>
                    have hhead := SimpleFrom.head?_eq h
                    simp at hhead
                    exact hhead ▸ rfl
                | cons _ _ => simp at hlen
          subst hpath
          exact Relation.ReflTransGen.refl
      | succ n =>
          have hlen2 : 1 < path.length := by omega
          have hdrop := SimpleFrom.dropLast h hlen2
          have hne := SimpleFrom.ne_nil h
          have hchild : CarrierNode.Child (.real path.dropLast) (.real path) :=
            ⟨path.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
          have hlenDrop : path.dropLast.length = n + 1 := by
            simp [List.length_dropLast, hlen]
          exact Relation.ReflTransGen.tail (ih _ hdrop hlenDrop) hchild

theorem carrier_reachable_raw (molecule : MoleculeGraph Atom) (root : Atom)
    (node : Nodes molecule root) :
    Relation.ReflTransGen (fun parent child : Nodes molecule root =>
      CarrierNode.Child parent.1 child.1)
      ⟨.real [root], carrier_root_valid molecule root⟩ node := by
  rcases node with ⟨node, hnode⟩
  cases node with
  | real _ => exact reachable_real molecule root hnode
  | ring _ _ =>
      exact Relation.ReflTransGen.tail (reachable_real molecule root hnode.1) rfl

/-- The finite prefix tree of simple outer paths and terminal ring closures. -/
def retainedCarrier (molecule : MoleculeGraph Atom) (root : Atom) : RootedDigraph Atom where
  Node := Nodes molecule root
  nodeFintype := @Fintype.ofFinite _ (valid_finite molecule root).to_subtype
  root := ⟨.real [root], carrier_root_valid molecule root⟩
  child := fun parent node => CarrierNode.Child parent.1 node.1
  label := fun node => CarrierNode.label node.1
  depth := fun node => CarrierNode.depth node.1
  root_depth := by simp [CarrierNode.depth]
  child_depth := by
    intro parent node hchild
    exact carrierChild_depth parent.2 node.2 hchild
  reachable := carrier_reachable_raw molecule root

@[simp] theorem retainedCarrier_child (molecule : MoleculeGraph Atom) (root : Atom)
    {parent node : (retainedCarrier molecule root).Node} :
    (retainedCarrier molecule root).child parent node ↔ CarrierNode.Child parent.1 node.1 :=
  Iff.rfl

@[simp] theorem retainedCarrier_label (molecule : MoleculeGraph Atom) (root : Atom)
    (node : (retainedCarrier molecule root).Node) :
    (retainedCarrier molecule root).label node = CarrierNode.label node.1 :=
  rfl

@[simp] theorem retainedCarrier_depth (molecule : MoleculeGraph Atom) (root : Atom)
    (node : (retainedCarrier molecule root).Node) :
    (retainedCarrier molecule root).depth node = CarrierNode.depth node.1 :=
  rfl

theorem retainedCarrier_root (molecule : MoleculeGraph Atom) (root : Atom) :
    (retainedCarrier molecule root).root = ⟨.real [root], carrier_root_valid molecule root⟩ :=
  rfl

theorem retainedCarrier_unique_parent (molecule : MoleculeGraph Atom) (root : Atom)
    {first second node : (retainedCarrier molecule root).Node}
    (hfirst : (retainedCarrier molecule root).child first node)
    (hsecond : (retainedCarrier molecule root).child second node) :
    first = second := by
  apply Subtype.ext
  exact carrier_unique_parent_raw hfirst hsecond

theorem depth_lt_of_transGen {graph : RootedDigraph Atom} {parent node : graph.Node}
    (h : Relation.TransGen graph.child parent node) :
    graph.depth parent < graph.depth node := by
  induction h with
  | single hedge =>
      rw [graph.child_depth hedge]
      omega
  | tail _ hedge ih =>
      rw [graph.child_depth hedge]
      omega

theorem retainedCarrier_acyclic (molecule : MoleculeGraph Atom) (root : Atom)
    (node : (retainedCarrier molecule root).Node) :
    ¬ Relation.TransGen (retainedCarrier molecule root).child node node := by
  intro h
  have hlt := depth_lt_of_transGen (graph := retainedCarrier molecule root) h
  omega

theorem retainedCarrier_not_child_root (molecule : MoleculeGraph Atom) (root : Atom)
    (parent : (retainedCarrier molecule root).Node) :
    ¬ (retainedCarrier molecule root).child parent (retainedCarrier molecule root).root := by
  intro hchild
  have hdepth := (retainedCarrier molecule root).child_depth hchild
  simp [retainedCarrier_depth, retainedCarrier_root, CarrierNode.depth] at hdepth

theorem take_append_succ (p : List Atom) (atom : Atom) (rest : List Atom) :
    (p ++ (atom :: rest)).take (p.length + 1) = p ++ [atom] := by
  induction p with
  | nil => simp
  | cons x xs ih =>
      simp [List.length_cons, List.take_succ_cons, ih]

theorem transGen_of_append (molecule : MoleculeGraph Atom) (root : Atom)
    {p rest : List Atom} (hp : SimpleFrom molecule root p)
    (hq : SimpleFrom molecule root (p ++ rest)) (hne : rest ≠ []) :
    Relation.TransGen (retainedCarrier molecule root).child
      ⟨.real p, hp⟩ ⟨.real (p ++ rest), hq⟩ := by
  cases rest with
  | nil => exact (hne rfl).elim
  | cons atom rest =>
      have hmid : SimpleFrom molecule root (p ++ [atom]) := by
        have htaken := SimpleFrom.of_take hq (n := p.length + 1) (by omega) (by simp)
        have htakeEq := take_append_succ p atom rest
        simpa [htakeEq] using htaken
      have hchild : (retainedCarrier molecule root).child
          ⟨.real p, hp⟩ ⟨.real (p ++ [atom]), hmid⟩ := by
        change CarrierNode.Child (.real p) (.real (p ++ [atom]))
        exact ⟨atom, rfl⟩
      cases rest with
      | nil =>
          have hsame : (⟨.real (p ++ [atom]), hmid⟩ : Nodes molecule root) =
              ⟨.real (p ++ [atom]), hq⟩ := Subtype.ext rfl
          rw [← hsame]
          exact Relation.TransGen.single hchild
      | cons b rest =>
          have hpath : (p ++ [atom]) ++ (b :: rest) = p ++ (atom :: b :: rest) := by simp
          have htailSimple : SimpleFrom molecule root ((p ++ [atom]) ++ (b :: rest)) := by
            simpa [hpath] using hq
          have hrec := transGen_of_append molecule root hmid htailSimple (by simp)
          have hend : (⟨.real ((p ++ [atom]) ++ (b :: rest)), htailSimple⟩ :
              Nodes molecule root) = ⟨.real (p ++ (atom :: b :: rest)), hq⟩ := by
            apply Subtype.ext
            simpa [hpath]
          rw [← hend]
          exact Relation.TransGen.head hchild hrec

/-- Real carrier ancestry is strict prefix extension, so each real node has one route from the
outer root. -/
theorem retainedCarrier_real_ancestor_iff (molecule : MoleculeGraph Atom) (root : Atom)
    {p q : List Atom} (hp : SimpleFrom molecule root p) (hq : SimpleFrom molecule root q) :
    Relation.TransGen (retainedCarrier molecule root).child
      ⟨.real p, hp⟩ ⟨.real q, hq⟩ ↔
      ∃ rest, rest ≠ [] ∧ q = p ++ rest := by
  constructor
  · intro htrans
    suffices ∀ (src tgt : Nodes molecule root),
        Relation.TransGen (retainedCarrier molecule root).child src tgt →
        ∀ {p q : List Atom} (hp : SimpleFrom molecule root p),
          src = ⟨.real p, hp⟩ → tgt.1 = .real q →
          ∃ rest, rest ≠ [] ∧ q = p ++ rest by
      exact this ⟨.real p, hp⟩ ⟨.real q, hq⟩ htrans hp rfl rfl
    intro src tgt htrans
    induction htrans with
    | single hedge =>
        intro p q hp hsrc htgt
        have hchild : CarrierNode.Child (.real p) (.real q) := by
          simpa [hsrc, htgt] using hedge
        obtain ⟨atom, rfl⟩ := hchild
        exact ⟨[atom], by simp, rfl⟩
    | @tail middle current hprev hedge ih =>
        intro p q hp hsrc htgt
        have hchild : CarrierNode.Child middle.1 (.real q) := by
          simpa [htgt] using hedge
        cases hmid : middle.1 with
        | ring _ _ => simp [CarrierNode.Child, hmid] at hchild
        | real mpath =>
            obtain ⟨rest, hne, hsplit⟩ := ih (q := mpath) hp hsrc hmid
            obtain ⟨atom, hqeq⟩ := by simpa [hmid] using hchild
            exact ⟨rest ++ [atom], by simp [hne], by simp [hsplit, hqeq]⟩
  · rintro ⟨rest, hne, rfl⟩
    exact transGen_of_append molecule root hp hq hne

theorem getLast?_cons_ne {a : Atom} {l : List Atom} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact (h rfl).elim
  | cons _ _ => rfl

theorem duplicatePrefix_getLast? {path : List Atom} {atom : Atom} (hmem : atom ∈ path) :
    (path.take (path.idxOf atom + 1)).getLast? = some atom := by
  induction path with
  | nil => simp at hmem
  | cons x xs ih =>
      by_cases hx : x = atom
      · subst x
        simp [List.idxOf_cons_self]
      · have htail : atom ∈ xs := by
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact (hx rfl).elim
          · exact hmem
        have hidx : (x :: xs).idxOf atom = xs.idxOf atom + 1 := by
          rw [List.idxOf_cons, beq_eq_false_iff_ne.mpr hx]
          rfl
        rw [hidx, List.take_succ_cons]
        have hne : xs.take (xs.idxOf atom + 1) ≠ [] := by
          intro hempty
          have hlen := congrArg List.length hempty
          simp [List.length_take, List.idxOf_lt_length_of_mem htail] at hlen
        rw [getLast?_cons_ne hne]
        exact ih htail

/-- The ring distance is the depth of the outer-root ancestor that carries the duplicated atom. -/
theorem ring_distance_eq_ancestor_depth (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    ∃ ancestor : (retainedCarrier molecule root).Node,
      ((retainedCarrier molecule root).label ancestor).atom? = some atom ∧
        ((retainedCarrier molecule root).label ancestor).provenance =
          NodeProvenance.realAtom ∧
        (retainedCarrier molecule root).depth ancestor = path.idxOf atom ∧
        Relation.TransGen (retainedCarrier molecule root).child ancestor
          ⟨.ring path atom, h⟩ := by
  obtain ⟨hsimple, ⟨⟨current, hlast, hadj⟩, hmem, _hpen⟩⟩ := h
  have hne : atom ≠ current :=
    ring_atom_ne_current ⟨⟨current, hlast, hadj⟩, hmem, _hpen⟩ hlast
  have hpos : 0 < path.idxOf atom + 1 := by omega
  have hle : path.idxOf atom + 1 ≤ path.length :=
    Nat.succ_le_of_lt (List.idxOf_lt_length_of_mem hmem)
  let prefixPath := path.take (path.idxOf atom + 1)
  have hprefix : SimpleFrom molecule root prefixPath :=
    SimpleFrom.of_take hsimple hpos hle
  have hlastPrefix : prefixPath.getLast? = some atom := duplicatePrefix_getLast? hmem
  have hstrict : path.idxOf atom + 1 < path.length := by
    by_contra hge
    have heq : path.idxOf atom + 1 = path.length := by
      have := List.idxOf_lt_length_of_mem hmem
      omega
    have htake : prefixPath = path := by
      simp [prefixPath, heq, List.take_length]
    rw [htake] at hlastPrefix
    exact hne (Option.some_inj.mp (hlastPrefix.symm.trans hlast))
  have hrestNe : path.drop (path.idxOf atom + 1) ≠ [] := by
    intro hempty
    have hsplit := List.take_append_drop (path.idxOf atom + 1) path
    rw [hempty, List.append_nil] at hsplit
    have hlen := congrArg List.length hsplit
    simp [List.length_take, Nat.min_eq_left hle] at hlen
    omega
  have hjoined : prefixPath ++ path.drop (path.idxOf atom + 1) = path :=
    List.take_append_drop _ _
  have htailSimple : SimpleFrom molecule root
      (prefixPath ++ path.drop (path.idxOf atom + 1)) := by
    simpa [hjoined] using hsimple
  have htrans := transGen_of_append molecule root hprefix htailSimple hrestNe
  have hend : (⟨.real (prefixPath ++ path.drop (path.idxOf atom + 1)), htailSimple⟩ :
      Nodes molecule root) = ⟨.real path, hsimple⟩ := by
    apply Subtype.ext
    simpa [hjoined]
  rw [hend] at htrans
  refine ⟨⟨.real prefixPath, hprefix⟩, ?_, rfl, ?_, Relation.TransGen.tail htrans rfl⟩
  · simp [retainedCarrier_label, CarrierNode.label, hlastPrefix]
  · simp [retainedCarrier_depth, CarrierNode.depth, prefixPath, List.length_take,
      Nat.min_eq_left hle]

/-! ## Readback to occurrence paths -/

/-- The occurrence path stored by `molecularFrameUnit`: the root-first atoms after the outer root.
A ring closure appends its final atom, so only that final atom may repeat. -/
def occurrenceReadback (root : Atom) : CarrierNode Atom → OccurrenceUnit Atom
  | .real path => ⟨root, path.tail⟩
  | .ring path atom => ⟨root, path.tail ++ [atom]⟩

theorem occurrenceReadback_real {path : List Atom}
    (h : CarrierNode.Valid molecule root (.real path)) :
    occurrenceReadback root (.real path) = ⟨root, path.tail⟩ ∧
      root :: path.tail = path := by
  refine ⟨rfl, ?_⟩
  have hhead := SimpleFrom.head?_eq h
  cases path with
  | nil => exact (SimpleFrom.ne_nil h rfl).elim
  | cons a as =>
      simp at hhead
      subst a
      rfl

theorem occurrenceReadback_ring {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    occurrenceReadback root (.ring path atom) = ⟨root, path.tail ++ [atom]⟩ ∧
      root :: (path.tail ++ [atom]) = path ++ [atom] := by
  refine ⟨rfl, ?_⟩
  have hhead := SimpleFrom.head?_eq h.1
  cases path with
  | nil => exact (SimpleFrom.ne_nil h.1 rfl).elim
  | cons a as =>
      simp at hhead
      subst a
      rfl

/-- `molecularFrameUnit` stores `history.reverse.tail` for a current-first official history.
For a carrier node that history is the reversal of `fullAtoms`. -/
theorem occurrenceReadback_eq_history_reverse_tail {node : CarrierNode Atom}
    (h : CarrierNode.Valid molecule root node) :
    (⟨root, (CarrierNode.fullAtoms node).reverse.reverse.tail⟩ : OccurrenceUnit Atom) =
      occurrenceReadback root node := by
  cases node with
  | real path =>
      obtain ⟨_, hsplit⟩ := occurrenceReadback_real h
      simp [CarrierNode.fullAtoms, occurrenceReadback]
  | ring path atom =>
      have hne : path ≠ [] := SimpleFrom.ne_nil h.1
      simp [CarrierNode.fullAtoms, occurrenceReadback, List.tail_append_of_ne_nil hne]

theorem mem_of_getLast? {a : Atom} {l : List Atom} (h : l.getLast? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs =>
      rw [List.getLast?_eq_some_getLast (l := x :: xs) (by simp)] at h
      cases h
      exact List.getLast_mem _

theorem suffix_split_two (suffix : List Atom) (h : 1 < suffix.length) :
    ∃ front last veryLast, suffix = front ++ [last, veryLast] := by
  have hne : suffix ≠ [] := by
    intro hempty
    simp [hempty] at h
  have hdropNe : suffix.dropLast ≠ [] := by
    intro hempty
    have hlen' := congrArg List.length (List.dropLast_concat_getLast hne)
    simp [hempty] at hlen'
    omega
  refine ⟨suffix.dropLast.dropLast, suffix.dropLast.getLast hdropNe, suffix.getLast hne, ?_⟩
  have houter := List.dropLast_concat_getLast hne
  have hinner := List.dropLast_concat_getLast hdropNe
  have hassoc : suffix.dropLast.dropLast ++
      [suffix.dropLast.getLast hdropNe, suffix.getLast hne] =
      (suffix.dropLast.dropLast ++ [suffix.dropLast.getLast hdropNe]) ++
        [suffix.getLast hne] := by
    simp
  rw [hassoc, hinner, houter]

theorem incomingAtom?_eq_dropLast_getLast (rootAtom : Atom) (suffix : List Atom)
    (h : 1 < suffix.length) :
    incomingAtom? rootAtom suffix = suffix.dropLast.getLast? := by
  obtain ⟨front, last, veryLast, hsplit⟩ := suffix_split_two suffix h
  have hrev : suffix.reverse = veryLast :: last :: front.reverse := by
    simp [hsplit, List.reverse_append]
  have hdrop : suffix.dropLast = front ++ [last] := by
    simp [hsplit]
  simp [incomingAtom?, hrev, hdrop]

theorem incomingAtom?_eq_full_penultimate (outer : Atom) (suffix : List Atom)
    (h : 0 < suffix.length) :
    incomingAtom? outer suffix = (outer :: suffix).dropLast.getLast? := by
  cases suffix with
  | nil => simp at h
  | cons a as =>
      cases as with
      | nil =>
          simp [incomingAtom?, List.dropLast, List.reverse_cons]
      | cons b bs =>
          have hin := incomingAtom?_eq_dropLast_getLast outer (a :: b :: bs) (by simp)
          have hdrop : (outer :: a :: b :: bs).dropLast =
              outer :: (a :: b :: bs).dropLast :=
            List.dropLast_cons_of_ne_nil (by simp)
          rw [hdrop, getLast?_cons_ne (by simp), hin]

theorem reentry_readback_eq_rerootStep {focus : List Atom}
    (h : SimpleFrom molecule root focus) (hlen : 1 < focus.length) :
    occurrenceReadback root (.real focus.dropLast) =
      ⟨root, rerootStep root focus.tail
        (focus.dropLast.getLast (by
          intro hempty
          have hrecon := List.dropLast_concat_getLast (SimpleFrom.ne_nil h)
          have hlen' := congrArg List.length hrecon
          simp [hempty] at hlen'
          omega))⟩ := by
  cases focus with
  | nil => simp at hlen
  | cons head tail =>
      have hhead : head = root := by
        have := SimpleFrom.head?_eq h
        simp at this
        exact this
      subst head
      have htailPos : 0 < tail.length := by simp at hlen; omega
      have hdropNe : (root :: tail).dropLast ≠ [] := by
        cases tail with
        | nil => simp at htailPos
        | cons _ _ => simp [List.dropLast_cons_of_ne_nil]
      have hdrop : (root :: tail).dropLast = root :: tail.dropLast :=
        List.dropLast_cons_of_ne_nil (by
          intro hempty
          simp [hempty] at htailPos)
      have hin := incomingAtom?_eq_full_penultimate root tail htailPos
      have hsome : (root :: tail).dropLast.getLast? =
          some ((root :: tail).dropLast.getLast hdropNe) :=
        List.getLast?_eq_some_getLast _
      have hstep : rerootStep root tail ((root :: tail).dropLast.getLast hdropNe) =
          tail.dropLast := by
        rw [rerootStep, hin, hsome]
        simp
      simp [occurrenceReadback, hdrop]
      have hlastEq : (root :: tail.dropLast).getLast (by
          intro hempty
          exact hdropNe (hdrop.trans hempty)) =
          (root :: tail).dropLast.getLast hdropNe := by
        apply Option.some_inj.mp
        rw [← List.getLast?_eq_some_getLast, ← List.getLast?_eq_some_getLast]
        exact congrArg List.getLast? hdrop.symm
      rw [hlastEq]
      exact hstep.symm

theorem outward_readback_eq_rerootStep {path : List Atom} {next : Atom}
    (h : SimpleFrom molecule root (path ++ [next])) (hne : path ≠ []) :
    occurrenceReadback root (.real (path ++ [next])) =
      ⟨root, rerootStep root path.tail next⟩ := by
  have hprefix : SimpleFrom molecule root path := by
    have hpos : 0 < path.length := List.length_pos_iff.mpr hne
    have htaken := SimpleFrom.of_take h hpos (by simp)
    simpa [List.take_left] using htaken
  have hnot : next ∉ path := by
    intro hmem
    exact (List.nodup_append.mp h.2).2.2 next hmem next (by simp) rfl
  cases path with
  | nil => exact (hne rfl).elim
  | cons head tail =>
      have hhead : head = root := by
        have := SimpleFrom.head?_eq hprefix
        simp at this
        exact this
      subst head
      have hread : ((root :: tail) ++ [next]).tail = tail ++ [next] := by
        simp
      cases tail with
      | nil => simp [occurrenceReadback, rerootStep_nil]
      | cons a as =>
          have hdiff : incomingAtom? root (a :: as) ≠ some next := by
            intro heq
            have hin := incomingAtom?_eq_full_penultimate root (a :: as) (by simp)
            rw [hin] at heq
            exact hnot ((List.dropLast_sublist (root :: a :: as)).mem (mem_of_getLast? heq))
          have hstep : rerootStep root (a :: as) next = a :: as ++ [next] := by
            simp [rerootStep, hdiff]
          simp [occurrenceReadback, hstep]

theorem ring_readback_eq_rerootStep {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    occurrenceReadback root (.ring path atom) =
      ⟨root, rerootStep root path.tail atom⟩ := by
  have hnot : path.dropLast.getLast? ≠ some atom := h.2.2.2
  cases path with
  | nil => exact (SimpleFrom.ne_nil h.1 rfl).elim
  | cons head tail =>
      have hhead : head = root := by
        have := SimpleFrom.head?_eq h.1
        simp at this
        exact this
      subst head
      have htailPos : 0 < tail.length := by
        by_contra hzero
        have htail : tail = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hzero)
        subst htail
        have hatom : atom = root := by simpa using h.2.2.1
        subst hatom
        exact (ring_atom_ne_current h.2 rfl) rfl
      have hin := incomingAtom?_eq_full_penultimate root tail htailPos
      have hdiff : incomingAtom? root tail ≠ some atom := by
        rw [hin]
        exact hnot
      have hstep : rerootStep root tail atom = tail ++ [atom] := by
        simp [rerootStep, hdiff]
      simp [occurrenceReadback, hstep]

/-! ## Neighbor classification -/

theorem neighbor_child_iff {path : List Atom} {current next : Atom}
    (hpath : SimpleFrom molecule root path) (hlast : path.getLast? = some current) :
    (∃ child, CarrierNode.Child (.real path) child ∧ CarrierNode.atomOf child = some next ∧
        CarrierNode.Valid molecule root child) ↔
      molecule.Adj current next ∧ path.dropLast.getLast? ≠ some next := by
  constructor
  · rintro ⟨child, hchild, hatom, hvalid⟩
    cases child with
    | real q =>
        obtain ⟨atom, rfl⟩ := hchild
        simp [CarrierNode.atomOf] at hatom
        subst atom
        obtain ⟨⟨current', hlast', hadj⟩, hnot⟩ :=
          (SimpleFrom.append_iff hpath).1 hvalid
        cases hlast.symm.trans hlast'
        refine ⟨hadj, ?_⟩
        intro hpen
        exact hnot ((List.dropLast_sublist path).mem (mem_of_getLast? hpen))
    | ring q atom =>
        cases hchild
        simp [CarrierNode.atomOf] at hatom
        subst atom
        obtain ⟨⟨current', hlast', hadj⟩, _hmem, hpen⟩ := hvalid.2
        cases hlast.symm.trans hlast'
        exact ⟨hadj, hpen⟩
  · rintro ⟨hadj, hpen⟩
    by_cases hmem : next ∈ path
    · refine ⟨.ring path next, rfl, rfl, ⟨hpath, ⟨⟨current, hlast, hadj⟩, hmem, hpen⟩⟩⟩
    · refine ⟨.real (path ++ [next]), ⟨next, rfl⟩, ?_, ?_⟩
      · simp [CarrierNode.atomOf]
      · exact (SimpleFrom.append_iff hpath).2 ⟨⟨current, hlast, hadj⟩, hmem⟩

theorem simpleBonded_neighbor_child_iff {path : List Atom} {current next : Atom}
    (hsimple : MoleculeGraph.SimpleBonded molecule)
    (hpath : SimpleFrom molecule root path) (hlast : path.getLast? = some current) :
    (∃ child, CarrierNode.Child (.real path) child ∧ CarrierNode.atomOf child = some next ∧
        CarrierNode.Valid molecule root child) ↔
      molecule.Adj current next ∧ path.dropLast.getLast? ≠ some next ∧
        molecule.bond current next = 1 := by
  rw [neighbor_child_iff hpath hlast]
  constructor
  · rintro ⟨hadj, hpen⟩
    exact ⟨hadj, hpen, hsimple current next hadj⟩
  · rintro ⟨hadj, hpen, _hbond⟩
    exact ⟨hadj, hpen⟩

/-! ## Rerooting the prefix tree -/

def commonPrefixLength : List Atom → List Atom → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => if a = b then commonPrefixLength as bs + 1 else 0

theorem commonPrefixLength_self (l : List Atom) : commonPrefixLength l l = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [commonPrefixLength, ih]

theorem commonPrefixLength_comm (l r : List Atom) :
    commonPrefixLength l r = commonPrefixLength r l := by
  induction l generalizing r with
  | nil => cases r <;> rfl
  | cons a as ih =>
      cases r with
      | nil => rfl
      | cons b bs =>
          by_cases h : a = b
          · simp [commonPrefixLength, h, ih]
          · simp [commonPrefixLength, h, Ne.symm h]

theorem cons_prefix_cons {a : Atom} {l₁ l₂ : List Atom} :
    a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa using ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by simpa using ht⟩

theorem commonPrefixLength_eq_length_left {l r : List Atom} :
    commonPrefixLength l r = l.length ↔ l <+: r := by
  induction l generalizing r with
  | nil => simp [commonPrefixLength]
  | cons a as ih =>
      cases r with
      | nil => simp [commonPrefixLength]
      | cons b bs =>
          by_cases h : a = b
          · subst b
            simp [commonPrefixLength, List.length_cons, ih]
          · simp [commonPrefixLength, h, List.length_cons]

theorem commonPrefixLength_le_left (l r : List Atom) :
    commonPrefixLength l r ≤ l.length := by
  induction l generalizing r with
  | nil => simp [commonPrefixLength]
  | cons a as ih =>
      cases r with
      | nil => simp [commonPrefixLength]
      | cons b bs =>
          by_cases h : a = b
          · simp [commonPrefixLength, h, ih]
          · simp [commonPrefixLength, h]

theorem commonPrefixLength_le_right (l r : List Atom) :
    commonPrefixLength l r ≤ r.length := by
  rw [commonPrefixLength_comm]
  exact commonPrefixLength_le_left r l

theorem commonPrefixLength_append_singleton_of_not_prefix
    (focus parent : List Atom) (x : Atom) (hnot : ¬ parent ++ [x] <+: focus) :
    commonPrefixLength focus (parent ++ [x]) = commonPrefixLength focus parent := by
  induction parent generalizing focus with
  | nil =>
      cases focus with
      | nil => simp [commonPrefixLength]
      | cons a as =>
          by_cases h : a = x
          · subst a
            exact (hnot ⟨as, by simp⟩).elim
          · simp [commonPrefixLength, h]
  | cons b bs ih =>
      cases focus with
      | nil => simp [commonPrefixLength]
      | cons a as =>
          by_cases h : a = b
          · subst a
            simp [commonPrefixLength]
            apply ih
            intro hpre
            rcases hpre with ⟨t, ht⟩
            exact hnot ⟨t, by simpa using ht⟩
          · simp [commonPrefixLength, h]

def realArmDepth (focus path : List Atom) : Nat :=
  path.length + focus.length - 2 * commonPrefixLength focus path

theorem realArmDepth_eq_zero_iff (focus path : List Atom) :
    realArmDepth focus path = 0 ↔ path = focus := by
  constructor
  · intro h
    have hleftBound := commonPrefixLength_le_left focus path
    have hrightBound := commonPrefixLength_le_right focus path
    have hsub : path.length + focus.length - 2 * commonPrefixLength focus path = 0 := by
      simpa [realArmDepth] using h
    have hleSum : 2 * commonPrefixLength focus path ≤ path.length + focus.length := by
      have hsum : focus.length + path.length = path.length + focus.length := by ac_rfl
      exact hsum ▸ (by omega)
    have heq : path.length + focus.length = 2 * commonPrefixLength focus path :=
      Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hsub) hleSum
    have hleft : commonPrefixLength focus path = focus.length := by omega
    have hpre : focus <+: path := (commonPrefixLength_eq_length_left).1 hleft
    rcases hpre with ⟨t, ht⟩
    have ht0 : t.length = 0 := by
      have := congrArg List.length ht
      simp at this
      omega
    simp at ht0
    simp [ht0] at ht
    exact ht.symm
  · rintro rfl
    rw [realArmDepth, commonPrefixLength_self]
    omega

theorem realArmDepth_append_not_prefix (focus parent : List Atom) (x : Atom)
    (hnot : ¬ parent ++ [x] <+: focus) :
    realArmDepth focus (parent ++ [x]) = realArmDepth focus parent + 1 := by
  unfold realArmDepth
  rw [commonPrefixLength_append_singleton_of_not_prefix focus parent x hnot]
  simp [List.length_append]
  have hle : 2 * commonPrefixLength focus parent ≤ parent.length + focus.length := by
    have h1 := commonPrefixLength_le_left focus parent
    have h2 := commonPrefixLength_le_right focus parent
    omega
  omega

theorem realArmDepth_prefix_step (focus parent : List Atom) (x : Atom)
    (hpre : parent ++ [x] <+: focus) :
    realArmDepth focus parent = realArmDepth focus (parent ++ [x]) + 1 := by
  have hparent : parent <+: focus := by
    rcases hpre with ⟨t, ht⟩
    exact ⟨x :: t, by simpa using ht⟩
  unfold realArmDepth
  rw [commonPrefixLength_comm focus parent,
    (commonPrefixLength_eq_length_left).2 hparent,
    commonPrefixLength_comm focus (parent ++ [x]),
    (commonPrefixLength_eq_length_left).2 hpre]
  simp [List.length_append]
  have hle : parent.length + 1 ≤ focus.length := by
    rcases hpre with ⟨t, ht⟩
    have := congrArg List.length ht
    simp at this
    omega
  omega

def armDepth (focus : List Atom) : CarrierNode Atom → Nat
  | .real path => realArmDepth focus path
  | .ring path _ => realArmDepth focus path + 1

/-- Parent in the tree rerooted at the real path `focus`. Ancestors step toward `focus`; every
other node keeps its original carrier parent. -/
def rawNewParent (focus : List Atom) (node : CarrierNode Atom) : Option (CarrierNode Atom) :=
  if node = .real focus then
    none
  else
    match node with
    | .real path =>
        if h : path.length < focus.length ∧ focus.take path.length = path then
          some (.real (path ++ [focus[path.length]]))
        else
          some (.real path.dropLast)
    | .ring path _ =>
        some (.real path)

theorem rawNewParent_focus (focus : List Atom) :
    rawNewParent focus (.real focus) = none := by
  simp [rawNewParent]

theorem adj_of_strict_prefix {focus path : List Atom}
    (hfocus : ChainFrom molecule root focus) (hlen : path.length < focus.length)
    (htake : focus.take path.length = path) (hne : path ≠ []) :
    ChainFrom molecule root (path ++ [focus[path.length]]) ∧
      ∃ current, path.getLast? = some current ∧
        molecule.Adj current (focus[path.length]) := by
  have hstep : focus.take (path.length + 1) =
      path ++ [focus[path.length]] := by
    rw [List.take_succ_eq_append_getElem hlen, htake]
  have hchain := ChainFrom.take_chain hfocus (n := path.length + 1) (by omega) (by omega)
  rw [hstep] at hchain
  obtain ⟨current, hprefix, hlast, hadj⟩ := ChainFrom.snoc_inv hchain hne
  exact ⟨hchain, current, hlast, hadj⟩

theorem rawNewParent_spec {focus : List Atom} {node : CarrierNode Atom}
    (hfocus : SimpleFrom molecule root focus)
    (hnode : CarrierNode.Valid molecule root node) (hne : node ≠ .real focus) :
    ∃ parent, rawNewParent focus node = some parent ∧
      CarrierNode.Valid molecule root parent ∧
      armDepth focus node = armDepth focus parent + 1 := by
  cases node with
  | ring path atom =>
      have hraw : rawNewParent focus (.ring path atom) = some (.real path) := by
        simp [rawNewParent]
      refine ⟨.real path, hraw, hnode.1, ?_⟩
      simp [armDepth]
  | real path =>
      by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
      · have hlen : path.length < focus.length := hpre.1
        have htake : focus.take path.length = path := hpre.2
        have hpathNe : path ≠ [] := SimpleFrom.ne_nil hnode
        obtain ⟨hchain, current, hlast, hadj⟩ :=
          adj_of_strict_prefix hfocus.1 hlen htake hpathNe
        set next := focus[path.length]
        have hnd : (path ++ [next]).Nodup := by
          have htakeStep : focus.take (path.length + 1) = path ++ [next] := by
            simpa [next] using (List.take_succ_eq_append_getElem hlen).trans (by rw [htake])
          have hsub : (path ++ [next]).Nodup := by
            rw [← htakeStep]
            exact hfocus.2.sublist (List.take_sublist _ _)
          exact hsub
        have hparent : SimpleFrom molecule root (path ++ [next]) := ⟨hchain, hnd⟩
        have hraw : rawNewParent focus (.real path) = some (.real (path ++ [next])) := by
          unfold rawNewParent
          rw [if_neg hne]
          simp [hpre, next]
        refine ⟨.real (path ++ [next]), hraw, hparent, ?_⟩
        have hprefix : path ++ [next] <+: focus := by
          refine ⟨focus.drop (path.length + 1), ?_⟩
          have htakeStep : focus.take (path.length + 1) = path ++ [next] := by
            simpa [next] using (List.take_succ_eq_append_getElem hlen).trans (by rw [htake])
          simpa [htakeStep] using List.take_append_drop (path.length + 1) focus
        simpa [armDepth] using realArmDepth_prefix_step focus path next hprefix
      · have hlen2 : 1 < path.length := by
          have hpathNe : path ≠ [] := SimpleFrom.ne_nil hnode
          have hpos : 0 < path.length := List.length_pos_iff.mpr hpathNe
          by_contra hshort
          have hlen1 : path.length = 1 := by omega
          have hpathRoot : path = [root] := by
            have hhead := SimpleFrom.head?_eq hnode
            cases path with
            | nil => simp at hlen1
            | cons a as =>
                cases as with
                | nil =>
                    simp at hhead
                    exact hhead ▸ rfl
                | cons => simp at hlen1
          have hfocusNe : focus ≠ [] := SimpleFrom.ne_nil hfocus
          by_cases hfl : focus.length = 1
          · have hfocusRoot : focus = [root] := by
              have hhead := SimpleFrom.head?_eq hfocus
              cases focus with
              | nil => simp at hfl
              | cons a as =>
                  cases as with
                  | nil =>
                      simp at hhead
                      exact hhead ▸ rfl
                  | cons => simp at hfl
            exact hne (by simp [hpathRoot, hfocusRoot])
          · have hfl2 : 1 < focus.length := by
              have : 0 < focus.length := List.length_pos_iff.mpr hfocusNe
              omega
            have htake1 : focus.take 1 = [root] := by
              have hhead := SimpleFrom.head?_eq hfocus
              cases focus with
              | nil => simp at hfocusNe
              | cons a as =>
                  simp at hhead
                  subst a
                  rfl
            exact hpre ⟨by simpa [hpathRoot, hlen1] using hfl2, by
              simpa [hpathRoot, hlen1] using htake1⟩
        have hparentSimple : SimpleFrom molecule root path.dropLast :=
          SimpleFrom.dropLast hnode hlen2
        have hnotPrefix : ¬ path <+: focus := by
          intro hprefix
          have hlenle : path.length ≤ focus.length := by
            rcases hprefix with ⟨t, ht⟩
            have := congrArg List.length ht
            simp at this
            omega
          by_cases hlt : path.length < focus.length
          · exact hpre ⟨hlt, (List.prefix_iff_eq_take.mp hprefix).symm⟩
          · have heq : path.length = focus.length := by omega
            rcases hprefix with ⟨t, ht⟩
            have htlen : t.length = 0 := by
              have := congrArg List.length ht
              simp at this
              omega
            simp at htlen
            subst t
            simp at ht
            exact hne (by simp [ht])
        have hsplit : path = path.dropLast ++ [path.getLast (SimpleFrom.ne_nil hnode)] :=
          (List.dropLast_append_getLast _).symm
        have hdepth : realArmDepth focus path =
            realArmDepth focus path.dropLast + 1 := by
          have hnotExt : ¬ path.dropLast ++ [path.getLast (SimpleFrom.ne_nil hnode)] <+: focus := by
            intro hbad
            exact hnotPrefix (hsplit.symm ▸ hbad)
          have hstep := realArmDepth_append_not_prefix focus path.dropLast
            (path.getLast (SimpleFrom.ne_nil hnode)) hnotExt
          rw [← hsplit] at hstep
          exact hstep
        have hraw : rawNewParent focus (.real path) = some (.real path.dropLast) := by
          unfold rawNewParent
          rw [if_neg hne]
          simp [hpre]
        refine ⟨.real path.dropLast, hraw, hparentSimple, ?_⟩
        simpa [armDepth] using hdepth

def armChild (focus : List Atom) (parent node : Nodes molecule root) : Prop :=
  rawNewParent focus node.1 = some parent.1

theorem armDepth_focus (focus : List Atom) : armDepth focus (.real focus) = 0 := by
  simp [armDepth, realArmDepth_eq_zero_iff]

theorem armDepth_eq_zero_iff {focus : List Atom} {node : CarrierNode Atom}
    (_hfocus : SimpleFrom molecule root focus)
    (_hnode : CarrierNode.Valid molecule root node) :
    armDepth focus node = 0 ↔ node = .real focus := by
  cases node with
  | real path =>
      simp [armDepth, realArmDepth_eq_zero_iff]
  | ring _ _ =>
      simp [armDepth]

theorem realArm_reachable (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (node : Nodes molecule root) :
    Relation.ReflTransGen (armChild focus) ⟨.real focus, hfocus⟩ node := by
  suffices ∀ n, ∀ node : Nodes molecule root, armDepth focus node.1 = n →
      Relation.ReflTransGen (armChild focus) ⟨.real focus, hfocus⟩ node by
    exact this _ node rfl
  intro n
  induction n with
  | zero =>
      intro node hzero
      have hnode : node.1 = .real focus :=
        (armDepth_eq_zero_iff hfocus node.2).1 hzero
      cases node with
      | mk val hv =>
          cases hnode
          exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro node hn
      have hne : node.1 ≠ .real focus := by
        intro heq
        have : armDepth focus node.1 = 0 := by rw [heq, armDepth_focus]
        omega
      obtain ⟨parent, hraw, hvalid, hdepth⟩ := rawNewParent_spec hfocus node.2 hne
      have hdep : armDepth focus parent = n := by
        have : armDepth focus node.1 = n + 1 := hn
        omega
      exact Relation.ReflTransGen.tail (ih ⟨parent, hvalid⟩ hdep) hraw

/-- The prefix tree rerooted at a real occurrence, still containing every carrier node.
The original parent is reattached as a child and its subtree is kept. Labels stay outer-root
labels. This is not the predecessor-cut ligand arm. -/
def realRetainedArm (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus) : RootedDigraph Atom where
  Node := Nodes molecule root
  nodeFintype := @Fintype.ofFinite _ (valid_finite molecule root).to_subtype
  root := ⟨.real focus, hfocus⟩
  child := armChild focus
  label := fun node => CarrierNode.label node.1
  depth := fun node => armDepth focus node.1
  root_depth := armDepth_focus focus
  child_depth := by
    intro parent node hchild
    have hne : node.1 ≠ .real focus := by
      intro heq
      have hnone : rawNewParent focus node.1 = none := by
        simp [heq, rawNewParent_focus]
      have hcontra : none = some parent.1 := by simpa [armChild, hnone] using hchild
      cases hcontra
    obtain ⟨parentVal, hraw, _hvalid, hdepth⟩ := rawNewParent_spec hfocus node.2 hne
    have hparent : parent.1 = parentVal :=
      Option.some_inj.mp (hchild.symm.trans hraw)
    simpa [hparent] using hdepth
  reachable := realArm_reachable molecule root hfocus

/-- A ring occurrence is already terminal. Removing its incoming carrier edge leaves a one-node arm
whose label is still the original closure. -/
def ringTerminalArm (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} {atom : Atom}
    (_h : CarrierNode.Valid molecule root (.ring path atom)) : RootedDigraph Atom where
  Node := PUnit.{u + 1}
  nodeFintype := inferInstance
  root := ⟨⟩
  child := fun _ _ => False
  label := fun _ => CarrierNode.label (.ring path atom)
  depth := fun _ => 0
  root_depth := rfl
  child_depth := fun hedge => hedge.elim
  reachable := fun _ => Relation.ReflTransGen.refl

/-- Uncut full reroot at `focus`. A real focus keeps every carrier node, including the
predecessor subtree. A ring focus is the one-node terminal arm. Not the predecessor-cut
ligand arm (`cutRetainedArm`). -/
def retainedArm (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) : RootedDigraph Atom :=
  match focus with
  | ⟨.real _, h⟩ => realRetainedArm molecule root h
  | ⟨.ring _ _, h⟩ => ringTerminalArm molecule root h

/-- Isomorphism to the uncut full reroot `retainedArm`. This does not assert that the
predecessor component was removed, and it is not `FaithfulExactExpansion`. -/
def FullRerootFaithful (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (graph : RootedDigraph Atom) : Prop :=
  Nonempty (RootedDigraph.Iso (retainedArm molecule root focus) graph)

theorem fullRerootFaithful_self (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) :
    FullRerootFaithful molecule root focus (retainedArm molecule root focus) :=
  ⟨RootedDigraph.Iso.refl _⟩

theorem fullRerootFaithful_iso (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) {graph₁ graph₂ : RootedDigraph Atom}
    (h : FullRerootFaithful molecule root focus graph₁)
    (iso : RootedDigraph.Iso graph₁ graph₂) :
    FullRerootFaithful molecule root focus graph₂ := by
  rcases h with ⟨iso₁⟩
  exact ⟨iso₁.trans iso⟩

theorem retainedArm_real {path : List Atom} (h : SimpleFrom molecule root path) :
    retainedArm molecule root ⟨.real path, h⟩ = realRetainedArm molecule root h :=
  rfl

theorem retainedArm_ring {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    retainedArm molecule root ⟨.ring path atom, h⟩ = ringTerminalArm molecule root h :=
  rfl

theorem realRetainedArm_label (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (node : Nodes molecule root) :
    (realRetainedArm molecule root hfocus).label node = CarrierNode.label node.1 :=
  rfl

theorem retainedArm_real_label {path : List Atom} (h : SimpleFrom molecule root path)
    (node : Nodes molecule root) :
    (retainedArm molecule root ⟨.real path, h⟩).label node = CarrierNode.label node.1 :=
  rfl

theorem retainedArm_ring_label {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    (retainedArm molecule root ⟨.ring path atom, h⟩).label
        (retainedArm molecule root ⟨.ring path atom, h⟩).root =
      CarrierNode.label (.ring path atom) :=
  rfl

theorem realRetainedArm_not_child_root (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (parent : Nodes molecule root) :
    ¬ (realRetainedArm molecule root hfocus).child parent
        (realRetainedArm molecule root hfocus).root := by
  intro hchild
  have hraw : rawNewParent focus (.real focus) = some parent.1 := hchild
  simp [rawNewParent_focus] at hraw

/-- The uncut reroot's root has no parent. The predecessor is still present: for a real
focus of length greater than one, `armChild_focus_iff` includes `focus.dropLast` as a child. -/
theorem fullReroot_root_has_no_parent (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (parent : (retainedArm molecule root focus).Node) :
    ¬ (retainedArm molecule root focus).child parent
        (retainedArm molecule root focus).root := by
  cases focus with
  | mk node hnode =>
      cases node with
      | real path =>
          simpa [retainedArm] using
            realRetainedArm_not_child_root molecule root hnode parent
      | ring path atom =>
          intro hchild
          exact hchild

theorem retainedArm_ring_terminal {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom))
    (parent child : (retainedArm molecule root ⟨.ring path atom, h⟩).Node) :
    ¬ (retainedArm molecule root ⟨.ring path atom, h⟩).child parent child :=
  fun hchild => hchild

theorem realRetainedArm_unique_parent (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {first second node : Nodes molecule root}
    (hfirst : (realRetainedArm molecule root hfocus).child first node)
    (hsecond : (realRetainedArm molecule root hfocus).child second node) :
    first = second := by
  apply Subtype.ext
  have hraw : some first.1 = some second.1 := hfirst.symm.trans hsecond
  exact Option.some_inj.mp hraw

theorem retainedArm_unique_parent (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root)
    {first second node : (retainedArm molecule root focus).Node}
    (hfirst : (retainedArm molecule root focus).child first node)
    (hsecond : (retainedArm molecule root focus).child second node) :
    first = second := by
  cases focus with
  | mk val hval =>
      cases val with
      | real path =>
          exact realRetainedArm_unique_parent molecule root hval hfirst hsecond
      | ring path atom => exact (hfirst : False).elim

theorem realRetainedArm_acyclic (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (node : Nodes molecule root) :
    ¬ Relation.TransGen (realRetainedArm molecule root hfocus).child node node := by
  intro h
  have hlt := depth_lt_of_transGen (graph := realRetainedArm molecule root hfocus) h
  omega

theorem retainedArm_acyclic (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (node : (retainedArm molecule root focus).Node) :
    ¬ Relation.TransGen (retainedArm molecule root focus).child node node := by
  cases focus with
  | mk val hval =>
      cases val with
      | real path =>
          simpa [retainedArm] using realRetainedArm_acyclic molecule root hval node
      | ring path atom =>
          intro h
          cases h with
          | single hedge => exact hedge
          | tail _ hedge => exact hedge

theorem armChild_focus_iff {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (node : Nodes molecule root) :
    armChild focus ⟨.real focus, hfocus⟩ node ↔
      CarrierNode.Child (.real focus) node.1 ∨
        (1 < focus.length ∧ node.1 = .real focus.dropLast) := by
  constructor
  · intro hchild
    have hraw : rawNewParent focus node.1 = some (.real focus) := hchild
    cases node with
    | mk val hval =>
        cases val with
        | real path =>
            have hne : CarrierNode.real path ≠ CarrierNode.real focus := by
              intro heq
              simp at hraw
              cases heq
              simp [rawNewParent] at hraw
            unfold rawNewParent at hraw
            rw [if_neg hne] at hraw
            by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
            · simp [hpre] at hraw
              have hlen : 1 < focus.length := by
                have : path.length < focus.length := hpre.1
                have hpos : 0 < focus.length := by omega
                have hpath : path ≠ [] := SimpleFrom.ne_nil hval
                have : 0 < path.length := List.length_pos_iff.mpr hpath
                omega
              have hdrop : path = focus.dropLast := by
                have happ : path ++ [focus[path.length]] = focus := by
                  simpa using hraw
                rw [← happ, List.dropLast_concat]
              exact Or.inr ⟨hlen, by simp [hdrop]⟩
            · simp [hpre] at hraw
              have hdropPath : path.dropLast = focus := by
                simpa using hraw
              have hpath : path = focus ++ [path.getLast (SimpleFrom.ne_nil hval)] := by
                rw [← hdropPath]
                exact (List.dropLast_concat_getLast (SimpleFrom.ne_nil hval)).symm
              exact Or.inl ⟨path.getLast (SimpleFrom.ne_nil hval), hpath⟩
        | ring path atom =>
            simp [rawNewParent] at hraw
            subst hraw
            exact Or.inl rfl
  · intro h
    cases node with
    | mk val hval =>
        rcases h with hchild | ⟨hlen, hparent⟩
        · cases val with
          | real path =>
              obtain ⟨atom, rfl⟩ := hchild
              have hne : CarrierNode.real (focus ++ [atom]) ≠ CarrierNode.real focus := by
                intro heq
                have := congrArg (fun node : CarrierNode Atom =>
                  match node with
                  | .real path => path.length
                  | .ring path _ => path.length) heq
                simp at this
              unfold armChild rawNewParent
              rw [if_neg hne]
              have hnot : ¬ ((focus ++ [atom]).length < focus.length ∧
                  focus.take (focus ++ [atom]).length = focus ++ [atom]) := by
                intro hpre
                have := hpre.1
                simp at this
              simp
          | ring path atom =>
              cases hchild
              unfold armChild rawNewParent
              simp
        · cases val with
          | ring _ _ => simp at hparent
          | real path =>
              simp at hparent
              subst path
              have hne : CarrierNode.real focus.dropLast ≠ CarrierNode.real focus := by
                intro heq
                have := congrArg (fun node : CarrierNode Atom =>
                  match node with
                  | .real path => path.length
                  | .ring path _ => path.length) heq
                simp [List.length_dropLast] at this
                omega
              unfold armChild rawNewParent
              rw [if_neg hne]
              have hleft := List.take_append_getLast focus (SimpleFrom.ne_nil hfocus)
              have hright := List.dropLast_append_getLast (l := focus)
                (SimpleFrom.ne_nil hfocus)
              have hpref : focus.take (focus.length - 1) = focus.dropLast :=
                List.append_inj_left' (hleft.trans hright.symm) (by simp)
              have hi : focus.length - 1 < focus.length := by omega
              have htake := List.take_succ_eq_append_getElem (l := focus) hi
              have htake' : focus.take (focus.length - 1 + 1) =
                  focus.dropLast ++ [focus[focus.length - 1]] := by
                rw [hpref] at htake
                exact htake
              have hsucc : focus.length - 1 + 1 = focus.length := by omega
              have hstep : focus.dropLast ++ [focus[focus.length - 1]] = focus := by
                have hrev : focus = focus.dropLast ++ [focus[focus.length - 1]] := by
                  simpa [hsucc, List.take_length] using htake'
                exact hrev.symm
              have hcond : 0 < focus.length ∧
                  focus.take (focus.length - 1) = focus.dropLast :=
                ⟨by omega, hpref⟩
              simp [hcond, hstep]

end

end RetainedOccurrenceCarrier
end DeclarativeCIP
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.real_valid_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.ring_valid_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.provenance_real_iff_nodup
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.label_ring_distance
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.provenance_ne_multipleBond
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.valid_finite
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.retainedCarrier_unique_parent
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.retainedCarrier_acyclic
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.retainedCarrier_real_ancestor_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.ring_distance_eq_ancestor_depth
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.occurrenceReadback_eq_history_reverse_tail
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.reentry_readback_eq_rerootStep
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.outward_readback_eq_rerootStep
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.ring_readback_eq_rerootStep
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.neighbor_child_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.simpleBonded_neighbor_child_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.fullReroot_root_has_no_parent
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.retainedArm_ring_terminal
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.retainedArm_unique_parent
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.retainedArm_acyclic
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.retainedArm_real_label
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.fullRerootFaithful_self
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.fullRerootFaithful_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedOccurrenceCarrier.armChild_focus_iff
