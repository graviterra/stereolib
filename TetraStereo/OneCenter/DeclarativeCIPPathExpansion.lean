import TetraStereo.OneCenter.DeclarativeCIPFaithfulCanonicalOutcome
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

/-!
# Every bonded ligand has a faithful exact expansion

The totality theorem for the declarative constitutional rules assumes that each ligand has an
admissible expansion.  This module removes that assumption for faithful exact expansions: it builds
the hierarchical path model of an arbitrary molecule and proves it faithful
(`pathExpansion_faithful`).

* Real nodes are simple bond paths from the ligand that avoid the external stereocenter, stored
  head-first.
* Below a real node with atom `a`, each bonded atom `b` contributes `bond a b - 1` multiple-bond
  duplicates, a real child if `b` is absent from the branch history, and one ring duplicate if `b`
  is a non-parent member of the branch history.
* Every rooted digraph whose nodes have unique parents admits a parent-preserving addressing
  (`exists_addressing_of_unique_parent`), so no addressing has to be chosen by hand.

Consequently `withFaithfulCanonicalSemantics` instantiates `ConstitutionalProblemData` for any
molecule whose stereounit ligands are bonded to their centers, and its Rule 1a, 1b, and 2
`RuleOutcome`s exist and are unique for every pair of ligands
(`withFaithfulCanonicalSemantics_ruleOutcome_existsUnique`).
-/

variable {Atom : Type u}

/-! ## Addressings from unique parents -/

namespace RootedDigraph

section UniqueParent

variable (graph : RootedDigraph Atom)
  (hunique : ∀ {first second node : graph.Node}, graph.child first node →
    graph.child second node → first = second)

local instance : Fintype graph.Node := graph.nodeFintype

theorem not_child_root_of_depth (parent : graph.Node) : ¬ graph.child parent graph.root := by
  intro hedge
  have := graph.child_depth hedge
  rw [graph.root_depth] at this
  omega

theorem exists_parent {node : graph.Node} (h : node ≠ graph.root) :
    ∃ parent, graph.child parent node := by
  rcases (graph.reachable node).cases_tail with hroot | ⟨parent, _, hedge⟩
  · exact (h hroot).elim
  · exact ⟨parent, hedge⟩

/-- A parent of each non-root node. -/
def someParent (node : graph.Node) : graph.Node :=
  if h : node = graph.root then graph.root
  else Classical.choose (graph.exists_parent h)

theorem someParent_child {node : graph.Node} (h : node ≠ graph.root) :
    graph.child (graph.someParent node) node := by
  unfold someParent
  rw [dif_neg h]
  exact Classical.choose_spec (graph.exists_parent h)

include hunique in
theorem someParent_eq {parent node : graph.Node} (hedge : graph.child parent node) :
    graph.someParent node = parent := by
  have hne : node ≠ graph.root := by
    rintro rfl
    exact graph.not_child_root_of_depth parent hedge
  exact hunique (graph.someParent_child hne) hedge

/-- Slot-by-rank address along unique parents. -/
def rankAddress (node : graph.Node) : List ℕ :=
  if _hroot : node = graph.root then []
  else rankAddress (graph.someParent node) ++
    [(graph.childList (graph.someParent node)).idxOf node]
termination_by graph.depth node
decreasing_by
  have := graph.child_depth (graph.someParent_child _hroot)
  omega

theorem rankAddress_root : graph.rankAddress graph.root = [] := by
  rw [rankAddress, dif_pos rfl]

include hunique in
theorem rankAddress_child {parent node : graph.Node} (hedge : graph.child parent node) :
    graph.rankAddress node =
      graph.rankAddress parent ++ [(graph.childList parent).idxOf node] := by
  have hne : node ≠ graph.root := by
    rintro rfl
    exact graph.not_child_root_of_depth parent hedge
  rw [rankAddress, dif_neg hne, graph.someParent_eq hunique hedge]

include hunique in
theorem rankAddress_eq_nil_iff (node : graph.Node) :
    graph.rankAddress node = [] ↔ node = graph.root := by
  constructor
  · intro h
    by_contra hne
    rw [graph.rankAddress_child hunique (graph.someParent_child hne)] at h
    simp at h
  · rintro rfl
    exact graph.rankAddress_root

include hunique in
theorem rankAddress_injective : Function.Injective graph.rankAddress := by
  intro first
  have hreachable := graph.reachable first
  induction hreachable with
  | refl =>
      intro second h
      rw [rankAddress_root] at h
      exact ((graph.rankAddress_eq_nil_iff hunique second).1 h.symm).symm
  | @tail parent node _ hedge ih =>
      intro second h
      have hsecond : second ≠ graph.root := by
        rintro rfl
        rw [rankAddress_root, graph.rankAddress_child hunique hedge] at h
        simp at h
      have hsecondEdge := graph.someParent_child hsecond
      rw [graph.rankAddress_child hunique hedge,
        graph.rankAddress_child hunique hsecondEdge] at h
      obtain ⟨hfront, hlast⟩ := List.append_inj' h rfl
      have hparent : parent = graph.someParent second := ih hfront
      rw [← hparent] at hlast
      have hidx : (graph.childList parent).idxOf node = (graph.childList parent).idxOf second := by
        simpa using hlast
      exact (List.idxOf_inj ((graph.mem_childList).2 hedge)).1 hidx

/-- **Unique parents give an addressing.** -/
def addressingOfUniqueParent : graph.Addressing where
  address := graph.rankAddress
  address_injective := graph.rankAddress_injective hunique
  root_address := graph.rankAddress_root
  child_iff := by
    intro parent node
    constructor
    · intro h
      exact ⟨_, graph.rankAddress_child hunique h⟩
    · rintro ⟨slot, hslot⟩
      have hne : node ≠ graph.root := by
        rintro rfl
        rw [rankAddress_root] at hslot
        simp at hslot
      have hedge := graph.someParent_child hne
      rw [graph.rankAddress_child hunique hedge] at hslot
      obtain ⟨hfront, _⟩ := List.append_inj' hslot rfl
      rw [← graph.rankAddress_injective hunique hfront]
      exact hedge

include hunique in
theorem exists_addressing_of_unique_parent : Nonempty graph.Addressing :=
  ⟨graph.addressingOfUniqueParent hunique⟩

end UniqueParent

end RootedDigraph

/-! ## The path model -/

/-- Raw nodes of the path model.  Paths are stored head-first: the represented atom first, the
ligand last. -/
inductive PathNode (Atom : Type u) where
  | real (path : List Atom)
  | bondDuplicate (path : List Atom) (atom : Atom) (index : ℕ)
  | ringDuplicate (path : List Atom) (atom : Atom)

section PathModel

variable [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (externalParent ligand : Atom)

/-- Head-first bond chains ending at the ligand. -/
def ChainToLigand : List Atom → Prop
  | [] => False
  | [atom] => atom = ligand
  | atom :: next :: rest => molecule.Adj atom next ∧ ChainToLigand (next :: rest)

/-- Branch paths: bond chains to the ligand without repeated atoms or the external stereocenter. -/
def SimplePath (path : List Atom) : Prop :=
  ChainToLigand molecule ligand path ∧ path.Nodup ∧ externalParent ∉ path

/-- The single ring duplicate of `atom` below a path is present exactly when `atom` is bonded,
belongs to the branch history, and is not the suppressed parent. -/
def RingAllowed (path : List Atom) (atom : Atom) : Prop :=
  ∃ current, path.head? = some current ∧ molecule.Adj current atom ∧
    (atom = externalParent ∨ atom ∈ path.tail) ∧
    ¬ ((path.tail = [] ∧ atom = externalParent) ∨ path.tail.head? = some atom)

/-- Valid path-model nodes. -/
def PathNode.Valid : PathNode Atom → Prop
  | .real path => SimplePath molecule externalParent ligand path
  | .bondDuplicate path atom index => SimplePath molecule externalParent ligand path ∧
      ∃ current, path.head? = some current ∧ index + 1 < molecule.bond current atom
  | .ringDuplicate path atom => SimplePath molecule externalParent ligand path ∧
      RingAllowed molecule externalParent path atom

/-- The path-model child relation. -/
def PathNode.Child : PathNode Atom → PathNode Atom → Prop
  | .real path, .real child => ∃ atom, child = atom :: path
  | .real path, .bondDuplicate child _ _ => child = path
  | .real path, .ringDuplicate child _ => child = path
  | _, _ => False

/-- Labels: duplicate payloads are the attached atom's sphere for multiple bonds and the duplicated
ancestor's sphere for ring closures (`0` for the external stereocenter). -/
def PathNode.label : PathNode Atom → NodeLabel Atom
  | .real path => ⟨path.head?, NodeProvenance.realAtom⟩
  | .bondDuplicate path atom _ => ⟨some atom, NodeProvenance.multipleBondDuplicate path.length⟩
  | .ringDuplicate path atom => ⟨some atom, NodeProvenance.ringDuplicate
      (if atom = externalParent then 0 else path.length - path.idxOf atom)⟩

def PathNode.depth : PathNode Atom → ℕ
  | .real path => path.length - 1
  | .bondDuplicate path _ _ => path.length
  | .ringDuplicate path _ => path.length

theorem chainToLigand_ne_nil {path : List Atom} (h : ChainToLigand molecule ligand path) :
    path ≠ [] := by
  rintro rfl
  exact h

theorem simplePath_tail {atom : Atom} {path : List Atom} (hpath : path ≠ [])
    (h : SimplePath molecule externalParent ligand (atom :: path)) :
    SimplePath molecule externalParent ligand path := by
  obtain ⟨hchain, hnodup, hext⟩ := h
  refine ⟨?_, hnodup.of_cons, fun hmem => hext (List.mem_cons_of_mem _ hmem)⟩
  rcases path with _ | ⟨next, rest⟩
  · exact (hpath rfl).elim
  · exact hchain.2

theorem simplePath_cons_iff {atom current : Atom} {rest : List Atom}
    (h : SimplePath molecule externalParent ligand (current :: rest)) :
    SimplePath molecule externalParent ligand (atom :: current :: rest) ↔
      molecule.Adj atom current ∧ atom ∉ current :: rest ∧ atom ≠ externalParent := by
  obtain ⟨hchain, hnodup, hext⟩ := h
  constructor
  · rintro ⟨⟨hadj, _⟩, hnd, hex⟩
    exact ⟨hadj, (List.nodup_cons.1 hnd).1, fun heq => hex (heq ▸ List.mem_cons_self)⟩
  · rintro ⟨hadj, hnot, hne⟩
    refine ⟨⟨hadj, hchain⟩, List.nodup_cons.2 ⟨hnot, hnodup⟩, ?_⟩
    rintro (_ | ⟨_, hmem⟩)
    · exact hne rfl
    · exact hext hmem

theorem simplePath_singleton_iff {atom : Atom} :
    SimplePath molecule externalParent ligand [atom] ↔ atom = ligand ∧ atom ≠ externalParent := by
  unfold SimplePath ChainToLigand
  simp [eq_comm]

omit [DecidableEq Atom] in
theorem finite_lists_length_le (n : ℕ) : {path : List Atom | path.length ≤ n}.Finite := by
  have hcover : {path : List Atom | path.length ≤ n} ⊆
      ⋃ k ∈ Set.Iic n, Set.range (fun vector : List.Vector Atom k => vector.toList) := by
    intro path hpath
    simp only [Set.mem_iUnion, Set.mem_Iic]
    exact ⟨path.length, hpath, ⟨path, rfl⟩, rfl⟩
  exact Set.Finite.subset ((Set.finite_Iic n).biUnion fun k _ => Set.finite_range _) hcover

theorem finite_valid :
    Set.Finite {node : PathNode Atom | node.Valid molecule externalParent ligand} := by
  let N := Fintype.card Atom
  obtain ⟨B, hB⟩ : ∃ B, ∀ first second, molecule.bond first second < B :=
    ⟨Finset.univ.sup (fun pair : Atom × Atom => molecule.bond pair.1 pair.2) + 1,
      fun first second => Nat.lt_succ_of_le (Finset.le_sup
        (f := fun pair : Atom × Atom => molecule.bond pair.1 pair.2)
        (Finset.mem_univ (first, second)))⟩
  have hpaths := finite_lists_length_le (Atom := Atom) N
  have hcover : {node : PathNode Atom | node.Valid molecule externalParent ligand} ⊆
      (PathNode.real '' {path : List Atom | path.length ≤ N}) ∪
        ((fun x : List Atom × Atom × ℕ => PathNode.bondDuplicate x.1 x.2.1 x.2.2) ''
          ({path : List Atom | path.length ≤ N} ×ˢ (Set.univ ×ˢ Set.Iio B))) ∪
        ((fun x : List Atom × Atom => PathNode.ringDuplicate x.1 x.2) ''
          ({path : List Atom | path.length ≤ N} ×ˢ Set.univ)) := by
    intro node hnode
    have hlen : ∀ {path : List Atom}, SimplePath molecule externalParent ligand path →
        path.length ≤ N := fun h => h.2.1.length_le_card
    cases node with
    | real path => exact Or.inl (Or.inl ⟨path, hlen hnode, rfl⟩)
    | bondDuplicate path atom index =>
        obtain ⟨hpath, current, _, hindex⟩ := hnode
        have hbound := hB current atom
        refine Or.inl (Or.inr ⟨(path, atom, index), ⟨hlen hpath, trivial, ?_⟩, rfl⟩)
        show index < B
        exact lt_trans (Nat.lt_of_succ_lt hindex) hbound
    | ringDuplicate path atom =>
        exact Or.inr ⟨(path, atom), ⟨hlen hnode.1, trivial⟩, rfl⟩
  refine Set.Finite.subset (Set.Finite.union (Set.Finite.union (hpaths.image _) ?_) ?_) hcover
  · exact (hpaths.prod (Set.finite_univ.prod (Set.finite_Iio B))).image _
  · exact (hpaths.prod Set.finite_univ).image _

variable {molecule externalParent ligand}

theorem root_valid (hbond : molecule.Adj externalParent ligand) :
    (PathNode.real [ligand]).Valid molecule externalParent ligand := by
  refine (simplePath_singleton_iff molecule externalParent ligand).2 ⟨rfl, ?_⟩
  intro heq
  rw [heq] at hbond
  exact not_adj_self molecule _ hbond

variable (molecule externalParent ligand)

/-- **The path expansion** of `ligand` seen from `externalParent`. -/
def pathExpansion (hbond : molecule.Adj externalParent ligand) : RootedDigraph Atom where
  Node := {node : PathNode Atom // node.Valid molecule externalParent ligand}
  nodeFintype := @Fintype.ofFinite _ (finite_valid molecule externalParent ligand).to_subtype
  root := ⟨.real [ligand], root_valid hbond⟩
  child := fun parent node => PathNode.Child parent.1 node.1
  label := fun node => PathNode.label externalParent node.1
  depth := fun node => node.1.depth
  root_depth := rfl
  child_depth := by
    rintro ⟨parent, hparent⟩ ⟨node, hnode⟩ hedge
    cases parent with
    | real path =>
        have hne := chainToLigand_ne_nil molecule ligand hparent.1
        cases node with
        | real child =>
            obtain ⟨atom, rfl⟩ := hedge
            simp only [PathNode.depth, List.length_cons]
            have := List.length_pos_iff.2 hne
            omega
        | bondDuplicate child _ _ =>
            cases hedge
            simp only [PathNode.depth]
            have := List.length_pos_iff.2 hne
            omega
        | ringDuplicate child _ =>
            cases hedge
            simp only [PathNode.depth]
            have := List.length_pos_iff.2 hne
            omega
    | bondDuplicate _ _ _ => cases node <;> exact hedge.elim
    | ringDuplicate _ _ => cases node <;> exact hedge.elim
  reachable := by
    have hreal : ∀ (path : List Atom) (hpath : SimplePath molecule externalParent ligand path),
        Relation.ReflTransGen (fun parent node : {node : PathNode Atom //
            node.Valid molecule externalParent ligand} => PathNode.Child parent.1 node.1)
          ⟨.real [ligand], root_valid hbond⟩ ⟨.real path, hpath⟩ := by
      intro path
      induction path with
      | nil => intro hpath; exact (chainToLigand_ne_nil molecule ligand hpath.1 rfl).elim
      | cons atom rest ih =>
          intro hpath
          rcases rest with _ | ⟨next, rest⟩
          · have h := ((simplePath_singleton_iff molecule externalParent ligand).1 hpath).1
            subst h
            exact Relation.ReflTransGen.refl
          · have htail := simplePath_tail molecule externalParent ligand (by simp) hpath
            exact Relation.ReflTransGen.tail (ih htail) ⟨atom, rfl⟩
    rintro ⟨node, hnode⟩
    cases node with
    | real path => exact hreal path hnode
    | bondDuplicate path atom index =>
        exact Relation.ReflTransGen.tail (hreal path hnode.1) (show path = path from rfl)
    | ringDuplicate path atom =>
        exact Relation.ReflTransGen.tail (hreal path hnode.1) (show path = path from rfl)

variable {molecule externalParent ligand}

theorem pathExpansion_unique_parent (hbond : molecule.Adj externalParent ligand)
    {first second node : (pathExpansion molecule externalParent ligand hbond).Node}
    (hfirst : (pathExpansion molecule externalParent ligand hbond).child first node)
    (hsecond : (pathExpansion molecule externalParent ligand hbond).child second node) :
    first = second := by
  obtain ⟨first, hf⟩ := first
  obtain ⟨second, hs⟩ := second
  obtain ⟨node, hn⟩ := node
  change PathNode.Child first node at hfirst
  change PathNode.Child second node at hsecond
  apply Subtype.ext
  cases first <;> cases second <;> cases node <;> simp_all [PathNode.Child]
  all_goals
    obtain ⟨_, rfl⟩ := hfirst
    obtain ⟨_, h⟩ := hsecond
    exact (List.cons.inj h).2

/-! ## Ancestors, parents and the root of path nodes -/

open RootedDigraph

section Structure

variable {hbond : molecule.Adj externalParent ligand}

local notation "G" => pathExpansion molecule externalParent ligand hbond

@[simp] theorem pathExpansion_child {x y : (G).Node} :
    (G).child x y ↔ PathNode.Child x.1 y.1 := Iff.rfl

@[simp] theorem pathExpansion_label (x : (G).Node) :
    (G).label x = PathNode.label externalParent x.1 := rfl

@[simp] theorem pathExpansion_depth (x : (G).Node) : (G).depth x = x.1.depth := rfl

theorem pathExpansion_root : (G).root = ⟨.real [ligand], root_valid hbond⟩ := rfl

theorem simplePath_suffix : ∀ (front suffix : List Atom), suffix ≠ [] →
    SimplePath molecule externalParent ligand (front ++ suffix) →
      SimplePath molecule externalParent ligand suffix
  | [], _, _, h => h
  | atom :: front, suffix, hne, h =>
      simplePath_suffix front suffix hne
        (simplePath_tail molecule externalParent ligand (by simp [hne]) h)

/-- A proper nonempty suffix of a real path is a strict ancestor. -/
theorem transGen_of_suffix : ∀ (front suffix : List Atom), front ≠ [] → suffix ≠ [] →
    ∀ (hsuffix : SimplePath molecule externalParent ligand suffix)
      (hpath : SimplePath molecule externalParent ligand (front ++ suffix)),
      Relation.TransGen (G).child ⟨.real suffix, hsuffix⟩ ⟨.real (front ++ suffix), hpath⟩
  | [], _, hne, _, _, _ => (hne rfl).elim
  | [atom], suffix, _, _, _, _ => Relation.TransGen.single ⟨atom, rfl⟩
  | atom :: next :: front, suffix, _, hne, hsuffix, hpath => by
      have hmid := simplePath_tail molecule externalParent ligand (by simp) hpath
      exact Relation.TransGen.tail (transGen_of_suffix (next :: front) suffix (by simp) hne
        hsuffix hmid) ⟨atom, rfl⟩

/-- Strict ancestors of a real path node are its proper nonempty suffixes. -/
theorem ancestor_of_transGen {ancestor node : (G).Node}
    (h : Relation.TransGen (G).child ancestor node) :
    ∀ path, node.1 = .real path → ∃ suffix front, ancestor.1 = .real suffix ∧ front ≠ [] ∧
      path = front ++ suffix := by
  induction h with
  | @single node hedge =>
      intro path hnode
      obtain ⟨anc, hanc⟩ := ancestor
      obtain ⟨n, hn⟩ := node
      simp only at hnode
      subst hnode
      cases anc with
      | real suffix =>
          obtain ⟨atom, rfl⟩ := hedge
          exact ⟨suffix, [atom], rfl, by simp, rfl⟩
      | bondDuplicate _ _ _ => exact hedge.elim
      | ringDuplicate _ _ => exact hedge.elim
  | @tail middle node _ hedge ih =>
      intro path hnode
      obtain ⟨m, hm⟩ := middle
      obtain ⟨n, hn⟩ := node
      simp only at hnode
      subst hnode
      cases m with
      | real middlePath =>
          obtain ⟨atom, rfl⟩ := hedge
          obtain ⟨suffix, front, hanc, hfront, rfl⟩ := ih middlePath rfl
          exact ⟨suffix, atom :: front, hanc, by simp, by simp⟩
      | bondDuplicate _ _ _ => exact hedge.elim
      | ringDuplicate _ _ => exact hedge.elim

theorem ancestorAtom_real_iff {path : List Atom}
    (hpath : SimplePath molecule externalParent ligand path) (atom : Atom) :
    AncestorAtom (G) ⟨.real path, hpath⟩ atom ↔ atom ∈ path.tail := by
  constructor
  · rintro ⟨⟨anc, hanc⟩, htrans, hatom⟩
    obtain ⟨suffix, front, hreal, hfront, hsplit⟩ := ancestor_of_transGen htrans path rfl
    simp only at hreal
    subst hreal
    have hne := chainToLigand_ne_nil molecule ligand hanc.1
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hfront
    obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [pathExpansion_label, PathNode.label, List.head?_cons, Option.some.injEq] at hatom
    subst hatom
    rw [hsplit]
    simp
  · intro hmem
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil
      (chainToLigand_ne_nil molecule ligand hpath.1)
    obtain ⟨before, after, hsplit⟩ := List.append_of_mem hmem
    simp only [List.tail_cons] at hsplit
    subst hsplit
    have hfull : first :: (before ++ atom :: after) = (first :: before) ++ (atom :: after) := rfl
    have hsuffix := simplePath_suffix (first :: before) (atom :: after) (by simp)
      (by rw [← hfull]; exact hpath)
    refine ⟨⟨.real (atom :: after), hsuffix⟩, ?_, rfl⟩
    have h := transGen_of_suffix (hbond := hbond) (first :: before) (atom :: after) (by simp)
      (by simp) hsuffix
      (by rw [← hfull]; exact hpath)
    exact h

theorem parentAtom_real_iff {path : List Atom}
    (hpath : SimplePath molecule externalParent ligand path) (atom : Atom) :
    ParentAtom (G) ⟨.real path, hpath⟩ atom ↔ path.tail.head? = some atom := by
  constructor
  · rintro ⟨⟨parent, hparent⟩, hedge, hatom⟩
    cases parent with
    | real parentPath =>
        obtain ⟨first, hfirst⟩ := hedge
        subst hfirst
        simpa using hatom
    | bondDuplicate _ _ _ => exact hedge.elim
    | ringDuplicate _ _ => exact hedge.elim
  · intro htail
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil
      (chainToLigand_ne_nil molecule ligand hpath.1)
    obtain ⟨next, after, rfl⟩ : ∃ next after, rest = next :: after := by
      cases rest with
      | nil => simp at htail
      | cons next after => exact ⟨next, after, rfl⟩
    simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at htail
    subst htail
    refine ⟨⟨.real (next :: after), simplePath_tail molecule externalParent ligand (by simp) hpath⟩,
      ⟨first, rfl⟩, rfl⟩

theorem root_real_iff {path : List Atom} (hpath : SimplePath molecule externalParent ligand path) :
    (⟨.real path, hpath⟩ : (G).Node) = (G).root ↔ path.tail = [] := by
  rw [pathExpansion_root]
  constructor
  · intro h
    have := congrArg Subtype.val h
    simp only [PathNode.real.injEq] at this
    subst this
    rfl
  · intro htail
    apply Subtype.ext
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil
      (chainToLigand_ne_nil molecule ligand hpath.1)
    simp only [List.tail_cons] at htail
    subst htail
    have := ((simplePath_singleton_iff molecule externalParent ligand).1 hpath).1
    subst this
    rfl

theorem branch_real_iff {path : List Atom} (hpath : SimplePath molecule externalParent ligand path)
    (atom : Atom) :
    BranchAncestorAtom (G) externalParent atom ⟨.real path, hpath⟩ ↔
      atom = externalParent ∨ atom ∈ path.tail := by
  unfold BranchAncestorAtom
  rw [ancestorAtom_real_iff]

theorem suppressed_real_iff {path : List Atom}
    (hpath : SimplePath molecule externalParent ligand path) (atom : Atom) :
    SuppressedParentAtom (G) externalParent atom ⟨.real path, hpath⟩ ↔
      (path.tail = [] ∧ atom = externalParent) ∨ path.tail.head? = some atom := by
  unfold SuppressedParentAtom
  rw [root_real_iff, parentAtom_real_iff]

end Structure

/-! ## Counting children -/

theorem card_subtype_eq_of_bijection {α β : Type*} {p : β → Prop} (f : α → β)
    (hf : ∀ a, p (f a)) (hinj : Function.Injective f) (hsurj : ∀ b, p b → ∃ a, f a = b) :
    Nat.card {b // p b} = Nat.card α :=
  (Nat.card_congr (Equiv.ofBijective (fun a => (⟨f a, hf a⟩ : {b // p b}))
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun ⟨b, hb⟩ => by
      obtain ⟨a, ha⟩ := hsurj b hb
      exact ⟨a, Subtype.ext ha⟩⟩)).symm

theorem card_unit_subtype (condition : Prop) :
    Nat.card {_unit : Unit // condition} = if condition then 1 else 0 := by
  by_cases h : condition
  · rw [if_pos h]
    haveI : Unique {_unit : Unit // condition} := ⟨⟨⟨(), h⟩⟩, fun _ => Subtype.ext rfl⟩
    exact Nat.card_unique
  · rw [if_neg h, Nat.card_eq_zero]
    left
    exact ⟨fun x => h x.2⟩

instance finite_index_subtype (n : ℕ) : Finite {index : ℕ // index + 1 < n} :=
  Finite.of_injective (fun i => (⟨i.1, by have := i.2; omega⟩ : Fin n))
    (fun a b h => Subtype.ext (by simpa using congrArg Fin.val h))

theorem card_index_subtype (n : ℕ) : Nat.card {index : ℕ // index + 1 < n} = n - 1 := by
  have e : {index : ℕ // index + 1 < n} ≃ Fin (n - 1) :=
    ⟨fun i => ⟨i.1, by have := i.2; omega⟩, fun i => ⟨i.1, by have := i.2; omega⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem multiplicity_arithmetic (bond : ℕ) (adjacent branch suppressed : Prop)
    [Decidable adjacent] [Decidable branch] [Decidable suppressed]
    (hadj : adjacent ↔ 0 < bond) (hsb : suppressed → branch) (hsa : suppressed → adjacent) :
    (if adjacent ∧ ¬ branch then 1 else 0) + (bond - 1) +
        (if adjacent ∧ branch ∧ ¬ suppressed then 1 else 0) =
      bond - (if suppressed then 1 else 0) := by
  by_cases ha : adjacent <;> by_cases hb : branch <;> by_cases hs : suppressed <;>
    simp_all <;> omega

section Faithful

variable {hbond : molecule.Adj externalParent ligand}

local notation "G" => pathExpansion molecule externalParent ligand hbond

open RootedDigraph

variable {current : Atom} {rest : List Atom}
  (hpath : SimplePath molecule externalParent ligand (current :: rest)) (atom : Atom)

/-- The real child, multiple-bond duplicates and ring duplicate of `atom` below a real node. -/
def childOfAtom :
    ({_unit : Unit // SimplePath molecule externalParent ligand (atom :: current :: rest)} ⊕
        {index : ℕ // index + 1 < molecule.bond current atom}) ⊕
      {_unit : Unit // RingAllowed molecule externalParent (current :: rest) atom} → (G).Node
  | .inl (.inl unit) => ⟨.real (atom :: current :: rest), unit.2⟩
  | .inl (.inr index) => ⟨.bondDuplicate (current :: rest) atom index.1,
      hpath, current, rfl, index.2⟩
  | .inr unit => ⟨.ringDuplicate (current :: rest) atom, hpath, unit.2⟩

theorem childOfAtom_injective : Function.Injective (childOfAtom (hbond := hbond) hpath atom) := by
  intro x y h
  have hv := congrArg Subtype.val h
  rcases x with ((⟨⟨⟩, _⟩ | ⟨i, _⟩) | ⟨⟨⟩, _⟩) <;> rcases y with ((⟨⟨⟩, _⟩ | ⟨j, _⟩) | ⟨⟨⟩, _⟩) <;>
    simp [childOfAtom] at hv
  · rfl
  · subst hv; rfl
  · rfl

theorem childOfAtom_spec : ∀ x,
    (G).child ⟨.real (current :: rest), hpath⟩ (childOfAtom (hbond := hbond) hpath atom x) ∧
      ((G).label (childOfAtom (hbond := hbond) hpath atom x)).atom? = some atom := by
  rintro ((_ | _) | _) <;> exact ⟨by simp [childOfAtom, PathNode.Child],
    by simp [childOfAtom, PathNode.label]⟩

theorem childOfAtom_surjective (y : (G).Node)
    (hy : (G).child ⟨.real (current :: rest), hpath⟩ y ∧ ((G).label y).atom? = some atom) :
    ∃ x, childOfAtom (hbond := hbond) hpath atom x = y := by
  obtain ⟨node, hnode⟩ := y
  obtain ⟨hedge, hatom⟩ := hy
  simp only [pathExpansion_child, pathExpansion_label] at hedge hatom
  cases node with
  | real childPath =>
      obtain ⟨first, rfl⟩ := hedge
      simp only [PathNode.label, List.head?_cons, Option.some.injEq] at hatom
      subst hatom
      exact ⟨.inl (.inl ⟨(), hnode⟩), rfl⟩
  | bondDuplicate childPath childAtom index =>
      change childPath = current :: rest at hedge
      subst hedge
      simp only [PathNode.label, Option.some.injEq] at hatom
      subst hatom
      obtain ⟨_, found, hfound, hindex⟩ := hnode
      simp only [List.head?_cons, Option.some.injEq] at hfound
      subst hfound
      exact ⟨.inl (.inr ⟨index, hindex⟩), rfl⟩
  | ringDuplicate childPath childAtom =>
      change childPath = current :: rest at hedge
      subst hedge
      simp only [PathNode.label, Option.some.injEq] at hatom
      subst hatom
      exact ⟨.inr ⟨(), hnode.2⟩, rfl⟩

include hpath in
theorem realChild_valid_iff :
    SimplePath molecule externalParent ligand (atom :: current :: rest) ↔
      molecule.Adj current atom ∧ ¬ (atom = externalParent ∨ atom ∈ rest) := by
  rw [simplePath_cons_iff molecule externalParent ligand hpath]
  constructor
  · rintro ⟨hadj, hnot, hne⟩
    refine ⟨(molecule.adj_symm).1 hadj, ?_⟩
    rintro (h | h)
    · exact hne h
    · exact hnot (List.mem_cons_of_mem _ h)
  · rintro ⟨hadj, hnot⟩
    refine ⟨(molecule.adj_symm).1 hadj, ?_, fun h => hnot (Or.inl h)⟩
    rintro (_ | ⟨_, hmem⟩)
    · exact not_adj_self molecule _ hadj
    · exact hnot (Or.inr hmem)

theorem ringAllowed_iff :
    RingAllowed molecule externalParent (current :: rest) atom ↔
      molecule.Adj current atom ∧ (atom = externalParent ∨ atom ∈ rest) ∧
        ¬ ((rest = [] ∧ atom = externalParent) ∨ rest.head? = some atom) := by
  unfold RingAllowed
  simp

/-- **Exact child multiplicities** of the path expansion. -/
theorem pathExpansion_multiplicities :
    AtomChildMultiplicities molecule externalParent (G) := by
  rintro ⟨node, hnode⟩ parentAtom hatom hreal atom
  cases node with
  | bondDuplicate _ _ _ => simp [PathNode.label, ProvenanceRealAtom] at hreal
  | ringDuplicate _ _ => simp [PathNode.label, ProvenanceRealAtom] at hreal
  | real path =>
      obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil
        (chainToLigand_ne_nil molecule ligand hnode.1)
      simp only [pathExpansion_label, PathNode.label, List.head?_cons, Option.some.injEq] at hatom
      subst hatom
      have hbranch := branch_real_iff (hbond := hbond) hnode atom
      have hsupp := suppressed_real_iff (hbond := hbond) hnode atom
      simp only [List.tail_cons] at hbranch hsupp
      haveI : Finite {index : ℕ // index + 1 < molecule.bond first atom} :=
        finite_index_subtype _
      have hspec := childOfAtom_spec (hbond := hbond) hnode atom
      have hinj := childOfAtom_injective (hbond := hbond) hnode atom
      have hsurj := childOfAtom_surjective (hbond := hbond) hnode atom
      have hreal' := realChild_valid_iff hnode atom
      have hring' := ringAllowed_iff (molecule := molecule) (externalParent := externalParent)
        (current := first) (rest := rest) atom
      have hsb : ((rest = [] ∧ atom = externalParent) ∨ rest.head? = some atom) →
          (atom = externalParent ∨ atom ∈ rest) := by
        rintro (⟨_, h⟩ | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_of_head? h)
      have hsa : ((rest = [] ∧ atom = externalParent) ∨ rest.head? = some atom) →
          molecule.Adj first atom := by
        rintro (⟨rfl, hext⟩ | h)
        · have := ((simplePath_singleton_iff molecule externalParent ligand).1 hnode).1
          subst this
          rw [hext]
          exact (molecule.adj_symm).1 hbond
        · cases rest with
          | nil => simp at h
          | cons next after =>
              simp only [List.head?_cons, Option.some.injEq] at h
              subst h
              exact hnode.1.1
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold ChildAtomCount ChildCountWhere
        refine Eq.trans (card_subtype_eq_of_bijection _ hspec hinj hsurj) ?_
        rw [Nat.card_sum, Nat.card_sum, card_unit_subtype, card_index_subtype, card_unit_subtype]
        simp only [hsupp]
        rw [if_congr hreal' rfl rfl, if_congr hring' rfl rfl]
        exact multiplicity_arithmetic _ _ _ _ Iff.rfl hsb hsa
      · unfold ChildAtomProvenanceCount ChildCountWhere
        refine Eq.trans (card_subtype_eq_of_bijection
          (fun index => childOfAtom (hbond := hbond) hnode atom (.inl (.inr index))) ?_ ?_ ?_) ?_
        · intro index
          exact ⟨(hspec _).1, (hspec _).2,
            by simp [childOfAtom, PathNode.label, ProvenanceMultipleBondDuplicate]⟩
        · intro i j h
          simpa using hinj h
        · rintro y ⟨hedge, hatom, hkind⟩
          obtain ⟨x, rfl⟩ := hsurj y ⟨hedge, hatom⟩
          rcases x with ((_ | index) | _)
          · simp [childOfAtom, PathNode.label, ProvenanceMultipleBondDuplicate] at hkind
          · exact ⟨index, rfl⟩
          · simp [childOfAtom, PathNode.label, ProvenanceMultipleBondDuplicate] at hkind
        · exact card_index_subtype _
      · unfold ChildAtomProvenanceCount ChildCountWhere
        refine Eq.trans (card_subtype_eq_of_bijection
          (fun unit => childOfAtom (hbond := hbond) hnode atom (.inr unit)) ?_ ?_ ?_) ?_
        · intro unit
          exact ⟨(hspec _).1, (hspec _).2,
            by simp [childOfAtom, PathNode.label, ProvenanceRingDuplicate]⟩
        · intro i j _
          exact Subsingleton.elim _ _
        · rintro y ⟨hedge, hatom, hkind⟩
          obtain ⟨x, rfl⟩ := hsurj y ⟨hedge, hatom⟩
          rcases x with ((_ | _) | unit)
          · simp [childOfAtom, PathNode.label, ProvenanceRingDuplicate] at hkind
          · simp [childOfAtom, PathNode.label, ProvenanceRingDuplicate] at hkind
          · exact ⟨unit, rfl⟩
        · rw [card_unit_subtype]
          simp only [hbranch, hsupp]
          exact if_congr hring' rfl rfl
      · unfold ChildAtomProvenanceCount ChildCountWhere
        refine Eq.trans (card_subtype_eq_of_bijection
          (fun unit => childOfAtom (hbond := hbond) hnode atom (.inl (.inl unit))) ?_ ?_ ?_) ?_
        · intro unit
          exact ⟨(hspec _).1, (hspec _).2,
            by simp [childOfAtom, PathNode.label, ProvenanceRealAtom]⟩
        · intro i j _
          exact Subsingleton.elim _ _
        · rintro y ⟨hedge, hatom, hkind⟩
          obtain ⟨x, rfl⟩ := hsurj y ⟨hedge, hatom⟩
          rcases x with ((unit | _) | _)
          · exact ⟨unit, rfl⟩
          · simp [childOfAtom, PathNode.label, ProvenanceRealAtom] at hkind
          · simp [childOfAtom, PathNode.label, ProvenanceRealAtom] at hkind
        · rw [card_unit_subtype]
          simp only [hbranch]
          exact if_congr hreal' rfl rfl

theorem pathExpansion_duplicateDistances (addressing : (G).Addressing) :
    DuplicateDistancesCorrect (G) externalParent addressing := by
  rintro ⟨parentNode, hparent⟩ ⟨childNode, hchild⟩ hedge
  cases parentNode with
  | bondDuplicate _ _ _ => cases childNode <;> exact hedge.elim
  | ringDuplicate _ _ => cases childNode <;> exact hedge.elim
  | real path =>
      have hne := chainToLigand_ne_nil molecule ligand hparent.1
      have hdepth : (addressing.address ⟨.real path, hparent⟩).length + 1 = path.length := by
        rw [addressing.address_length_eq_depth]
        simp only [pathExpansion_depth, PathNode.depth]
        have := List.length_pos_iff.2 hne
        omega
      cases childNode with
      | real _ => simp [PathNode.label]
      | bondDuplicate childPath atom index =>
          change childPath = path at hedge
          subst hedge
          simp only [pathExpansion_label, PathNode.label]
          exact hdepth.symm
      | ringDuplicate childPath atom =>
          change childPath = path at hedge
          subst hedge
          simp only [pathExpansion_label, PathNode.label]
          by_cases hext : atom = externalParent
          · exact Or.inl ⟨hext, by simp [hext]⟩
          · right
            obtain ⟨_, current, hcurrent, _, hhistory, _⟩ := hchild
            have hmem : atom ∈ childPath.tail := hhistory.resolve_left hext
            obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
            obtain ⟨before, after, hsplit⟩ := List.append_of_mem hmem
            simp only [List.tail_cons] at hsplit
            subst hsplit
            have hfull : first :: (before ++ atom :: after) =
                (first :: before) ++ (atom :: after) := rfl
            have hsuffix := simplePath_suffix (first :: before) (atom :: after) (by simp) hparent
            refine ⟨⟨.real (atom :: after), hsuffix⟩,
              transGen_of_suffix (hbond := hbond) (first :: before) (atom :: after) (by simp)
                (by simp) hsuffix hparent, rfl, ?_⟩
            have hnotin : atom ∉ first :: before := by
              have hnodup := hparent.2.1
              rw [hfull, List.nodup_append] at hnodup
              exact fun h => hnodup.2.2 atom h atom (by simp) rfl
            rw [if_neg hext, hfull, List.idxOf_append_of_notMem hnotin, List.idxOf_cons_self,
              addressing.address_length_eq_depth]
            simp only [pathExpansion_depth, PathNode.depth, List.length_append, List.length_cons]
            omega

theorem pathExpansion_locallyAdmissible :
    LocallyAdmissibleExpansion molecule ligand (G) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rintro ⟨node, hnode⟩
    cases node with
    | real path =>
        obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil
          (chainToLigand_ne_nil molecule ligand hnode.1)
        exact ⟨first, rfl⟩
    | bondDuplicate _ atom _ => exact ⟨atom, rfl⟩
    | ringDuplicate _ atom => exact ⟨atom, rfl⟩
  · rintro ⟨node, hnode⟩ hterminal ⟨child, _⟩ hedge
    cases node with
    | real _ => simp [PathNode.label, ProvenanceTerminal] at hterminal
    | bondDuplicate _ _ _ => cases child <;> exact hedge
    | ringDuplicate _ _ => cases child <;> exact hedge
  · rintro ⟨parentNode, hparent⟩ ⟨childNode, hchild⟩ parentAtom childAtom hedge hpa hca
    cases parentNode with
    | bondDuplicate _ _ _ => cases childNode <;> exact hedge.elim
    | ringDuplicate _ _ => cases childNode <;> exact hedge.elim
    | real path =>
        obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil
          (chainToLigand_ne_nil molecule ligand hparent.1)
        simp only [pathExpansion_label, PathNode.label, List.head?_cons, Option.some.injEq] at hpa
        subst hpa
        cases childNode with
        | real childPath =>
            obtain ⟨atom, rfl⟩ := hedge
            simp only [pathExpansion_label, PathNode.label, List.head?_cons,
              Option.some.injEq] at hca
            subst hca
            exact (molecule.adj_symm).1 hchild.1.1
        | bondDuplicate childPath atom index =>
            change childPath = first :: rest at hedge
            subst hedge
            simp only [pathExpansion_label, PathNode.label, Option.some.injEq] at hca
            subst hca
            obtain ⟨_, current, hcurrent, hindex⟩ := hchild
            simp only [List.head?_cons, Option.some.injEq] at hcurrent
            subst hcurrent
            exact lt_of_le_of_lt (Nat.zero_le _) hindex
        | ringDuplicate childPath atom =>
            change childPath = first :: rest at hedge
            subst hedge
            simp only [pathExpansion_label, PathNode.label, Option.some.injEq] at hca
            subst hca
            obtain ⟨_, current, hcurrent, hadj, _⟩ := hchild
            simp only [List.head?_cons, Option.some.injEq] at hcurrent
            subst hcurrent
            exact hadj

theorem pathExpansion_atomBearing : AtomBearingChildren (G) := by
  rintro ⟨parentNode, hparent⟩ ⟨childNode, hchild⟩ hedge
  cases parentNode with
  | bondDuplicate _ _ _ => cases childNode <;> exact hedge.elim
  | ringDuplicate _ _ => cases childNode <;> exact hedge.elim
  | real path =>
      cases childNode with
      | real childPath =>
          obtain ⟨atom, rfl⟩ := hedge
          exact ⟨atom, rfl⟩
      | bondDuplicate _ atom _ => exact ⟨atom, rfl⟩
      | ringDuplicate _ atom => exact ⟨atom, rfl⟩

/-- **The path expansion is a faithful exact expansion.** -/
theorem pathExpansion_faithful :
    FaithfulExactExpansion molecule externalParent ligand (G) := by
  obtain ⟨addressing⟩ := RootedDigraph.exists_addressing_of_unique_parent (G)
    (pathExpansion_unique_parent hbond)
  exact ⟨⟨pathExpansion_locallyAdmissible, addressing, pathExpansion_multiplicities⟩, hbond,
    pathExpansion_atomBearing, pathExpansion_duplicateDistances⟩

end Faithful

/-- Every ligand bonded to a stereocenter has a faithful exact expansion. -/
theorem exists_faithfulExactExpansion {externalParent ligand : Atom}
    (hbond : molecule.Adj externalParent ligand) :
    ∃ graph : RootedDigraph Atom, FaithfulExactExpansion molecule externalParent ligand graph :=
  ⟨pathExpansion molecule externalParent ligand hbond, pathExpansion_faithful⟩

end PathModel

/-! ## Universal declarative constitutional outcomes -/

namespace ConstitutionalProblemData

variable {Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Constitutional problem data whose admissible expansions are exactly the faithful exact
expansions of each unit's ligands.  Every other field is retained. -/
def withFaithfulExpansions (data : ConstitutionalProblemData Atom Unit) :
    ConstitutionalProblemData Atom Unit :=
  { data with
    admissibleExpansion := fun unit ligand graph =>
      RootedDigraph.FaithfulExactExpansion data.molecule (data.centerAtom unit) (data.ligandAtom unit ligand)
        graph
    expansion_sound := fun _ _ _ h => h.1 }

/-- **Universal totality of declarative Rules 1a, 1b, and 2.**  For any molecule and any
stereounits whose ligands are bonded to their centers, with faithful exact expansions and the
canonical addressing family, every descriptor map, unit, pair of ligands and constitutional rule
has exactly one `Problem.RuleOutcome`.  No expansion, addressing, runtime result or family
parameter is assumed. -/
theorem withFaithfulExpansions_ruleOutcome_existsUnique
    (data : ConstitutionalProblemData Atom Unit)
    (hbonded : ∀ unit ligand, data.molecule.Adj (data.centerAtom unit) (data.ligandAtom unit ligand))
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    (leftLigand rightLigand : Fin 4) :
    ∃! outcome, data.withFaithfulExpansions.withCanonicalAddressing.toProblem.RuleOutcome
      descriptorMap rule.toSequenceRule unit leftLigand rightLigand outcome :=
  data.withFaithfulExpansions.withCanonicalAddressing_ruleOutcome_existsUnique
    (by intro unit ligand graph h; exact h)
    (fun unit ligand => exists_faithfulExactExpansion (hbonded unit ligand))
    descriptorMap unit rule leftLigand rightLigand

end ConstitutionalProblemData

end
end DeclarativeCIP
end OneCenter
end TetraStereo
