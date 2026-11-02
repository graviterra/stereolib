import TetraStereo.OneCenter.DeclarativeCIP

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

/-!
# Concrete declarative semantics for Rules 1a, 1b, and 2

This module instantiates the constitutional part of the independent specification.  It remains
independent of every production comparison, sorting, expansion, and refusal function.

The important object is an `Addressing` of a rooted digraph.  Addresses retain parentage: a child
address is its parent's address followed by one semantic sibling slot.  Which addressings are
admissible is a proposition supplied by the revised-CIP hierarchy semantics.  A rule judgment must
hold for *every* admissible addressing, making traversal or container enumeration irrelevant.

Rules 1a, 1b, and 2 compare their node observations at the first differing address.  The definition
is relational and quantifies over the first-difference witness; it does not execute a traversal.
-/

universe u

namespace RootedDigraph

variable {Atom : Type u}

/-- Duplicate and explicit placeholder nodes are terminal in a finite CIP expansion. -/
def ProvenanceTerminal : NodeProvenance → Prop
  | NodeProvenance.realAtom => False
  | _ => True

/-- Atom-carrying provenance has an atom; explicit placeholder provenance does not. -/
def LabelCompatible (label : NodeLabel Atom) : Prop :=
  match label.provenance with
  | NodeProvenance.realAtom => ∃ atom, label.atom? = some atom
  | NodeProvenance.multipleBondDuplicate _ => ∃ atom, label.atom? = some atom
  | NodeProvenance.ringDuplicate _ => ∃ atom, label.atom? = some atom
  | NodeProvenance.phantom _ => label.atom? = none
  | NodeProvenance.lonePair _ => label.atom? = none
  | NodeProvenance.auxiliary _ => label.atom? = none

/-- Local, representation-independent admissibility conditions for a ligand expansion.

This predicate fixes the root label, enforces atom/provenance compatibility, makes duplicates and
placeholders leaves, and requires every atom-to-atom hierarchy edge to follow a molecular bond.
The later full expansion theorem must additionally prove the exact child multiplicities prescribed
by bond duplication and ring closure. -/
def LocallyAdmissibleExpansion [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (ligand : Atom) (graph : RootedDigraph Atom) : Prop :=
  graph.label graph.root = ⟨some ligand, NodeProvenance.realAtom⟩ ∧
    (∀ node, LabelCompatible (graph.label node)) ∧
    (∀ node, ProvenanceTerminal (graph.label node).provenance →
      ∀ child, ¬ graph.child node child) ∧
    (∀ parent node parentAtom nodeAtom,
      graph.child parent node →
        (graph.label parent).atom? = some parentAtom →
          (graph.label node).atom? = some nodeAtom →
            molecule.Adj parentAtom nodeAtom)

/-- Transport local expansion admissibility across a rooted-digraph representation isomorphism. -/
theorem locallyAdmissibleExpansion_iso [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (ligand : Atom)
    {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right) :
    LocallyAdmissibleExpansion molecule ligand left →
      LocallyAdmissibleExpansion molecule ligand right := by
    rintro ⟨hroot, hcompatible, hterminal, hadj⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hmap := iso.map_label left.root
      rw [iso.map_root] at hmap
      exact hmap.symm.trans hroot
    · intro node
      have hmap : left.label (iso.toEquiv.symm node) = right.label node := by
        simpa using iso.map_label (iso.toEquiv.symm node)
      rw [← hmap]
      exact hcompatible (iso.toEquiv.symm node)
    · intro node hterm child hchild
      have hmapNode : left.label (iso.toEquiv.symm node) = right.label node := by
        simpa using iso.map_label (iso.toEquiv.symm node)
      have htermLeft : ProvenanceTerminal (left.label (iso.toEquiv.symm node)).provenance := by
        simpa [hmapNode] using hterm
      have hchildLeft : left.child (iso.toEquiv.symm node) (iso.toEquiv.symm child) := by
        apply (iso.map_child (iso.toEquiv.symm node) (iso.toEquiv.symm child)).2
        simpa using hchild
      exact hterminal (iso.toEquiv.symm node) htermLeft (iso.toEquiv.symm child) hchildLeft
    · intro parent node parentAtom nodeAtom hedge hparent hnode
      have hedgeLeft : left.child (iso.toEquiv.symm parent) (iso.toEquiv.symm node) := by
        apply (iso.map_child (iso.toEquiv.symm parent) (iso.toEquiv.symm node)).2
        simpa using hedge
      have hparentMap :
          left.label (iso.toEquiv.symm parent) = right.label parent := by
        simpa using iso.map_label (iso.toEquiv.symm parent)
      have hnodeMap : left.label (iso.toEquiv.symm node) = right.label node := by
        simpa using iso.map_label (iso.toEquiv.symm node)
      exact hadj (iso.toEquiv.symm parent) (iso.toEquiv.symm node) parentAtom nodeAtom
        hedgeLeft (by simpa [hparentMap] using hparent) (by simpa [hnodeMap] using hnode)

/-- Local expansion admissibility is invariant under every rooted-digraph representation
isomorphism. -/
theorem locallyAdmissibleExpansion_iso_iff [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (ligand : Atom)
    {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right) :
    LocallyAdmissibleExpansion molecule ligand left ↔
      LocallyAdmissibleExpansion molecule ligand right :=
  ⟨locallyAdmissibleExpansion_iso molecule ligand iso,
    locallyAdmissibleExpansion_iso molecule ligand iso.symm⟩

/-- Transport a strict ancestry derivation across a rooted-digraph representation isomorphism. -/
theorem Iso.map_transGen {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (first second : left.Node) :
    Relation.TransGen left.child first second →
      Relation.TransGen right.child (iso.toEquiv first) (iso.toEquiv second) := by
    intro h
    induction h with
    | single hedge => exact .single ((iso.map_child _ _).1 hedge)
    | tail _ hedge ih => exact ih.tail ((iso.map_child _ _).1 hedge)

/-- Strict ancestry is preserved by a rooted-digraph representation isomorphism. -/
theorem Iso.transGen_iff {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (first second : left.Node) :
    Relation.TransGen left.child first second ↔
      Relation.TransGen right.child (iso.toEquiv first) (iso.toEquiv second) :=
  ⟨iso.map_transGen first second,
    fun h => by
      simpa [RootedDigraph.Iso.symm] using
        iso.symm.map_transGen (iso.toEquiv first) (iso.toEquiv second) h⟩

/-- A parent-preserving semantic address for every node of a rooted digraph. -/
structure Addressing (graph : RootedDigraph Atom) where
  address : graph.Node → List ℕ
  address_injective : Function.Injective address
  root_address : address graph.root = []
  child_iff : ∀ parent node,
    graph.child parent node ↔ ∃ slot, address node = address parent ++ [slot]

namespace Addressing

variable {left right third : RootedDigraph Atom}

@[ext] theorem ext {first second : Addressing left}
    (h : first.address = second.address) : first = second := by
  cases first
  cases second
  simp_all

/-- Transport semantic node addresses across a rooted-digraph isomorphism. -/
def transport (addressing : Addressing left) (iso : RootedDigraph.Iso left right) :
    Addressing right where
  address := fun node => addressing.address (iso.toEquiv.symm node)
  address_injective := by
    intro a b h
    exact iso.toEquiv.symm.injective (addressing.address_injective h)
  root_address := by
    have hroot : iso.toEquiv.symm right.root = left.root := by
      apply iso.toEquiv.injective
      simp [iso.map_root]
    simp [hroot, addressing.root_address]
  child_iff := by
    intro parent node
    calc
      right.child parent node ↔
          left.child (iso.toEquiv.symm parent) (iso.toEquiv.symm node) := by
            simpa using
              (iso.map_child (iso.toEquiv.symm parent) (iso.toEquiv.symm node)).symm
      _ ↔ ∃ slot,
          addressing.address (iso.toEquiv.symm node) =
            addressing.address (iso.toEquiv.symm parent) ++ [slot] :=
        addressing.child_iff _ _

@[simp] theorem transport_address (addressing : Addressing left)
    (iso : RootedDigraph.Iso left right) (node : right.Node) :
    (addressing.transport iso).address node = addressing.address (iso.toEquiv.symm node) :=
  rfl

@[simp] theorem transport_refl (addressing : Addressing left) :
    addressing.transport (RootedDigraph.Iso.refl left) = addressing := by
  apply Addressing.ext
  funext node
  rfl

@[simp] theorem transport_symm_transport (addressing : Addressing left)
    (iso : RootedDigraph.Iso left right) :
    (addressing.transport iso).transport iso.symm = addressing := by
  apply Addressing.ext
  funext node
  simp [transport, RootedDigraph.Iso.symm]

@[simp] theorem transport_transport_symm (addressing : Addressing right)
    (iso : RootedDigraph.Iso left right) :
    (addressing.transport iso.symm).transport iso = addressing := by
  apply Addressing.ext
  funext node
  simp [transport, RootedDigraph.Iso.symm]

/-- A parent-preserving addressing rules out incoming edges to the root. -/
theorem not_child_root (addressing : Addressing left) (parent : left.Node) :
    ¬ left.child parent left.root := by
  intro hedge
  rcases (addressing.child_iff parent left.root).1 hedge with ⟨slot, hslot⟩
  have hlength := congrArg List.length hslot
  simp [addressing.root_address] at hlength

/-- A node has at most one parent in an addressed hierarchy. -/
theorem parent_unique (addressing : Addressing left) {first second node : left.Node}
    (hfirst : left.child first node) (hsecond : left.child second node) :
    first = second := by
  rcases (addressing.child_iff first node).1 hfirst with ⟨firstSlot, hfirstAddress⟩
  rcases (addressing.child_iff second node).1 hsecond with ⟨secondSlot, hsecondAddress⟩
  apply addressing.address_injective
  have hdrop := congrArg List.dropLast (hfirstAddress.symm.trans hsecondAddress)
  simpa using hdrop

/-- Every non-root node has exactly one parent; thus an addressed rooted digraph is tree-shaped,
even though its representation was introduced as a digraph. -/
theorem existsUnique_parent (addressing : Addressing left) (node : left.Node)
    (hne : node ≠ left.root) :
    ∃! parent, left.child parent node := by
  rcases (left.reachable node).cases_tail with hroot | ⟨parent, _, hedge⟩
  · exact (hne hroot).elim
  · refine ⟨parent, hedge, ?_⟩
    intro other hother
    exact addressing.parent_unique hother hedge

/-- Parent-preserving addressings may rename sibling slots, but they assign every node the same
path length. -/
theorem address_length_eq (first second : left.Addressing) (node : left.Node) :
    (first.address node).length = (second.address node).length := by
  have hreachable := left.reachable node
  induction hreachable with
  | refl => simp [first.root_address, second.root_address]
  | @tail parent node hpath hedge inductionHypothesis =>
      rcases (first.child_iff parent node).1 hedge with ⟨firstSlot, hfirst⟩
      rcases (second.child_iff parent node).1 hedge with ⟨secondSlot, hsecond⟩
      rw [hfirst, hsecond]
      simp [inductionHypothesis]

end Addressing

variable {left right third : RootedDigraph Atom}

/-! ### Exact molecular child accounting -/

/-- An atom labels the immediate parent of a hierarchy node. -/
def ParentAtom (graph : RootedDigraph Atom) (node : graph.Node) (atom : Atom) : Prop :=
  ∃ parent, graph.child parent node ∧ (graph.label parent).atom? = some atom

/-- An atom occurs at a strict ancestor of a hierarchy node. -/
def AncestorAtom (graph : RootedDigraph Atom) (node : graph.Node) (atom : Atom) : Prop :=
  ∃ ancestor, Relation.TransGen graph.child ancestor node ∧
    (graph.label ancestor).atom? = some atom

/-- The external stereocenter and all represented strict ancestors form the branch history used to
classify ring-closure duplicates. -/
def BranchAncestorAtom (graph : RootedDigraph Atom) (externalParent atom : Atom)
    (node : graph.Node) : Prop :=
  atom = externalParent ∨ AncestorAtom graph node atom

/-- The zero-index occurrence of the external parent at the root, or of an immediate represented
parent below the root, is suppressed from the child expansion. -/
def SuppressedParentAtom (graph : RootedDigraph Atom) (externalParent atom : Atom)
    (node : graph.Node) : Prop :=
  (node = graph.root ∧ atom = externalParent) ∨ ParentAtom graph node atom

def ProvenanceMultipleBondDuplicate : NodeProvenance → Prop
  | NodeProvenance.multipleBondDuplicate _ => True
  | _ => False

def ProvenanceRingDuplicate : NodeProvenance → Prop
  | NodeProvenance.ringDuplicate _ => True
  | _ => False

def ProvenanceRealAtom : NodeProvenance → Prop
  | NodeProvenance.realAtom => True
  | _ => False

/-- Cardinality of children satisfying a semantic predicate. -/
noncomputable def ChildCountWhere (graph : RootedDigraph Atom) (parent : graph.Node)
    (predicate : graph.Node → Prop) : ℕ :=
  Nat.card {node : graph.Node // graph.child parent node ∧ predicate node}

/-- Number of children representing a specified molecular atom. -/
noncomputable def ChildAtomCount (graph : RootedDigraph Atom) (parent : graph.Node)
    (atom : Atom) : ℕ :=
  ChildCountWhere graph parent fun node => (graph.label node).atom? = some atom

/-- Number of children representing a specified atom with provenance satisfying `kind`. -/
noncomputable def ChildAtomProvenanceCount (graph : RootedDigraph Atom)
    (parent : graph.Node) (atom : Atom) (kind : NodeProvenance → Prop) : ℕ :=
  ChildCountWhere graph parent fun node =>
    (graph.label node).atom? = some atom ∧ kind (graph.label node).provenance

/-- Child cardinalities are preserved by representation isomorphism whenever the counted predicate
is transported pointwise. -/
theorem childCountWhere_iso (iso : RootedDigraph.Iso left right) (parent : left.Node)
    (leftPredicate : left.Node → Prop) (rightPredicate : right.Node → Prop)
    (predicate_iff : ∀ node, leftPredicate node ↔ rightPredicate (iso.toEquiv node)) :
    ChildCountWhere left parent leftPredicate =
      ChildCountWhere right (iso.toEquiv parent) rightPredicate := by
  apply Nat.card_congr
  exact iso.toEquiv.subtypeEquiv fun node => by
    exact and_congr (iso.map_child parent node) (predicate_iff node)

@[simp] theorem parentAtom_iso_iff (iso : RootedDigraph.Iso left right)
    (node : left.Node) (atom : Atom) :
    ParentAtom left node atom ↔ ParentAtom right (iso.toEquiv node) atom := by
  constructor
  · rintro ⟨parent, hedge, hlabel⟩
    exact ⟨iso.toEquiv parent, (iso.map_child _ _).1 hedge, by
      simpa [← iso.map_label parent] using hlabel⟩
  · rintro ⟨parent, hedge, hlabel⟩
    refine ⟨iso.toEquiv.symm parent, ?_, ?_⟩
    · apply (iso.map_child (iso.toEquiv.symm parent) node).2
      simpa using hedge
    · have hmap : left.label (iso.toEquiv.symm parent) = right.label parent := by
        simpa using iso.map_label (iso.toEquiv.symm parent)
      simpa [hmap] using hlabel

@[simp] theorem ancestorAtom_iso_iff (iso : RootedDigraph.Iso left right)
    (node : left.Node) (atom : Atom) :
    AncestorAtom left node atom ↔ AncestorAtom right (iso.toEquiv node) atom := by
  constructor
  · rintro ⟨ancestor, hancestor, hlabel⟩
    exact ⟨iso.toEquiv ancestor, (iso.transGen_iff ancestor node).1 hancestor, by
      simpa [← iso.map_label ancestor] using hlabel⟩
  · rintro ⟨ancestor, hancestor, hlabel⟩
    refine ⟨iso.toEquiv.symm ancestor, ?_, ?_⟩
    · have hback :=
        (iso.transGen_iff (iso.toEquiv.symm ancestor) node).2 (by simpa using hancestor)
      exact hback
    · have hmap : left.label (iso.toEquiv.symm ancestor) = right.label ancestor := by
        simpa using iso.map_label (iso.toEquiv.symm ancestor)
      simpa [hmap] using hlabel

theorem childAtomCount_iso (iso : RootedDigraph.Iso left right)
    (parent : left.Node) (atom : Atom) :
    ChildAtomCount left parent atom = ChildAtomCount right (iso.toEquiv parent) atom := by
  apply childCountWhere_iso iso parent
  intro node
  simp [iso.map_label node]

theorem childAtomProvenanceCount_iso (iso : RootedDigraph.Iso left right)
    (parent : left.Node) (atom : Atom) (kind : NodeProvenance → Prop) :
    ChildAtomProvenanceCount left parent atom kind =
      ChildAtomProvenanceCount right (iso.toEquiv parent) atom kind := by
  apply childCountWhere_iso iso parent
  intro node
  simp [iso.map_label node]

@[simp] theorem branchAncestorAtom_iso_iff (iso : RootedDigraph.Iso left right)
    (externalParent atom : Atom) (node : left.Node) :
    BranchAncestorAtom left externalParent atom node ↔
      BranchAncestorAtom right externalParent atom (iso.toEquiv node) := by
  unfold BranchAncestorAtom
  rw [ancestorAtom_iso_iff iso node atom]

@[simp] theorem suppressedParentAtom_iso_iff (iso : RootedDigraph.Iso left right)
    (externalParent atom : Atom) (node : left.Node) :
    SuppressedParentAtom left externalParent atom node ↔
      SuppressedParentAtom right externalParent atom (iso.toEquiv node) := by
  have hroot : node = left.root ↔ iso.toEquiv node = right.root := by
    constructor
    · intro h
      simpa [h] using iso.map_root
    · intro h
      apply iso.toEquiv.injective
      simpa [iso.map_root] using h
  unfold SuppressedParentAtom
  rw [hroot, parentAtom_iso_iff iso node atom]

/-- Exact atom-child multiplicities prescribed by the finite hierarchical expansion.

For every expandable real node and every molecular atom:

* the zero-index immediate-parent occurrence is suppressed;
* the remaining `bondOrder - 1` occurrences are multiple-bond duplicates;
* a non-parent ancestor contributes one ring duplicate;
* a bonded atom absent from branch history contributes one real child.
-/
noncomputable def AtomChildMultiplicities [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent : Atom)
    (graph : RootedDigraph Atom) : Prop := by
  classical
  exact
    ∀ parent parentAtom,
      (graph.label parent).atom? = some parentAtom →
        ProvenanceRealAtom (graph.label parent).provenance →
          ∀ atom,
            ChildAtomCount graph parent atom =
                molecule.bond parentAtom atom -
                  (if SuppressedParentAtom graph externalParent atom parent then 1 else 0) ∧
              ChildAtomProvenanceCount graph parent atom ProvenanceMultipleBondDuplicate =
                molecule.bond parentAtom atom - 1 ∧
              ChildAtomProvenanceCount graph parent atom ProvenanceRingDuplicate =
                (if molecule.Adj parentAtom atom ∧
                    BranchAncestorAtom graph externalParent atom parent ∧
                    ¬ SuppressedParentAtom graph externalParent atom parent then 1 else 0) ∧
              ChildAtomProvenanceCount graph parent atom ProvenanceRealAtom =
                (if molecule.Adj parentAtom atom ∧
                    ¬ BranchAncestorAtom graph externalParent atom parent then 1 else 0)

/-- Exact atom-child multiplicities are representation-invariant. -/
theorem atomChildMultiplicities_iso [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent : Atom)
    {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right) :
    AtomChildMultiplicities molecule externalParent left →
      AtomChildMultiplicities molecule externalParent right := by
  classical
  intro h parent parentAtom hparentAtom hparentReal atom
  let parentLeft := iso.toEquiv.symm parent
  have hmap : left.label parentLeft = right.label parent := by
    simpa [parentLeft] using iso.map_label parentLeft
  have hparentAtomLeft : (left.label parentLeft).atom? = some parentAtom := by
    simpa [hmap] using hparentAtom
  have hparentRealLeft : ProvenanceRealAtom (left.label parentLeft).provenance := by
    simpa [hmap] using hparentReal
  rcases h parentLeft parentAtom hparentAtomLeft hparentRealLeft atom with
    ⟨htotal, hmultiple, hring, hreal⟩
  have hparentImage : iso.toEquiv parentLeft = parent := by
    simp [parentLeft]
  have hsuppressed :
      SuppressedParentAtom left externalParent atom parentLeft ↔
        SuppressedParentAtom right externalParent atom (iso.toEquiv parentLeft) :=
    suppressedParentAtom_iso_iff iso externalParent atom parentLeft
  have hancestor :
      BranchAncestorAtom left externalParent atom parentLeft ↔
        BranchAncestorAtom right externalParent atom (iso.toEquiv parentLeft) :=
    branchAncestorAtom_iso_iff iso externalParent atom parentLeft
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      ChildAtomCount right parent atom = ChildAtomCount left parentLeft atom := by
        simpa [hparentImage] using (childAtomCount_iso iso parentLeft atom).symm
      _ = molecule.bond parentAtom atom -
          (if SuppressedParentAtom left externalParent atom parentLeft then 1 else 0) := htotal
      _ = molecule.bond parentAtom atom -
          (if SuppressedParentAtom right externalParent atom parent then 1 else 0) := by
            rw [← hparentImage, hsuppressed]
  · calc
      ChildAtomProvenanceCount right parent atom ProvenanceMultipleBondDuplicate =
          ChildAtomProvenanceCount left parentLeft atom ProvenanceMultipleBondDuplicate := by
            simpa [hparentImage] using
              (childAtomProvenanceCount_iso iso parentLeft atom
                ProvenanceMultipleBondDuplicate).symm
      _ = molecule.bond parentAtom atom - 1 := hmultiple
  · calc
      ChildAtomProvenanceCount right parent atom ProvenanceRingDuplicate =
          ChildAtomProvenanceCount left parentLeft atom ProvenanceRingDuplicate := by
            simpa [hparentImage] using
              (childAtomProvenanceCount_iso iso parentLeft atom ProvenanceRingDuplicate).symm
      _ = (if molecule.Adj parentAtom atom ∧
          BranchAncestorAtom left externalParent atom parentLeft ∧
          ¬ SuppressedParentAtom left externalParent atom parentLeft then 1 else 0) := hring
      _ = (if molecule.Adj parentAtom atom ∧
          BranchAncestorAtom right externalParent atom parent ∧
          ¬ SuppressedParentAtom right externalParent atom parent then 1 else 0) := by
            rw [← hparentImage, hancestor, hsuppressed]
  · calc
      ChildAtomProvenanceCount right parent atom ProvenanceRealAtom =
          ChildAtomProvenanceCount left parentLeft atom ProvenanceRealAtom := by
            simpa [hparentImage] using
              (childAtomProvenanceCount_iso iso parentLeft atom ProvenanceRealAtom).symm
      _ = (if molecule.Adj parentAtom atom ∧
          ¬ BranchAncestorAtom left externalParent atom parentLeft then 1 else 0) := hreal
      _ = (if molecule.Adj parentAtom atom ∧
          ¬ BranchAncestorAtom right externalParent atom parent then 1 else 0) := by
            rw [← hparentImage, hancestor]

/-- Full constitutional expansion predicate: local chemical compatibility, a tree-shaped semantic
addressing, and exact child multiplicities. -/
def ExactExpansion [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom) : Prop :=
  LocallyAdmissibleExpansion molecule ligand graph ∧
    (∃ _addressing : graph.Addressing,
      AtomChildMultiplicities molecule externalParent graph)

/-- Every represented child in an exact molecular expansion bears an atom.  This excludes
unaccounted phantom, lone-pair, or auxiliary children that atom-indexed multiplicity equations
cannot see. -/
def AtomBearingChildren (graph : RootedDigraph Atom) : Prop :=
  ∀ parent child, graph.child parent child → ∃ atom, (graph.label child).atom? = some atom

/-- Duplicate provenance distances agree with the semantic addressing.

Multiple-bond duplicates carry the sphere of the atom to which they are attached.  Ring
duplicates carry the sphere of the strict ancestor atom they duplicate.  Spheres are counted from
the external stereocenter, so a represented address of length `n` lies in sphere `n + 1`. -/
def DuplicateDistancesCorrect (graph : RootedDigraph Atom) (externalParent : Atom)
    (addressing : graph.Addressing) : Prop :=
  ∀ parent child, graph.child parent child →
    match graph.label child with
    | ⟨_, NodeProvenance.multipleBondDuplicate distance⟩ =>
        distance = (addressing.address parent).length + 1
    | ⟨some atom, NodeProvenance.ringDuplicate distance⟩ =>
        (atom = externalParent ∧ distance = 0) ∨
          ∃ ancestor, Relation.TransGen graph.child ancestor parent ∧
            (graph.label ancestor).atom? = some atom ∧
            distance = (addressing.address ancestor).length + 1
    | ⟨none, NodeProvenance.ringDuplicate _⟩ => False
    | _ => True

/-- Duplicate-distance correctness depends only on hierarchy depth, not on the numeric names an
addressing assigns to sibling slots. -/
theorem duplicateDistancesCorrect_addressing_iff (graph : RootedDigraph Atom)
    (externalParent : Atom) (first second : graph.Addressing) :
    DuplicateDistancesCorrect graph externalParent first ↔
      DuplicateDistancesCorrect graph externalParent second := by
  suffices hforward : ∀ (source target : graph.Addressing),
      DuplicateDistancesCorrect graph externalParent source →
        DuplicateDistancesCorrect graph externalParent target by
    exact ⟨hforward first second, hforward second first⟩
  intro source target hcorrect parent child hedge
  have hlocal := hcorrect parent child hedge
  cases hlabel : graph.label child with
  | mk atom? provenance =>
      cases provenance with
      | realAtom | lonePair | phantom | auxiliary => trivial
      | multipleBondDuplicate distance =>
          simp [hlabel] at hlocal ⊢
          exact hlocal.trans (congrArg (fun depth => depth + 1)
            (source.address_length_eq target parent))
      | ringDuplicate distance =>
          cases atom? with
          | none =>
              simp [hlabel] at hlocal
          | some atom =>
              simp [hlabel] at hlocal ⊢
              rcases hlocal with hexternal | hrepresented
              · exact Or.inl hexternal
              · obtain ⟨ancestor, hancestor, hatom, hdistance⟩ := hrepresented
                refine Or.inr ⟨ancestor, hancestor, hatom, ?_⟩
                exact hdistance.trans (congrArg (fun depth => depth + 1)
                  (source.address_length_eq target ancestor))

/-- One correct addressing therefore establishes duplicate-distance correctness for every
parent-preserving addressing of the same rooted hierarchy. -/
theorem duplicateDistancesCorrect_all_of_one (graph : RootedDigraph Atom)
    (externalParent : Atom) (addressing : graph.Addressing)
    (hcorrect : DuplicateDistancesCorrect graph externalParent addressing) :
    ∀ other : graph.Addressing, DuplicateDistancesCorrect graph externalParent other :=
  fun other =>
    (duplicateDistancesCorrect_addressing_iff graph externalParent addressing other).1 hcorrect

/-- Strengthened independent constitutional boundary used for production hierarchy correspondence.

Besides the original local and multiplicity clauses, it requires a genuine root bond, accounts for
every child (including atomless labels), and fixes the Rule-1b distance payloads under every
parent-preserving semantic addressing. -/
def FaithfulExactExpansion [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : RootedDigraph Atom) : Prop :=
  ExactExpansion molecule externalParent ligand graph ∧
    molecule.Adj externalParent ligand ∧
    AtomBearingChildren graph ∧
    ∀ addressing : graph.Addressing,
      DuplicateDistancesCorrect graph externalParent addressing

/-- Exact expansion is invariant under arbitrary finite node-representation changes. -/
theorem exactExpansion_iso_iff [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right) :
    ExactExpansion molecule externalParent ligand left ↔
      ExactExpansion molecule externalParent ligand right := by
  constructor
  · rintro ⟨hlocal, addressing, hmultiplicity⟩
    exact ⟨locallyAdmissibleExpansion_iso molecule ligand iso hlocal,
      addressing.transport iso,
      atomChildMultiplicities_iso molecule externalParent iso hmultiplicity⟩
  · rintro ⟨hlocal, addressing, hmultiplicity⟩
    exact ⟨locallyAdmissibleExpansion_iso molecule ligand iso.symm hlocal,
      addressing.transport iso.symm,
      atomChildMultiplicities_iso molecule externalParent iso.symm hmultiplicity⟩

theorem atomBearingChildren_iso (iso : RootedDigraph.Iso left right) :
    AtomBearingChildren left → AtomBearingChildren right := by
  intro h parent child hedge
  let parentLeft := iso.toEquiv.symm parent
  let childLeft := iso.toEquiv.symm child
  have hedgeLeft : left.child parentLeft childLeft := by
    apply (iso.map_child parentLeft childLeft).2
    simpa [parentLeft, childLeft] using hedge
  obtain ⟨atom, hatom⟩ := h parentLeft childLeft hedgeLeft
  refine ⟨atom, ?_⟩
  have hlabel := iso.map_label childLeft
  simpa [childLeft, hlabel] using hatom

theorem duplicateDistancesCorrect_transport
    (iso : RootedDigraph.Iso left right) (externalParent : Atom)
    (addressing : left.Addressing)
    (hcorrect : DuplicateDistancesCorrect left externalParent addressing) :
    DuplicateDistancesCorrect right externalParent (addressing.transport iso) := by
  intro parent child hedge
  let parentLeft := iso.toEquiv.symm parent
  let childLeft := iso.toEquiv.symm child
  have hedgeLeft : left.child parentLeft childLeft := by
    apply (iso.map_child parentLeft childLeft).2
    simpa [parentLeft, childLeft] using hedge
  have hlocal := hcorrect parentLeft childLeft hedgeLeft
  have hchildLabel : left.label childLeft = right.label child := by
    simpa [childLeft] using iso.map_label childLeft
  rw [← hchildLabel]
  cases hlabel : left.label childLeft with
  | mk atom? provenance =>
      cases provenance with
      | realAtom | lonePair | phantom | auxiliary => trivial
      | multipleBondDuplicate distance =>
          simp [hlabel] at hlocal
          simpa [Addressing.transport_address] using hlocal
      | ringDuplicate distance =>
          cases atom? with
          | none =>
              simp [hlabel] at hlocal
          | some atom =>
              simp [hlabel] at hlocal
              rcases hlocal with hexternal | hrepresented
              · exact Or.inl hexternal
              · obtain ⟨ancestorLeft, hancestor, hatom, hdistance⟩ := hrepresented
                refine Or.inr ⟨iso.toEquiv ancestorLeft, ?_, ?_, ?_⟩
                · simpa [parentLeft] using
                    (iso.transGen_iff ancestorLeft parentLeft).1 hancestor
                · simpa [iso.map_label ancestorLeft] using hatom
                · simpa [Addressing.transport_address] using hdistance

theorem faithfulExactExpansion_iso_iff [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right) :
    FaithfulExactExpansion molecule externalParent ligand left ↔
      FaithfulExactExpansion molecule externalParent ligand right := by
  constructor
  · rintro ⟨hexact, hrootBond, hatomBearing, hdistances⟩
    exact ⟨(exactExpansion_iso_iff molecule externalParent ligand iso).1 hexact,
      hrootBond, atomBearingChildren_iso iso hatomBearing,
      fun addressing => by
        simpa using duplicateDistancesCorrect_transport iso externalParent
          (addressing.transport iso.symm) (hdistances (addressing.transport iso.symm))⟩
  · rintro ⟨hexact, hrootBond, hatomBearing, hdistances⟩
    exact ⟨(exactExpansion_iso_iff molecule externalParent ligand iso).2 hexact,
      hrootBond, atomBearingChildren_iso iso.symm hatomBearing,
      fun addressing => by
        simpa using duplicateDistancesCorrect_transport iso.symm externalParent
          (addressing.transport iso) (hdistances (addressing.transport iso))⟩

namespace Addressing

variable {left right third : RootedDigraph Atom}

/-- A semantic address contains either exactly one node label or no node label. -/
def LabelAt (graph : RootedDigraph Atom) (addressing : Addressing graph)
    (position : List ℕ) (label : Option (NodeLabel Atom)) : Prop :=
  (∃ node, addressing.address node = position ∧ label = some (graph.label node)) ∨
    (label = none ∧ ∀ node, addressing.address node ≠ position)

theorem labelAt_exists (graph : RootedDigraph Atom) (addressing : Addressing graph)
    (position : List ℕ) :
    ∃ label, LabelAt graph addressing position label := by
  classical
  by_cases h : ∃ node, addressing.address node = position
  · rcases h with ⟨node, hnode⟩
    exact ⟨some (graph.label node), Or.inl ⟨node, hnode, rfl⟩⟩
  · exact ⟨none, Or.inr ⟨rfl, by simpa only [not_exists] using h⟩⟩

theorem labelAt_functional (graph : RootedDigraph Atom) (addressing : Addressing graph)
    (position : List ℕ) {first second : Option (NodeLabel Atom)}
    (hfirst : LabelAt graph addressing position first)
    (hsecond : LabelAt graph addressing position second) :
    first = second := by
  rcases hfirst with ⟨node₁, hpos₁, rfl⟩ | ⟨rfl, hempty₁⟩
  · rcases hsecond with ⟨node₂, hpos₂, hlabel₂⟩ | ⟨_, hempty₂⟩
    · have hnode : node₁ = node₂ := addressing.address_injective (hpos₁.trans hpos₂.symm)
      subst node₂
      exact hlabel₂.symm
    · exact (hempty₂ node₁ hpos₁).elim
  · rcases hsecond with ⟨node₂, hpos₂, _⟩ | ⟨hlabel₂, _⟩
    · exact (hempty₁ node₂ hpos₂).elim
    · exact hlabel₂.symm

/-- `LabelAt` is preserved exactly by transport across a rooted-digraph isomorphism. -/
theorem labelAt_transport_iff (addressing : Addressing left)
    (iso : RootedDigraph.Iso left right) (position : List ℕ)
    (label : Option (NodeLabel Atom)) :
    LabelAt left addressing position label ↔
      LabelAt right (addressing.transport iso) position label := by
  constructor
  · intro h
    rcases h with ⟨node, hpos, hlabel⟩ | ⟨hlabel, hempty⟩
    · left
      refine ⟨iso.toEquiv node, ?_, ?_⟩
      · simpa using hpos
      · simpa [← iso.map_label node] using hlabel
    · right
      refine ⟨hlabel, ?_⟩
      intro node hpos
      exact hempty (iso.toEquiv.symm node) (by simpa using hpos)
  · intro h
    rcases h with ⟨node, hpos, hlabel⟩ | ⟨hlabel, hempty⟩
    · left
      refine ⟨iso.toEquiv.symm node, ?_, ?_⟩
      · simpa using hpos
      · have hmap : left.label (iso.toEquiv.symm node) = right.label node := by
          simpa using iso.map_label (iso.toEquiv.symm node)
        exact hlabel.trans (congrArg some hmap).symm
    · right
      refine ⟨hlabel, ?_⟩
      intro node hpos
      exact hempty (iso.toEquiv node) (by simpa using hpos)

end Addressing
end RootedDigraph

/-! ## Rule-local observations -/

/-- The constitutional rule fragment formalized concretely in this module. -/
inductive ConstitutionalRule where
  | rule1aAtomicNumber
  | rule1bDuplicateNodeProximity
  | rule2AtomicMass
  deriving DecidableEq, Repr

namespace ConstitutionalRule

/-- Embed the constitutional fragment into the complete revised-CIP rule order. -/
def toSequenceRule : ConstitutionalRule → SequenceRule
  | rule1aAtomicNumber => SequenceRule.rule1aAtomicNumber
  | rule1bDuplicateNodeProximity => SequenceRule.rule1bDuplicateNodeProximity
  | rule2AtomicMass => SequenceRule.rule2AtomicMass

end ConstitutionalRule

/-- Atomic number represented by a semantic node label.  Non-atom placeholders carry priority
zero at Rule 1a. -/
def nodeAtomicNumber {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (label : Option (NodeLabel Atom)) : ℕ :=
  match label.bind NodeLabel.atom? with
  | some atom => molecule.atomZ atom
  | none => 0

/-- Isotopic mass represented by a semantic node label.

Revised-CIP duplicate nodes retain the duplicated atom's Rule-1a atomic-number label but carry
mass zero for Rule 2.  Physical isotope or ordinary atomic mass is read only at real atom nodes;
phantom, lone-pair, auxiliary, and absent sparse positions also carry zero. -/
def nodeAtomicMass {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (label : Option (NodeLabel Atom)) : ℕ :=
  match label with
  | some ⟨some atom, .realAtom⟩ => molecule.atomMass atom
  | _ => 0

/-- Total revised Rule-1b root distance at one semantic hierarchy position.

Duplicate and explicit phantom nodes retain their validated payload.  A real node occupies sphere
`position.length + 1`, because the ligand root is sphere one.  Missing sparse positions use that
same positional sphere; this is the implicit-phantom convention used by paired hierarchy
comparison.  In particular, real and missing observations are never treated as an inapplicable
Rule-1b value. -/
def nodeRule1bRootDistance {Atom : Type u} (position : List ℕ) :
    Option (NodeLabel Atom) → ℕ
  | some ⟨_, NodeProvenance.multipleBondDuplicate distance⟩ => distance
  | some ⟨_, NodeProvenance.ringDuplicate distance⟩ => distance
  | some ⟨_, NodeProvenance.phantom distance⟩ => distance
  | _ => position.length + 1

theorem nodeRule1bRootDistance_eq_of_length_eq {Atom : Type u}
    {first second : List ℕ} (h : first.length = second.length)
    (label : Option (NodeLabel Atom)) :
    nodeRule1bRootDistance first label = nodeRule1bRootDistance second label := by
  cases label with
  | none => simp [nodeRule1bRootDistance, h]
  | some label =>
      cases label with
      | mk atom provenance =>
          cases provenance <;> simp [nodeRule1bRootDistance, h]

/-- The total Rule-1b observation of a represented node is independent of sibling-slot names in
the chosen parent-preserving addressing. -/
theorem nodeRule1bRootDistance_addressing_independent {Atom : Type u}
    {graph : RootedDigraph Atom} (first second : graph.Addressing) (node : graph.Node) :
    nodeRule1bRootDistance (first.address node) (some (graph.label node)) =
      nodeRule1bRootDistance (second.address node) (some (graph.label node)) :=
  nodeRule1bRootDistance_eq_of_length_eq (first.address_length_eq second node) _

/-- Relational comparison of priority-valued naturals: larger values have higher priority. -/
inductive DescendingNatOutcome (left right : ℕ) : Ordering → Prop where
  | gt (h : right < left) : DescendingNatOutcome left right Ordering.gt
  | lt (h : left < right) : DescendingNatOutcome left right Ordering.lt
  | eq (h : left = right) : DescendingNatOutcome left right Ordering.eq

namespace DescendingNatOutcome

theorem functional {left right : ℕ} {first second : Ordering}
    (hfirst : DescendingNatOutcome left right first)
    (hsecond : DescendingNatOutcome left right second) :
    first = second := by
  cases hfirst <;> cases hsecond
  all_goals try rfl
  all_goals omega

theorem total (left right : ℕ) : ∃ outcome, DescendingNatOutcome left right outcome := by
  rcases lt_trichotomy left right with h | h | h
  · exact ⟨Ordering.lt, .lt h⟩
  · exact ⟨Ordering.eq, .eq h⟩
  · exact ⟨Ordering.gt, .gt h⟩

end DescendingNatOutcome

/-- Relational Rule-1b comparison of total root distances.  The closer root has higher priority. -/
inductive Rule1bDistanceOutcome : ℕ → ℕ → Ordering → Prop where
  | gt {left right} (h : left < right) :
      Rule1bDistanceOutcome left right Ordering.gt
  | lt {left right} (h : right < left) :
      Rule1bDistanceOutcome left right Ordering.lt
  | eq {left right} (h : left = right) :
      Rule1bDistanceOutcome left right Ordering.eq

namespace Rule1bDistanceOutcome

theorem functional {left right : ℕ} {first second : Ordering}
    (hfirst : Rule1bDistanceOutcome left right first)
    (hsecond : Rule1bDistanceOutcome left right second) :
    first = second := by
  cases hfirst <;> cases hsecond
  all_goals try rfl
  all_goals omega

theorem total (left right : ℕ) :
    ∃ outcome, Rule1bDistanceOutcome left right outcome := by
  rcases lt_trichotomy left right with h | h | h
  · exact ⟨Ordering.gt, .gt h⟩
  · exact ⟨Ordering.eq, .eq h⟩
  · exact ⟨Ordering.lt, .lt h⟩

theorem eq_refl (distance : ℕ) :
    Rule1bDistanceOutcome distance distance Ordering.eq :=
  .eq rfl

theorem eq_trans {first second third : ℕ}
    (hfirst : Rule1bDistanceOutcome first second Ordering.eq)
    (hsecond : Rule1bDistanceOutcome second third Ordering.eq) :
    Rule1bDistanceOutcome first third Ordering.eq := by
  cases hfirst with
  | eq hfirst =>
      cases hsecond with
      | eq hsecond => exact .eq (hfirst.trans hsecond)

theorem gt_trans {first second third : ℕ}
    (hfirst : Rule1bDistanceOutcome first second Ordering.gt)
    (hsecond : Rule1bDistanceOutcome second third Ordering.gt) :
    Rule1bDistanceOutcome first third Ordering.gt := by
  cases hfirst with
  | gt hfirst =>
      cases hsecond with
      | gt hsecond => exact .gt (hfirst.trans hsecond)

theorem gt_eq_trans {first second third : ℕ}
    (hfirst : Rule1bDistanceOutcome first second Ordering.gt)
    (hsecond : Rule1bDistanceOutcome second third Ordering.eq) :
    Rule1bDistanceOutcome first third Ordering.gt := by
  cases hfirst with
  | gt hfirst =>
      cases hsecond with
      | eq hsecond => exact .gt (by simpa [hsecond] using hfirst)

theorem eq_gt_trans {first second third : ℕ}
    (hfirst : Rule1bDistanceOutcome first second Ordering.eq)
    (hsecond : Rule1bDistanceOutcome second third Ordering.gt) :
    Rule1bDistanceOutcome first third Ordering.gt := by
  cases hfirst with
  | eq hfirst =>
      cases hsecond with
      | gt hsecond => exact .gt (by simpa [hfirst] using hsecond)

@[simp] theorem eq_iff {left right : ℕ} :
    Rule1bDistanceOutcome left right Ordering.eq ↔ left = right := by
  constructor
  · intro h
    cases h with
    | eq heq => exact heq
  · exact .eq

@[simp] theorem gt_iff {left right : ℕ} :
    Rule1bDistanceOutcome left right Ordering.gt ↔ left < right := by
  constructor
  · intro h
    cases h with
    | gt hlt => exact hlt
  · exact .gt

@[simp] theorem lt_iff {left right : ℕ} :
    Rule1bDistanceOutcome left right Ordering.lt ↔ right < left := by
  constructor
  · intro h
    cases h with
    | lt hlt => exact hlt
  · exact .lt

theorem outcome_ne_lt_iff_le {left right : ℕ} {outcome : Ordering}
    (h : Rule1bDistanceOutcome left right outcome) :
    outcome ≠ Ordering.lt ↔ left ≤ right := by
  cases h with
  | gt hlt => simp [hlt.le]
  | eq heq => simp [heq]
  | lt hlt => simp [Nat.not_le_of_lt hlt]

end Rule1bDistanceOutcome

/-- Weak Rule-1b priority at one position.  Because every observation has a total distance, this is
ordinary natural-number order and hence a total preorder. -/
def Rule1bWeakPriority {Atom : Type u} (position : List ℕ)
    (left right : Option (NodeLabel Atom)) : Prop :=
  nodeRule1bRootDistance position left ≤ nodeRule1bRootDistance position right

theorem rule1bWeakPriority_iff_outcome_ne_lt {Atom : Type u}
    (position : List ℕ) (left right : Option (NodeLabel Atom)) :
    Rule1bWeakPriority position left right ↔
      ∃ outcome, Rule1bDistanceOutcome
          (nodeRule1bRootDistance position left)
          (nodeRule1bRootDistance position right) outcome ∧
        outcome ≠ Ordering.lt := by
  constructor
  · intro hle
    obtain ⟨outcome, houtcome⟩ := Rule1bDistanceOutcome.total
      (nodeRule1bRootDistance position left) (nodeRule1bRootDistance position right)
    exact ⟨outcome, houtcome, (houtcome.outcome_ne_lt_iff_le).2 hle⟩
  · rintro ⟨outcome, houtcome, hne⟩
    exact (houtcome.outcome_ne_lt_iff_le).1 hne

theorem rule1bWeakPriority_refl {Atom : Type u} (position : List ℕ)
    (label : Option (NodeLabel Atom)) :
    Rule1bWeakPriority position label label :=
  le_rfl

theorem rule1bWeakPriority_trans {Atom : Type u} (position : List ℕ)
    {first second third : Option (NodeLabel Atom)}
    (hfirst : Rule1bWeakPriority position first second)
    (hsecond : Rule1bWeakPriority position second third) :
    Rule1bWeakPriority position first third :=
  hfirst.trans hsecond

theorem rule1bWeakPriority_total {Atom : Type u} (position : List ℕ)
    (left right : Option (NodeLabel Atom)) :
    Rule1bWeakPriority position left right ∨ Rule1bWeakPriority position right left :=
  le_total _ _

/-- Concrete local node judgment for one of Rules 1a, 1b, or 2. -/
def ConstitutionalNodeOutcome {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (position : List ℕ) (left right : Option (NodeLabel Atom)) (outcome : Ordering) : Prop :=
  match rule with
  | ConstitutionalRule.rule1aAtomicNumber =>
      DescendingNatOutcome (nodeAtomicNumber molecule left) (nodeAtomicNumber molecule right) outcome
  | ConstitutionalRule.rule1bDuplicateNodeProximity =>
      Rule1bDistanceOutcome (nodeRule1bRootDistance position left)
        (nodeRule1bRootDistance position right) outcome
  | ConstitutionalRule.rule2AtomicMass =>
      DescendingNatOutcome (nodeAtomicMass molecule left) (nodeAtomicMass molecule right) outcome

theorem constitutionalNodeOutcome_functional
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (position : List ℕ) (left right : Option (NodeLabel Atom)) {first second : Ordering}
    (hfirst : ConstitutionalNodeOutcome molecule rule position left right first)
    (hsecond : ConstitutionalNodeOutcome molecule rule position left right second) :
    first = second := by
  cases rule
  · exact DescendingNatOutcome.functional hfirst hsecond
  · exact Rule1bDistanceOutcome.functional hfirst hsecond
  · exact DescendingNatOutcome.functional hfirst hsecond

theorem constitutionalNodeOutcome_total
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (position : List ℕ) (left right : Option (NodeLabel Atom)) :
    ∃ outcome, ConstitutionalNodeOutcome molecule rule position left right outcome := by
  cases rule
  · exact DescendingNatOutcome.total _ _
  · exact Rule1bDistanceOutcome.total _ _
  · exact DescendingNatOutcome.total _ _

theorem rule1bWeakPriority_iff_constitutionalNodeOutcome_ne_lt
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (position : List ℕ)
    (left right : Option (NodeLabel Atom)) :
    Rule1bWeakPriority position left right ↔
      ∃ outcome, ConstitutionalNodeOutcome molecule
          ConstitutionalRule.rule1bDuplicateNodeProximity position left right outcome ∧
        outcome ≠ Ordering.lt := by
  simpa [ConstitutionalNodeOutcome] using
    (rule1bWeakPriority_iff_outcome_ne_lt position left right)

/-! ## First-difference hierarchy semantics -/

/-- Sphere-major address rank: nearer hierarchy spheres precede every deeper sphere, and canonical
positional paths order nodes within one sphere. -/
def HierarchyAddressKey (address : List ℕ) : List ℕ :=
  address.length :: address

/-- Strict semantic order of hierarchy addresses. -/
def HierarchyAddressBefore (earlier later : List ℕ) : Prop :=
  HierarchyAddressKey earlier < HierarchyAddressKey later

/-- Relational lexicographic outcome for observations indexed by semantic hierarchy addresses. -/
def FirstDifferenceOutcome (observation : List ℕ → Ordering → Prop) : Ordering → Prop
  | Ordering.eq => ∀ position, observation position Ordering.eq
  | Ordering.gt =>
      ∃ position, observation position Ordering.gt ∧
        ∀ earlier, HierarchyAddressBefore earlier position → observation earlier Ordering.eq
  | Ordering.lt =>
      ∃ position, observation position Ordering.lt ∧
        ∀ earlier, HierarchyAddressBefore earlier position → observation earlier Ordering.eq

namespace FirstDifferenceOutcome

theorem congr {left right : List ℕ → Ordering → Prop}
    (h : ∀ position outcome, left position outcome ↔ right position outcome)
    (outcome : Ordering) :
    FirstDifferenceOutcome left outcome ↔ FirstDifferenceOutcome right outcome := by
  cases outcome <;> simp only [FirstDifferenceOutcome]
  · constructor
    · rintro ⟨position, hposition, hearlier⟩
      exact ⟨position, (h _ _).1 hposition, fun earlier hlt => (h _ _).1 (hearlier earlier hlt)⟩
    · rintro ⟨position, hposition, hearlier⟩
      exact ⟨position, (h _ _).2 hposition, fun earlier hlt => (h _ _).2 (hearlier earlier hlt)⟩
  · constructor <;> intro hall position
    · exact (h _ _).1 (hall position)
    · exact (h _ _).2 (hall position)
  · constructor
    · rintro ⟨position, hposition, hearlier⟩
      exact ⟨position, (h _ _).1 hposition, fun earlier hlt => (h _ _).1 (hearlier earlier hlt)⟩
    · rintro ⟨position, hposition, hearlier⟩
      exact ⟨position, (h _ _).2 hposition, fun earlier hlt => (h _ _).2 (hearlier earlier hlt)⟩

/-- A first-difference outcome is single-valued whenever every position has a single-valued local
outcome. -/
theorem functional {observation : List ℕ → Ordering → Prop}
    (localFunctional : ∀ position first second,
      observation position first → observation position second → first = second)
    {first second : Ordering}
    (hfirst : FirstDifferenceOutcome observation first)
    (hsecond : FirstDifferenceOutcome observation second) :
    first = second := by
  cases first with
  | lt =>
      rcases hfirst with ⟨firstPosition, hfirstAt, hfirstEarlier⟩
      cases second with
      | lt => rfl
      | eq =>
          have h := localFunctional firstPosition Ordering.lt Ordering.eq
            hfirstAt (hsecond firstPosition)
          cases h
      | gt =>
          rcases hsecond with ⟨secondPosition, hsecondAt, hsecondEarlier⟩
          rcases lt_trichotomy (HierarchyAddressKey firstPosition)
              (HierarchyAddressKey secondPosition) with hlt | heq | hgt
          · have h := localFunctional firstPosition Ordering.lt Ordering.eq
              hfirstAt (hsecondEarlier firstPosition hlt)
            cases h
          · have hposition : firstPosition = secondPosition := congrArg List.tail heq
            subst secondPosition
            have h := localFunctional firstPosition Ordering.lt Ordering.gt hfirstAt hsecondAt
            cases h
          · have h := localFunctional secondPosition Ordering.gt Ordering.eq
              hsecondAt (hfirstEarlier secondPosition hgt)
            cases h
  | eq =>
      cases second with
      | lt =>
          rcases hsecond with ⟨position, hposition, _⟩
          have h := localFunctional position Ordering.eq Ordering.lt (hfirst position) hposition
          cases h
      | eq => rfl
      | gt =>
          rcases hsecond with ⟨position, hposition, _⟩
          have h := localFunctional position Ordering.eq Ordering.gt (hfirst position) hposition
          cases h
  | gt =>
      rcases hfirst with ⟨firstPosition, hfirstAt, hfirstEarlier⟩
      cases second with
      | lt =>
          rcases hsecond with ⟨secondPosition, hsecondAt, hsecondEarlier⟩
          rcases lt_trichotomy (HierarchyAddressKey firstPosition)
              (HierarchyAddressKey secondPosition) with hlt | heq | hgt
          · have h := localFunctional firstPosition Ordering.gt Ordering.eq
              hfirstAt (hsecondEarlier firstPosition hlt)
            cases h
          · have hposition : firstPosition = secondPosition := congrArg List.tail heq
            subst secondPosition
            have h := localFunctional firstPosition Ordering.gt Ordering.lt hfirstAt hsecondAt
            cases h
          · have h := localFunctional secondPosition Ordering.lt Ordering.eq
              hsecondAt (hfirstEarlier secondPosition hgt)
            cases h
      | eq =>
          have h := localFunctional firstPosition Ordering.gt Ordering.eq
            hfirstAt (hsecond firstPosition)
          cases h
      | gt => rfl

/-- A finite-support family of total local observations has a global first-difference outcome. -/
theorem total_of_finite_support {observation : List ℕ → Ordering → Prop}
    (localTotal : ∀ position, ∃ outcome, observation position outcome)
    (support : Finset (List ℕ))
    (outside : ∀ position, position ∉ support → observation position Ordering.eq) :
    ∃ outcome, FirstDifferenceOutcome observation outcome := by
  classical
  by_cases hall : ∀ position, observation position Ordering.eq
  · exact ⟨Ordering.eq, hall⟩
  · push_neg at hall
    let differing := support.filter fun position => ¬ observation position Ordering.eq
    have hdiffering : differing.Nonempty := by
      rcases hall with ⟨position, hposition⟩
      have hmem : position ∈ support := by
        by_contra hnot
        exact hposition (outside position hnot)
      exact ⟨position, Finset.mem_filter.2 ⟨hmem, hposition⟩⟩
    let differingRanks := differing.image HierarchyAddressKey
    have hdifferingRanks : differingRanks.Nonempty := hdiffering.image _
    let firstRank := differingRanks.min' hdifferingRanks
    have hfirstRankMem : firstRank ∈ differingRanks := differingRanks.min'_mem hdifferingRanks
    rcases Finset.mem_image.1 hfirstRankMem with
      ⟨firstPosition, hfirstMem, hfirstRank⟩
    have hfirstNotEq : ¬ observation firstPosition Ordering.eq :=
      (Finset.mem_filter.1 hfirstMem).2
    rcases localTotal firstPosition with ⟨outcome, houtcome⟩
    have hearlier : ∀ earlier, HierarchyAddressBefore earlier firstPosition →
        observation earlier Ordering.eq := by
      intro earlier hearlier
      by_contra hnotEq
      have hearlierSupport : earlier ∈ support := by
        by_contra hnotMem
        exact hnotEq (outside earlier hnotMem)
      have hearlierDiffering : earlier ∈ differing :=
        Finset.mem_filter.2 ⟨hearlierSupport, hnotEq⟩
      have hearlierRank : HierarchyAddressKey earlier ∈ differingRanks :=
        Finset.mem_image.2 ⟨earlier, hearlierDiffering, rfl⟩
      have hminimal := differingRanks.min'_le (HierarchyAddressKey earlier) hearlierRank
      change firstRank ≤ HierarchyAddressKey earlier at hminimal
      unfold HierarchyAddressBefore at hearlier
      rw [hfirstRank] at hearlier
      exact (not_lt_of_ge hminimal) hearlier
    cases outcome with
    | lt => exact ⟨Ordering.lt, ⟨firstPosition, houtcome, hearlier⟩⟩
    | eq => exact (hfirstNotEq houtcome).elim
    | gt => exact ⟨Ordering.gt, ⟨firstPosition, houtcome, hearlier⟩⟩

end FirstDifferenceOutcome

/-- Rule-local outcome at one shared semantic address. -/
def ConstitutionalOutcomeAt
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ) (outcome : Ordering) : Prop :=
  ∃ leftLabel rightLabel,
    RootedDigraph.Addressing.LabelAt left leftAddressing position leftLabel ∧
      RootedDigraph.Addressing.LabelAt right rightAddressing position rightLabel ∧
        ConstitutionalNodeOutcome molecule rule position leftLabel rightLabel outcome

/-- Concrete parent-preserving hierarchy outcome for Rules 1a, 1b, or 2. -/
def ConstitutionalHierarchyOutcome
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (outcome : Ordering) : Prop :=
  FirstDifferenceOutcome
    (ConstitutionalOutcomeAt molecule rule left leftAddressing right rightAddressing) outcome

namespace RootedDigraph.Addressing

/-- The finite set of semantic addresses occupied by nodes of a rooted digraph. -/
noncomputable def occupiedAddresses {Atom : Type u} (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) : Finset (List ℕ) := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  exact Finset.univ.image addressing.address

@[simp] theorem mem_occupiedAddresses_iff {Atom : Type u} (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (position : List ℕ) :
    position ∈ occupiedAddresses graph addressing ↔
      ∃ node, addressing.address node = position := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  simp [occupiedAddresses, eq_comm]

end RootedDigraph.Addressing

theorem constitutionalOutcomeAt_functional
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ) {first second : Ordering}
    (hfirst : ConstitutionalOutcomeAt molecule rule left leftAddressing
      right rightAddressing position first)
    (hsecond : ConstitutionalOutcomeAt molecule rule left leftAddressing
      right rightAddressing position second) :
    first = second := by
  rcases hfirst with ⟨leftLabel₁, rightLabel₁, hleft₁, hright₁, hout₁⟩
  rcases hsecond with ⟨leftLabel₂, rightLabel₂, hleft₂, hright₂, hout₂⟩
  have hl : leftLabel₁ = leftLabel₂ :=
    RootedDigraph.Addressing.labelAt_functional left leftAddressing position hleft₁ hleft₂
  have hr : rightLabel₁ = rightLabel₂ :=
    RootedDigraph.Addressing.labelAt_functional right rightAddressing position hright₁ hright₂
  subst leftLabel₂
  subst rightLabel₂
  exact constitutionalNodeOutcome_functional molecule rule position
    leftLabel₁ rightLabel₁ hout₁ hout₂

/-- Every address has a constitutional local outcome. -/
theorem constitutionalOutcomeAt_total
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ) :
    ∃ outcome, ConstitutionalOutcomeAt molecule rule left leftAddressing
      right rightAddressing position outcome := by
  rcases RootedDigraph.Addressing.labelAt_exists left leftAddressing position with
    ⟨leftLabel, hleft⟩
  rcases RootedDigraph.Addressing.labelAt_exists right rightAddressing position with
    ⟨rightLabel, hright⟩
  rcases constitutionalNodeOutcome_total molecule rule position leftLabel rightLabel with
    ⟨outcome, houtcome⟩
  exact ⟨outcome, leftLabel, rightLabel, hleft, hright, houtcome⟩

/-- Outside both finite node-address supports, the two hierarchy observations tie. -/
theorem constitutionalOutcomeAt_eq_of_outside
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ)
    (hleft : position ∉ RootedDigraph.Addressing.occupiedAddresses left leftAddressing)
    (hright : position ∉ RootedDigraph.Addressing.occupiedAddresses right rightAddressing) :
    ConstitutionalOutcomeAt molecule rule left leftAddressing
      right rightAddressing position Ordering.eq := by
  have hleftLabel : RootedDigraph.Addressing.LabelAt left leftAddressing position none := by
    right
    refine ⟨rfl, ?_⟩
    intro node hnode
    exact hleft ((RootedDigraph.Addressing.mem_occupiedAddresses_iff
      left leftAddressing position).2 ⟨node, hnode⟩)
  have hrightLabel : RootedDigraph.Addressing.LabelAt right rightAddressing position none := by
    right
    refine ⟨rfl, ?_⟩
    intro node hnode
    exact hright ((RootedDigraph.Addressing.mem_occupiedAddresses_iff
      right rightAddressing position).2 ⟨node, hnode⟩)
  refine ⟨none, none, hleftLabel, hrightLabel, ?_⟩
  cases rule
  · exact DescendingNatOutcome.eq rfl
  · exact Rule1bDistanceOutcome.eq rfl
  · exact DescendingNatOutcome.eq rfl

/-- The concrete constitutional hierarchy judgment cannot return two different outcomes. -/
theorem constitutionalHierarchyOutcome_functional
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    {first second : Ordering}
    (hfirst : ConstitutionalHierarchyOutcome molecule rule left leftAddressing
      right rightAddressing first)
    (hsecond : ConstitutionalHierarchyOutcome molecule rule left leftAddressing
      right rightAddressing second) :
    first = second := by
  exact FirstDifferenceOutcome.functional
    (fun position first second =>
      constitutionalOutcomeAt_functional molecule rule left leftAddressing
        right rightAddressing position) hfirst hsecond

/-- Every pair of finite addressed hierarchies has a Rule-1a, Rule-1b, or Rule-2 outcome. -/
theorem constitutionalHierarchyOutcome_total
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing) :
    ∃ outcome, ConstitutionalHierarchyOutcome molecule rule left leftAddressing
      right rightAddressing outcome := by
  let support :=
    RootedDigraph.Addressing.occupiedAddresses left leftAddressing ∪
      RootedDigraph.Addressing.occupiedAddresses right rightAddressing
  apply FirstDifferenceOutcome.total_of_finite_support
    (fun position => constitutionalOutcomeAt_total molecule rule
      left leftAddressing right rightAddressing position) support
  intro position houtside
  have hboth :
      position ∉ RootedDigraph.Addressing.occupiedAddresses left leftAddressing ∧
        position ∉ RootedDigraph.Addressing.occupiedAddresses right rightAddressing := by
    simpa [support] using houtside
  exact constitutionalOutcomeAt_eq_of_outside molecule rule
    left leftAddressing right rightAddressing position hboth.1 hboth.2

theorem constitutionalOutcomeAt_transport_iff
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (position : List ℕ) (outcome : Ordering) :
    ConstitutionalOutcomeAt molecule rule left leftAddressing right rightAddressing position outcome ↔
      ConstitutionalOutcomeAt molecule rule left' (leftAddressing.transport leftIso)
        right' (rightAddressing.transport rightIso) position outcome := by
  constructor
  · rintro ⟨leftLabel, rightLabel, hleft, hright, houtcome⟩
    exact ⟨leftLabel, rightLabel,
      (RootedDigraph.Addressing.labelAt_transport_iff leftAddressing leftIso position leftLabel).1 hleft,
      (RootedDigraph.Addressing.labelAt_transport_iff rightAddressing rightIso position rightLabel).1 hright,
      houtcome⟩
  · rintro ⟨leftLabel, rightLabel, hleft, hright, houtcome⟩
    exact ⟨leftLabel, rightLabel,
      (RootedDigraph.Addressing.labelAt_transport_iff leftAddressing leftIso position leftLabel).2 hleft,
      (RootedDigraph.Addressing.labelAt_transport_iff rightAddressing rightIso position rightLabel).2 hright,
      houtcome⟩

theorem constitutionalHierarchyOutcome_transport_iff
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (outcome : Ordering) :
    ConstitutionalHierarchyOutcome molecule rule left leftAddressing right rightAddressing outcome ↔
      ConstitutionalHierarchyOutcome molecule rule left' (leftAddressing.transport leftIso)
        right' (rightAddressing.transport rightIso) outcome := by
  exact FirstDifferenceOutcome.congr
    (fun position localOutcome =>
      constitutionalOutcomeAt_transport_iff molecule rule leftAddressing rightAddressing
        leftIso rightIso position localOutcome) outcome

/-! ## Concrete constitutional `Problem` constructor -/

/-- Independent data for a revised-CIP problem whose Rules 1a, 1b, and 2 use the concrete
parent-preserving semantics above.

Later rules remain relational inputs so that this constructor can be extended without importing an
executable comparator.  `addressing_invariant` is a semantic naturality requirement: admissibility
of a hierarchy address cannot depend on the carrier type used to represent its nodes. -/
structure ConstitutionalProblemData (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom] where
  molecule : MoleculeGraph Atom
  centerAtom : Unit → Atom
  ligandAtom : Unit → Fin 4 → Atom
  admissibleExpansion : Unit → Fin 4 → RootedDigraph Atom → Prop
  expansion_sound :
    ∀ unit ligand graph, admissibleExpansion unit ligand graph →
      RootedDigraph.ExactExpansion molecule (centerAtom unit) (ligandAtom unit ligand) graph
  admissibleAddressing :
    DescriptorMap Unit → Unit → (graph : RootedDigraph Atom) → graph.Addressing → Prop
  addressing_invariant :
    ∀ descriptorMap unit {left right : RootedDigraph Atom}
      (iso : RootedDigraph.Iso left right) (addressing : left.Addressing),
      admissibleAddressing descriptorMap unit left addressing ↔
        admissibleAddressing descriptorMap unit right (addressing.transport iso)
  laterRuleJudgment :
    DescriptorMap Unit → SequenceRule → Unit →
      RootedDigraph Atom → RootedDigraph Atom → Ordering → Prop
  admissibleRule6Reference : DescriptorMap Unit → Unit → Atom → Prop
  rule6Judgment :
    DescriptorMap Unit → Unit → Atom →
      RootedDigraph Atom → RootedDigraph Atom → Ordering → Prop
  dependsOn : DescriptorMap Unit → Unit → Unit → Prop
  orientationJudgment : Unit → Equiv.Perm (Fin 4) → Descriptor → Prop

namespace ConstitutionalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- A constitutional hierarchy outcome is admissible only when both graphs possess an admissible
semantic addressing, and the same outcome holds for every such pair of addressings. -/
def CanonicalOutcome (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    (left right : RootedDigraph Atom) (outcome : Ordering) : Prop :=
  (∃ leftAddressing,
      data.admissibleAddressing descriptorMap unit left leftAddressing) ∧
    (∃ rightAddressing,
      data.admissibleAddressing descriptorMap unit right rightAddressing) ∧
    ∀ leftAddressing rightAddressing,
      data.admissibleAddressing descriptorMap unit left leftAddressing →
        data.admissibleAddressing descriptorMap unit right rightAddressing →
          ConstitutionalHierarchyOutcome data.molecule rule
            left leftAddressing right rightAddressing outcome

/-- Addressing/traversal independence for one constitutional comparison. -/
def AddressingIndependent (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    (left right : RootedDigraph Atom) : Prop :=
  ∀ firstLeft firstRight secondLeft secondRight firstOutcome secondOutcome,
    data.admissibleAddressing descriptorMap unit left firstLeft →
      data.admissibleAddressing descriptorMap unit right firstRight →
        data.admissibleAddressing descriptorMap unit left secondLeft →
          data.admissibleAddressing descriptorMap unit right secondRight →
            ConstitutionalHierarchyOutcome data.molecule rule
              left firstLeft right firstRight firstOutcome →
              ConstitutionalHierarchyOutcome data.molecule rule
                left secondLeft right secondRight secondOutcome →
                firstOutcome = secondOutcome

/-- Build the general independent `Problem`, concretely instantiating Rules 1a, 1b, and 2. -/
def toProblem (data : ConstitutionalProblemData Atom Unit) : Problem Atom Unit where
  molecule := data.molecule
  ligandAtom := data.ligandAtom
  admissibleExpansion := data.admissibleExpansion
  ordinaryRuleJudgment := fun descriptorMap rule unit left right outcome =>
    match rule with
    | SequenceRule.rule1aAtomicNumber =>
        data.CanonicalOutcome descriptorMap unit ConstitutionalRule.rule1aAtomicNumber
          left right outcome
    | SequenceRule.rule1bDuplicateNodeProximity =>
        data.CanonicalOutcome descriptorMap unit ConstitutionalRule.rule1bDuplicateNodeProximity
          left right outcome
    | SequenceRule.rule2AtomicMass =>
        data.CanonicalOutcome descriptorMap unit ConstitutionalRule.rule2AtomicMass
          left right outcome
    | _ => data.laterRuleJudgment descriptorMap rule unit left right outcome
  admissibleRule6Reference := data.admissibleRule6Reference
  rule6Judgment := data.rule6Judgment
  dependsOn := data.dependsOn
  orientationJudgment := data.orientationJudgment

/-- Every expansion admitted by the constructed problem satisfies the root/provenance laws and the
exact real, ring-duplicate, multiple-bond, and parent-suppression multiplicities. -/
theorem toProblem_expansion_sound
    (data : ConstitutionalProblemData Atom Unit) (unit : Unit) (ligand : Fin 4)
    (graph : RootedDigraph Atom)
    (h : data.toProblem.admissibleExpansion unit ligand graph) :
    RootedDigraph.ExactExpansion data.molecule (data.centerAtom unit)
      (data.ligandAtom unit ligand) graph :=
  data.expansion_sound unit ligand graph h

@[simp] theorem toProblem_rule1a
    (data : ConstitutionalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : RootedDigraph Atom) (outcome : Ordering) :
    data.toProblem.OutcomeOnGraphs descriptorMap SequenceRule.rule1aAtomicNumber
      unit left right outcome ↔
        data.CanonicalOutcome descriptorMap unit ConstitutionalRule.rule1aAtomicNumber
          left right outcome :=
  Iff.rfl

@[simp] theorem toProblem_rule1b
    (data : ConstitutionalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : RootedDigraph Atom) (outcome : Ordering) :
    data.toProblem.OutcomeOnGraphs descriptorMap SequenceRule.rule1bDuplicateNodeProximity
      unit left right outcome ↔
        data.CanonicalOutcome descriptorMap unit ConstitutionalRule.rule1bDuplicateNodeProximity
          left right outcome :=
  Iff.rfl

@[simp] theorem toProblem_rule2
    (data : ConstitutionalProblemData Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : RootedDigraph Atom) (outcome : Ordering) :
    data.toProblem.OutcomeOnGraphs descriptorMap SequenceRule.rule2AtomicMass
      unit left right outcome ↔
        data.CanonicalOutcome descriptorMap unit ConstitutionalRule.rule2AtomicMass
          left right outcome :=
  Iff.rfl

/-- Transport a canonical constitutional outcome across arbitrary representation isomorphisms. -/
theorem canonicalOutcome_transport
    (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (outcome : Ordering)
    (h : data.CanonicalOutcome descriptorMap unit rule left right outcome) :
    data.CanonicalOutcome descriptorMap unit rule left' right' outcome := by
  rcases h with ⟨⟨leftAddressing, hleftAddressing⟩,
    ⟨rightAddressing, hrightAddressing⟩, hall⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨leftAddressing.transport leftIso,
      (data.addressing_invariant descriptorMap unit leftIso leftAddressing).1 hleftAddressing⟩
  · exact ⟨rightAddressing.transport rightIso,
      (data.addressing_invariant descriptorMap unit rightIso rightAddressing).1 hrightAddressing⟩
  · intro leftAddressing' rightAddressing' hleft' hright'
    let leftBack := leftAddressing'.transport leftIso.symm
    let rightBack := rightAddressing'.transport rightIso.symm
    have hleftBack : data.admissibleAddressing descriptorMap unit left leftBack :=
      (data.addressing_invariant descriptorMap unit leftIso.symm leftAddressing').1 hleft'
    have hrightBack : data.admissibleAddressing descriptorMap unit right rightBack :=
      (data.addressing_invariant descriptorMap unit rightIso.symm rightAddressing').1 hright'
    have houtcome := hall leftBack rightBack hleftBack hrightBack
    have htransported :=
      (constitutionalHierarchyOutcome_transport_iff data.molecule rule leftBack rightBack
        leftIso rightIso outcome).1 houtcome
    simpa [leftBack, rightBack] using htransported

/-- The canonical constitutional judgment is representation-invariant. -/
theorem canonicalOutcome_transport_iff
    (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    {left left' right right' : RootedDigraph Atom}
    (leftIso : RootedDigraph.Iso left left') (rightIso : RootedDigraph.Iso right right')
    (outcome : Ordering) :
    data.CanonicalOutcome descriptorMap unit rule left right outcome ↔
      data.CanonicalOutcome descriptorMap unit rule left' right' outcome := by
  constructor
  · exact data.canonicalOutcome_transport descriptorMap unit rule leftIso rightIso outcome
  · exact data.canonicalOutcome_transport descriptorMap unit rule
      leftIso.symm rightIso.symm outcome

/-- Canonical quantification over addressings preserves the single-valuedness of the hierarchy
judgment. -/
theorem canonicalOutcome_functional
    (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    (left right : RootedDigraph Atom) {first second : Ordering}
    (hfirst : data.CanonicalOutcome descriptorMap unit rule left right first)
    (hsecond : data.CanonicalOutcome descriptorMap unit rule left right second) :
    first = second := by
  rcases hfirst with ⟨⟨leftAddressing, hleft⟩, ⟨rightAddressing, hright⟩, hallFirst⟩
  rcases hsecond with ⟨_, _, hallSecond⟩
  exact constitutionalHierarchyOutcome_functional data.molecule rule
    left leftAddressing right rightAddressing
    (hallFirst leftAddressing rightAddressing hleft hright)
    (hallSecond leftAddressing rightAddressing hleft hright)

/-- Nonempty admissible addressing families and addressing independence produce a canonical
constitutional outcome.  Combined with `canonicalOutcome_functional`, this gives existence and
uniqueness without selecting a traversal algorithm. -/
theorem canonicalOutcome_exists_of_addressingIndependent
    (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (rule : ConstitutionalRule)
    (left right : RootedDigraph Atom)
    (leftExists : ∃ addressing,
      data.admissibleAddressing descriptorMap unit left addressing)
    (rightExists : ∃ addressing,
      data.admissibleAddressing descriptorMap unit right addressing)
    (independent : data.AddressingIndependent descriptorMap unit rule left right) :
    ∃ outcome, data.CanonicalOutcome descriptorMap unit rule left right outcome := by
  rcases leftExists with ⟨firstLeft, hfirstLeft⟩
  rcases rightExists with ⟨firstRight, hfirstRight⟩
  rcases constitutionalHierarchyOutcome_total data.molecule rule
    left firstLeft right firstRight with ⟨outcome, houtcome⟩
  refine ⟨outcome, ⟨firstLeft, hfirstLeft⟩, ⟨firstRight, hfirstRight⟩, ?_⟩
  intro secondLeft secondRight hsecondLeft hsecondRight
  rcases constitutionalHierarchyOutcome_total data.molecule rule
    left secondLeft right secondRight with ⟨secondOutcome, hsecondOutcome⟩
  have heq := independent firstLeft firstRight secondLeft secondRight outcome secondOutcome
    hfirstLeft hfirstRight hsecondLeft hsecondRight houtcome hsecondOutcome
  simpa [heq] using hsecondOutcome

end ConstitutionalProblemData

/-- Representation invariance restricted to the concretely instantiated constitutional rules. -/
def ConstitutionalRepresentationInvariant
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) : Prop :=
  ∀ descriptorMap (rule : ConstitutionalRule) unit left left' right right' outcome,
    RootedDigraph.Iso left left' →
      RootedDigraph.Iso right right' →
        (problem.OutcomeOnGraphs descriptorMap rule.toSequenceRule unit left right outcome ↔
          problem.OutcomeOnGraphs descriptorMap rule.toSequenceRule unit left' right' outcome)

/-- Every problem built by `ConstitutionalProblemData.toProblem` is representation-invariant for
Rules 1a, 1b, and 2. -/
theorem ConstitutionalProblemData.constitutional_representationInvariant
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (data : ConstitutionalProblemData Atom Unit) :
    ConstitutionalRepresentationInvariant data.toProblem := by
  intro descriptorMap rule unit left left' right right' outcome leftIso rightIso
  cases rule
  · exact data.canonicalOutcome_transport_iff descriptorMap unit
      ConstitutionalRule.rule1aAtomicNumber leftIso rightIso outcome
  · exact data.canonicalOutcome_transport_iff descriptorMap unit
      ConstitutionalRule.rule1bDuplicateNodeProximity leftIso rightIso outcome
  · exact data.canonicalOutcome_transport_iff descriptorMap unit
      ConstitutionalRule.rule2AtomicMass leftIso rightIso outcome

/-- The concrete Rules 1a, 1b, and 2 judgments of the constructed problem are functional. -/
theorem ConstitutionalProblemData.constitutional_outcome_functional
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (data : ConstitutionalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) (rule : ConstitutionalRule) (unit : Unit)
    (left right : RootedDigraph Atom) {first second : Ordering}
    (hfirst : data.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
      unit left right first)
    (hsecond : data.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
      unit left right second) :
    first = second := by
  cases rule
  · exact data.canonicalOutcome_functional descriptorMap unit
      ConstitutionalRule.rule1aAtomicNumber left right hfirst hsecond
  · exact data.canonicalOutcome_functional descriptorMap unit
      ConstitutionalRule.rule1bDuplicateNodeProximity left right hfirst hsecond
  · exact data.canonicalOutcome_functional descriptorMap unit
      ConstitutionalRule.rule2AtomicMass left right hfirst hsecond

end
end DeclarativeCIP
end OneCenter
end TetraStereo
